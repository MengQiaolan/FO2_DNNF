from __future__ import annotations
from logzero import logger
from itertools import combinations, product
from copy import deepcopy
import functools
import sympy

from wfomc.fol.syntax import AtomicFormula, Const, Pred, QFFormula, a, b, c, X, Y, QuantifiedFormula, top, bot
from wfomc.problems import WFOMCProblem
from wfomc.fol.sc2 import SC2, to_sc2
from wfomc.fol.utils import new_predicate, exactly_one_qf
from wfomc.cell_graph.cell_graph import CellGraph, Cell, OptimizedCellGraph
from wfomc.cell_graph.utils import conditional_on

from circuit import NodeType, NC

EXT_PRED_PREFIX = '@beta'

def build_two_tables(formula: QFFormula, cells: list[Cell]) -> tuple[list[frozenset[AtomicFormula]], 
                                                                     dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]]]:
    models = dict()
    gnd_formula: QFFormula = ground_on_tuple(formula, a, b) & ground_on_tuple(formula, b, a)
    gnd_formula = gnd_formula.substitute({a: X, b: Y})
    gnd_lits = gnd_formula.atoms()
    gnd_lits = gnd_lits.union(frozenset(map(lambda x: ~x, gnd_lits)))
    for model in gnd_formula.models():
        models[model] = 1

    two_tables: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]] = dict()
    for i, cell in enumerate(cells):
        models_1 = conditional_on(models, gnd_lits, cell.get_evidences(X))
        for j, other_cell in enumerate(cells):
            models_2 = conditional_on(models_1, gnd_lits, other_cell.get_evidences(Y))
            two_tables[(cell, other_cell)] = []
            two_table_list = list(models_2.keys())
            for model in two_table_list:
                two_tables[(cell, other_cell)].append(frozenset({atom for atom in model if len(atom.args) == 2 and atom.args[0] != atom.args[1]}))
      
    return list(models.keys()), two_tables

def ground_on_tuple(formula: QFFormula, c1: Const, c2: Const = None) -> QFFormula:
        variables = formula.vars()
        if len(variables) > 2:
            raise RuntimeError(
                "Can only ground out FO2"
            )
        if len(variables) == 1:
            constants = [c1]
        else:
            if c2 is not None:
                constants = [c1, c2]
            else:
                constants = [c1, c1]
        substitution = dict(zip(variables, constants))
        gnd_formula = formula.substitute(substitution)
        return gnd_formula

def conditional_on_lit(evi: AtomicFormula, dnf:list[frozenset[AtomicFormula]], rm_evi: bool = False) -> list[frozenset[AtomicFormula]]:
    if evi is None:
        return dnf
    conditioned_dnf: list[frozenset[AtomicFormula]] = []
    for clause in dnf:
        if evi not in clause and ~evi not in clause:
            conditioned_dnf.append(clause)
            continue
        for lit in clause:
            if lit.pred.name == evi.pred.name and lit.args == evi.args:
                if lit.positive == evi.positive:
                    if rm_evi:
                        clause = frozenset(filter(lambda atom: atom != evi, clause))
                    conditioned_dnf.append(clause)
                break
    return conditioned_dnf

def conditional_on_lits(evidences: list[AtomicFormula], dnf:list[frozenset[AtomicFormula]], rm_evi: bool = False) -> list[frozenset[AtomicFormula]]:
    if evidences is None:
        return dnf
    for evi in evidences:
        conditioned_dnf = conditional_on_lit(evi, dnf, rm_evi)
    return conditioned_dnf

@functools.lru_cache(maxsize=None)
def group_relations_by_blocks(rels: frozenset[frozenset[AtomicFormula]], block_status: tuple[tuple, tuple]) \
                                -> set[frozenset[AtomicFormula]]:
    result: dict[frozenset[frozenset[AtomicFormula]], tuple[tuple[bool], tuple[bool]]] = {}
    rels: set = set(rels)
    
    def update_blocks(rel: frozenset[AtomicFormula], blocks: tuple[tuple, tuple]) -> tuple[tuple, tuple]:
        post_blocks: list[list[bool]] = [list(blocks[0]), list(blocks[1])]
        for lit in rel:
            if lit.pred.name.startswith(EXT_PRED_PREFIX) and lit.positive:
                block_idx = int(lit.pred.name[len(EXT_PRED_PREFIX):])
                if lit.args[0] == X:
                    post_blocks[0][block_idx] = False
                elif lit.args[0] == Y:
                    post_blocks[1][block_idx] = False
                else:
                    raise RuntimeError(f'The arguments of the atom is not correct: {lit}')
        return tuple(map(tuple, post_blocks))
    
    def find_equivalent_twotype(rel: frozenset[AtomicFormula], blocks: tuple[tuple, tuple]) -> set[frozenset[AtomicFormula]]:
        res_relset: set[frozenset[AtomicFormula]] = {rel}
        post_blocks = update_blocks(rel, blocks)
        for other_rel in rels:
            if other_rel == rel:
                continue
            other_post_blocks = update_blocks(other_rel, blocks)
            if post_blocks == other_post_blocks:
                res_relset.add(other_rel)
        return res_relset, tuple(map(tuple, post_blocks))
    
    while len(rels) > 0:
        rel = rels.pop()
        equivalent_rels, post_blocks = find_equivalent_twotype(rel, block_status)
        result[frozenset(remove_aux_atom(equivalent_rels|{rel}))] = post_blocks
        rels = rels - equivalent_rels
    return result

def remove_aux_atom(input):
    assert isinstance(input, (frozenset, list, set))
    if isinstance(next(iter(input)), AtomicFormula):
        return type(input)(filter(lambda atom: not atom.pred.name.startswith(EXT_PRED_PREFIX), set(input)))
    elif isinstance(next(iter(input)), (frozenset, list, set)):
        return type(input)(map(lambda clause: remove_aux_atom(clause), input))
    else:
        raise RuntimeError(f'The type of input is not correct: {type(input)}')

def substitute(input, subst):
    if isinstance(input, AtomicFormula):
        return input.substitute(subst)
    assert isinstance(input, (frozenset, list, set))
    if isinstance(next(iter(input)), AtomicFormula):
        return type(input)(map(lambda atom: atom.substitute(subst), input))
    elif isinstance(next(iter(input)), (frozenset, list, set)):
        return type(input)(map(lambda clause: substitute(clause, subst), input))
    else:
        raise RuntimeError(f'The type of input is not correct: {type(input)}')

@functools.lru_cache(maxsize=None)
def rels_conjunction(input_rels: frozenset[frozenset[AtomicFormula]]) -> QFFormula:
    fml: QFFormula = bot
    for rel in input_rels:
        rel_fml = top
        for lit in remove_aux_atom(rel):
            rel_fml = rel_fml & lit
        fml = fml | rel_fml
    fml = fml.simplify()
    return fml

class Context(object):
    
    def __init__(self, problem: WFOMCProblem):
        self.sentence: SC2 = problem.sentence
        self.weights: dict[Pred, tuple] = problem.weights
        self.domain_size = len(problem.domain)
        self.domain: list[Const] = [Const(f'{i}') for i in range(self.domain_size)]
        
        # scott normal form
        self.uni_formula: QFFormula = self.sentence.uni_formula
        self.ext_formulas: list[QuantifiedFormula] = []
        self._scott()
        
        # number of ext predicates
        self._m = len(self.ext_formulas)
        
        # build cell graph
        self.cell_graph: CellGraph = CellGraph(self.uni_formula, self.get_weight)
        self.cells: list[Cell] = self.cell_graph.cells
        
        # 2-tables contaion the cells, but the relations are not included
        self.rels_of_cells: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]] = {}
        self.two_tables, self.rels_of_cells = build_two_tables(self.uni_formula, self.cells)
        
        self.atom_to_sym: dict[AtomicFormula, sympy.Symbol] = {}
        self.sym_to_atom: dict[sympy.Symbol, AtomicFormula] = {}
        self.relations: list[frozenset[AtomicFormula]] = []
        for two_table in self.two_tables:
            relation: set[AtomicFormula] = set()
            for lit in two_table:
                if lit.args[0] != lit.args[1]:
                    relation.add(lit)
                    atom = lit if lit.positive else ~lit
                    if atom not in self.atom_to_sym and not atom.pred.name.startswith(EXT_PRED_PREFIX):
                        symbol = sympy.Symbol(atom.__str__())
                        self.atom_to_sym[atom] = symbol
                        self.sym_to_atom[symbol] = atom
            self.relations.append(frozenset(relation))
        
        # init the blocks of each cell
        self.blcok_of_cell: dict[Cell, list[bool]] = {}
        for cell in self.cells:
            self.blcok_of_cell[cell] = [True for _ in range(self._m)]
            for pred in cell.preds:
                if pred.name.startswith(EXT_PRED_PREFIX) and cell.is_positive(pred):
                    block_idx = int(pred.name[len(EXT_PRED_PREFIX):])
                    self.blcok_of_cell[cell][block_idx] = False
        
        # init the leaf nodes
        self.literal_to_node_index: dict[str, int] = {}
        self.node_index_to_literal: dict[int, str] = {}
        self.gnd_rel_to_node_index: dict[str, int] = {}
        self.freepair_to_node_index: dict[frozenset[Const], int] = {}
        
        for (cell_1, cell_2) in combinations(self.domain, 2):
            element_pair = f'({cell_1.name},{cell_2.name})'
            r_element_pair = f'({cell_2.name},{cell_1.name})'
            
            for pred in self.cells[0].preds:
                if pred.name.startswith(EXT_PRED_PREFIX) or pred.arity != 2:
                    continue
                leaf_node = NC.create_node(NodeType.LEAF, f'{pred.name}{element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = NC.create_node(NodeType.LEAF, f'{pred.name}{r_element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = NC.create_node(NodeType.LEAF, f'~{pred.name}{element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
                
                leaf_node = NC.create_node(NodeType.LEAF, f'~{pred.name}{r_element_pair}')
                self.literal_to_node_index[leaf_node.literal_str] = leaf_node.index
                self.node_index_to_literal[leaf_node.index] = leaf_node.literal_str
            
            or_node = NC.create_node(NodeType.OR)
            self.freepair_to_node_index[frozenset([cell_1, cell_2])] = or_node.index
            for rel in self.relations:
                and_node = NC.create_node(NodeType.AND)
                or_node.children.add(and_node.index)
                for lit in rel:
                    if lit.pred.name.startswith(EXT_PRED_PREFIX) or lit.args[0] == lit.args[1]:
                        continue
                    positive = '' if lit.positive else '~'
                    if lit.args[0] == X and lit.args[1] == Y:
                        and_node.children.add(self.literal_to_node_index[f'{positive}{lit.pred.name}{element_pair}'])
                    elif lit.args[0] == Y and lit.args[1] == X:
                        and_node.children.add(self.literal_to_node_index[f'{positive}{lit.pred.name}{r_element_pair}'])
                    else:
                        raise RuntimeError(f'The the arguments is not correct: {lit.args[0]}, {lit.args[1]}')
                self.gnd_rel_to_node_index[f'R{self.relations.index(rel)}({cell_1},{cell_2})'] = and_node.index
                self.gnd_rel_to_node_index[f'R{self.relations.index(rel)}({cell_2},{cell_1})'] = and_node.index
        
        # construct 2-table subcircuits
        # 每对cell的每个2-table都对应一个子电路
        self.subcircuit_of_rels: dict[tuple[Cell, Cell],
                                       dict[tuple[tuple, tuple], # blocks of the 2-table
                                            dict[tuple[Const, Const], int]]] = {}
        self.expression_of_rels: dict[tuple[Cell, Cell],
                                       dict[tuple[tuple, tuple], # blocks of the 2-table
                                            dict[tuple[Const, Const], sympy.Expr]]] = {}
        self.init_subcircuits_of_rels()
        
        # 对于没有block的pair，可以直接添加全部2-table的子电路, 换句话说，可以不用关心 false blocks
        # 因此构建subcircuit的时候，只需要对 true blocks 的影响
        # 换句话说，在进行分支的时候，如果两个2-table对pair的true blocks (之前是所有blocks) 影响是相同的，那么可以合并成一个分支
        
        # 先求对于当前pair及其blocks，哪些2-type是等价的，然后查表，或者重新构建。
        # set of twotype -> element pair -> node index
        self.subcircuit_cache: dict[frozenset[frozenset[AtomicFormula]], 
                                    dict[tuple[Const, Const], int]] = {}
        
        
        # 
        self.template_freepair_expr: dict[tuple[Cell], QFFormula] = {}
        for cell_pair in product(self.cells, repeat=2):
            cell_1, cell_2 = cell_pair
            fml = bot
            for rel in self.rels_of_cells[(cell_1, cell_2)]:
                rel_fml = top
                for lit in remove_aux_atom(rel):
                    rel_fml = rel_fml & lit
                fml = fml | rel_fml
            fml = fml.simplify()
            self.template_freepair_expr[cell_pair] = fml
            
    
    # neccessary paraneter for CellGraph function     
    def get_weight(self, pred: Pred) -> tuple:
        default = 1
        if pred in self.weights:
            return self.weights[pred]
        return (default, default)
    
    @functools.lru_cache(maxsize=None)
    def get_witness_relation(self, target_cell: Cell, witness_cell: Cell, block_idx: int) \
            -> list[frozenset[AtomicFormula]]:
        result = []
        for rel in self.rels_of_cells[(target_cell, witness_cell)]:
            for atom in rel:
                if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                        int(atom.pred.name[len(EXT_PRED_PREFIX):]) == block_idx and atom.args[0] == X:
                    # result.append((rel, atom))
                    result.append(rel)
                    break
        return result
    
    def get_witness_lit(self, ego_element_cell: Const, witness_cell: Const, block_idx: int) \
        -> AtomicFormula:
        for rel in self.rels_of_cells[(ego_element_cell, witness_cell)]:
            for atom in rel:
                if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                        int(atom.pred.name[len(EXT_PRED_PREFIX):]) == block_idx and atom.args[0] == X:
                    return atom
        return None
    
    def _scott(self):
        while(not isinstance(self.uni_formula, QFFormula)):
            self.uni_formula = self.uni_formula.quantified_formula
        
        # FIXME: this is a hack to map the auxiliary predicates to the original formulas
        self.auxlit_to_orilit: dict[AtomicFormula, AtomicFormula] = {}
        self.orilit_to_auxlit: dict[AtomicFormula, AtomicFormula] = {}

        for formula in self.sentence.ext_formulas:
            quantified_formula = formula.quantified_formula.quantified_formula
            new_pred = new_predicate(2, EXT_PRED_PREFIX)
            new_atom = new_pred(X,Y)
            
            # FIXME: this is a hack to map the auxiliary predicates to the original formulas
            if isinstance(quantified_formula, AtomicFormula):
                self.auxlit_to_orilit[new_atom] = quantified_formula
                self.orilit_to_auxlit[quantified_formula] = new_atom
            
            formula.quantified_formula.quantified_formula = new_atom
            self.ext_formulas.append(formula)
            self.uni_formula = self.uni_formula.__and__(new_atom.equivalent(quantified_formula))

        logger.info('The universal formula: \n%s', self.uni_formula)
        logger.info('The existential formulas: \n%s', self.ext_formulas)
        
    def simplify_dnf(self, dnf: set[frozenset[AtomicFormula]]):
        sympy_expr: sympy.Expr = sympy.Or()
        for clause in dnf:
            sympy_clause_expr = sympy.And()
            for lit in clause:
                if lit.positive:
                    sympy_clause_expr = sympy.And(sympy_clause_expr, self.atom_to_sym[lit])
                else:
                    sympy_clause_expr = sympy.And(sympy_clause_expr, ~self.atom_to_sym[~lit])
            sympy_expr = sympy.Or(sympy_expr, sympy_clause_expr)
        sympy_expr = sympy.simplify_logic(sympy_expr)
        # TODO: convert the sympy expression to the formula
        # formula: QFFormula = top        
        return sympy_expr
    
    def get_subcircuit_of_twotypes(self, twotypes: frozenset[frozenset[AtomicFormula]], element_pair: tuple[Const, Const]):
        if twotypes in self.subcircuit_cache:
            if element_pair in self.subcircuit_cache[twotypes]:
                return self.subcircuit_cache[twotypes][element_pair]
        else:
            self.subcircuit_cache[twotypes] = {}
        expr = self.simplify_dnf(remove_aux_atom(twotypes))
        if expr == sympy.true:
            self.subcircuit_cache[twotypes][element_pair] = None
            return None
        
        def build_subcircuit_from_expr(expr: sympy.Expr):
            if isinstance(expr, sympy.And):
                new_node = NC.create_node(NodeType.AND)
                for arg in expr.args:
                    new_node.children.add(build_subcircuit_from_expr(arg))
                return new_node.index
            elif isinstance(expr, sympy.Or):
                new_node = NC.create_node(NodeType.OR)
                for arg in expr.args:
                    new_node.children.add(build_subcircuit_from_expr(arg))
                return new_node.index
            elif isinstance(expr, sympy.Symbol):
                atom = self.sym_to_atom[expr].substitute({X: element_pair[0], Y: element_pair[1]})
                return self.literal_to_node_index[atom.__str__()]
            elif isinstance(expr, sympy.Not):
                atom = self.sym_to_atom[~expr].substitute({X: element_pair[0], Y: element_pair[1]})
                return self.literal_to_node_index[(~atom).__str__()]
            else:
                raise RuntimeError(f'The expression is not a conjunction, disjunction or literal: {expr}')
        
        
        node_index = build_subcircuit_from_expr(expr)
        self.subcircuit_cache[twotypes][element_pair] = node_index
        return node_index
    
    def init_subcircuits_of_rels(self):
        for cell_pair, rels in self.rels_of_cells.items():
            self.subcircuit_of_rels[cell_pair] = {}
            self.expression_of_rels[cell_pair] = {}
            # classify the relations according to the blocks
            block_to_rel: dict[tuple[tuple, tuple], set[frozenset[AtomicFormula]]] = {}
            for rel in rels: # rel don't include the cell literals
                break_blocks_1, break_blocks_2 = [False for _ in range(self._m)], [False for _ in range(self._m)]
                for lit in rel:
                    if lit.pred.name.startswith(EXT_PRED_PREFIX) and lit.positive:
                        block_idx = int(lit.pred.name[len(EXT_PRED_PREFIX):])
                        if lit.args[0] == X:
                            break_blocks_1[block_idx] = True
                        elif lit.args[0] == Y:
                            break_blocks_2[block_idx] = True
                        else:
                            raise RuntimeError(f'The arguments of the atom is not correct: {lit}')
                break_block: tuple[tuple, tuple] = (tuple(break_blocks_1), tuple(break_blocks_2))
                if break_block not in block_to_rel:
                    block_to_rel[break_block] = set()
                block_to_rel[break_block].add(rel)
            
            # construct the subcircuit for rels corresponding to the break_block
            for break_block, rels in block_to_rel.items():
                self.subcircuit_of_rels[cell_pair][break_block] = {}
                self.expression_of_rels[cell_pair][break_block] = {}
                if len(rels) == 0:
                    raise RuntimeError('The length of rels is 0')
                expr = self.simplify_dnf(remove_aux_atom(rels))
                
                conjunction_formula = rels_conjunction(frozenset(rels))
                
                if conjunction_formula.expr == sympy.true:
                    for element_pair in product(self.domain, repeat=2):
                        self.subcircuit_of_rels[cell_pair][break_block][element_pair] = None
                        self.expression_of_rels[cell_pair][break_block][element_pair] = sympy.true
                    continue
                
                for element_pair in product(self.domain, repeat=2):
                    e_1, e_2 = element_pair
                    if e_1 == e_2:
                        continue
                    ground_fomula = conjunction_formula.substitute({X: e_1, Y: e_2})
                    
                    def build_subcircuit_from_expr(expr: sympy.Expr):
                        if isinstance(expr, sympy.And):
                            new_node = NC.create_node(NodeType.AND)
                            for arg in expr.args:
                                new_node.children.add(build_subcircuit_from_expr(arg))
                            return new_node.index
                        elif isinstance(expr, sympy.Or):
                            new_node = NC.create_node(NodeType.OR)
                            for arg in expr.args:
                                new_node.children.add(build_subcircuit_from_expr(arg))
                            return new_node.index
                        elif isinstance(expr, sympy.Symbol) or isinstance(expr, sympy.Not):
                            return self.literal_to_node_index[expr.__str__()]
                        elif expr == sympy.true:
                            return None
                        else:
                            raise RuntimeError(f'The expression is not valid: {expr}, type: {type(expr)}')
                    
                    self.subcircuit_of_rels[cell_pair][break_block][element_pair] = build_subcircuit_from_expr(ground_fomula.expr)
                    self.expression_of_rels[cell_pair][break_block][element_pair] = expr
    
    def get_wit_subcircuit(self, cell_pair: tuple[Cell, Cell], element_pair: tuple[Const, Const], block_index: int):
        for break_block in self.subcircuit_of_rels[cell_pair].keys():
            if break_block[0][block_index]:
                yield self.subcircuit_of_rels[cell_pair][break_block][element_pair], \
                        self.expression_of_rels[cell_pair][break_block][element_pair], \
                            break_block
    
    def get_all_subcircuit(self, cell_pair: tuple[Cell, Cell], element_pair: tuple[Const, Const]):
        for break_block in self.subcircuit_of_rels[cell_pair].keys():
            yield self.subcircuit_of_rels[cell_pair][break_block][element_pair], \
                    self.expression_of_rels[cell_pair][break_block][element_pair], \
                        break_block
    
    @functools.lru_cache(maxsize=None)
    def ground_freepair_subcircuit(self, element_pair: tuple[Const, Const], cell_pair: tuple[Cell, Cell]):
        template_freepair_expr = self.template_freepair_expr[cell_pair]
        if template_freepair_expr.expr == sympy.true:
            return None
        ground_expr = template_freepair_expr.substitute({X: element_pair[0], Y: element_pair[1]})
        
        print(ground_expr)
                
        def build_subcircuit_from_expr(expr: sympy.Expr):
            if isinstance(expr, sympy.And):
                new_node = NC.create_node(NodeType.AND)
                for arg in expr.args:
                    new_node.children.add(build_subcircuit_from_expr(arg))
                return new_node.index
            elif isinstance(expr, sympy.Or):
                new_node = NC.create_node(NodeType.OR)
                for arg in expr.args:
                    new_node.children.add(build_subcircuit_from_expr(arg))
                return new_node.index
            elif isinstance(expr, sympy.Symbol) or isinstance(expr, sympy.Not):
                return self.literal_to_node_index[expr.__str__()]
            elif isinstance(expr, sympy.true):
                return None
            else:
                raise RuntimeError(f'The expression is not valid: {expr}')
        
        node_index = build_subcircuit_from_expr(ground_expr.expr)
        return node_index