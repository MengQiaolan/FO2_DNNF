import functools
import sympy
from itertools import combinations, product
from logzero import logger

from wfomc.problems import WFOMCProblem
from wfomc.cell_graph.cell_graph import CellGraph, Cell
from wfomc.fol.syntax import AtomicFormula, Const, Pred, QFFormula, X, Y, QuantifiedFormula
from wfomc.fol.sc2 import SC2
from wfomc.fol.utils import new_predicate

from compilation_utils import *

from circuit import NodeType, NC

@functools.lru_cache(maxsize=None)
def group_relations_by_blocks(rels: frozenset[Relation], block_status: tuple[tuple, tuple]) \
                                -> set[Relation]:
    """
    Group relations by their influence on the blocks.
    """
    result: dict[frozenset[Relation], tuple[tuple[bool], tuple[bool]]] = {}
    rels: set = set(rels)
    
    def update_blocks(rel: Relation, blocks: tuple[tuple, tuple]) -> tuple[tuple, tuple]:
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
    
    def get_equivalent_relations(rel: Relation, blocks: tuple[tuple, tuple]) -> set[Relation]:
        res_relset: set[Relation] = {rel}
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
        equivalent_rels, post_blocks = get_equivalent_relations(rel, block_status)
        result[frozenset(remove_aux_atom(equivalent_rels|{rel}))] = post_blocks
        rels = rels - equivalent_rels
    return result

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
        self.rels_of_cells: dict[tuple[Cell, Cell], list[Relation]] = {}
        self.two_tables, self.rels_of_cells = build_two_tables(self.uni_formula, self.cells)
        
        self.relations: list[Relation] = []
        for two_table in self.two_tables:
            relation: set[AtomicFormula] = set()
            for lit in two_table:
                if lit.args[0] != lit.args[1]:
                    relation.add(lit)
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
        for (e_1, e_2) in combinations(self.domain, 2):
            tuples = [(e_1, e_2), (e_2, e_1)]
            for pred in self.cells[0].preds:
                if pred.name.startswith(EXT_PRED_PREFIX):
                    continue
                for a, b in tuples:
                    for sign in ("", "~"):
                        lit_str = f'{sign}{pred.name}({a.name},{b.name})'
                        leaf_node = NC.create_node(NodeType.LEAF, lit_str)
                        self.literal_to_node_index[lit_str] = leaf_node.index
            
        # init the simplified formulas for relations of free pairs
        self.tpl_freepair_formula: dict[tuple[Cell, Cell], QFFormula] = {}
        for cell_pair in product(self.cells, repeat=2):
            rels = frozenset(self.rels_of_cells[cell_pair])
            self.tpl_freepair_formula[cell_pair] = rels_conjunction(rels)
            
    
    # neccessary parameter for CellGraph function     
    def get_weight(self, pred: Pred) -> tuple:
        return (1, 1)
    
    @functools.lru_cache(maxsize=None)
    def get_witness_relation(self, target_cell: Cell, witness_cell: Cell, block_idx: int) \
            -> list[Relation]:
        result = []
        for rel in self.rels_of_cells[(target_cell, witness_cell)]:
            for atom in rel:
                if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                        int(atom.pred.name[len(EXT_PRED_PREFIX):]) == block_idx and atom.args[0] == X:
                    # result.append((rel, atom))
                    result.append(rel)
                    break
        return result
    
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
    
    @functools.lru_cache(maxsize=None)  
    def gound_rels_subcircuit(self, elem_tuple: tuple[Const, Const], rels: frozenset[Relation]):
        rels_formula = rels_conjunction(rels)
        if rels_formula.expr == sympy.true:
            return None
        ground_rels_formula = rels_formula.substitute({X: elem_tuple[0], Y: elem_tuple[1]})
        node_index = self.build_subcircuit_from_expr(ground_rels_formula.expr)
        return node_index
    
    @functools.lru_cache(maxsize=None)
    def build_subcircuit_from_expr(self, expr: sympy.Expr):
        if isinstance(expr, sympy.And):
            new_node = NC.create_node(NodeType.AND)
            for arg in expr.args:
                new_node.children.add(self.build_subcircuit_from_expr(arg))
            return new_node.index
        elif isinstance(expr, sympy.Or):
            new_node = NC.create_node(NodeType.OR)
            for arg in expr.args:
                new_node.children.add(self.build_subcircuit_from_expr(arg))
            return new_node.index
        elif isinstance(expr, sympy.Symbol) or isinstance(expr, sympy.Not):
            return self.literal_to_node_index[expr.__str__()]
        else:
            raise RuntimeError(f'The expression is not valid: {expr}')
    
    