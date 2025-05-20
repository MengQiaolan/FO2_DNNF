
import copy
import functools
from wfomc.fol.syntax import Const, X
from wfomc.cell_graph.cell_graph import Cell, AtomicFormula
from wfomc.fol.syntax import AtomicFormula, Const, QFFormula, a, b, X, Y, top, bot
from wfomc.cell_graph.utils import conditional_on


EXT_PRED_PREFIX = '@beta'
Relation = frozenset[AtomicFormula]

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
def rels_conjunction(input_rels: frozenset[Relation]) -> QFFormula:
    formula: QFFormula = bot
    for rel in input_rels:
        clause = top
        for lit in rel:
            if lit.pred.name.startswith(EXT_PRED_PREFIX):
                continue
            clause = clause & lit
        formula = formula | clause
    formula = formula.simplify()
    return formula

def init_candidate_witness(domain_to_cell: dict[Const, Cell], 
                          get_witness_relation: callable,
                          block_status: dict[Const, list[bool]],
                          domain: set[Const]):
    candidate_witness: dict[Const, list[set[Const]]] = {(element): [] for element in domain}
    for element in domain:
        for idx_ext, block in enumerate(block_status[element]):
            if not block:
                candidate_witness[element].append(None) # FIXME: should be None ?
                continue
            witness_list: set[Const] = set()
            for wit in domain:
                if element == wit:
                    continue
                if get_witness_relation(domain_to_cell[element], domain_to_cell[wit], idx_ext):
                    witness_list.add(wit)
            assert len(witness_list) != 0
            candidate_witness[element].append(witness_list)
    return candidate_witness

def check_sat(domain_to_cell: dict[Const, Cell], get_witness_relation: callable, block_status: dict[Const, list[bool]], 
                candidate_witness: dict[Const, list[set[Const]]]) -> bool:
    current_blocks: dict[Const, list[bool]] = copy.deepcopy(block_status)
    relation_assignments: dict[frozenset[Const], Relation] = {}
    
    def find_next_block() -> tuple[Const, int]:
        for elem, status in current_blocks.items():
            for idx, val in enumerate(status):
                if val:
                    return elem, idx
        return None, None
    
    def get_relations(elem: Const, witness: Const, block_idx: int) -> list[Relation]:
        return get_witness_relation(domain_to_cell[elem], domain_to_cell[witness], block_idx)
    
    def blocks_to_unblock(elem: Const, witness: Const, rel: Relation) -> list[tuple[Const, int]]:
        breakblock: list[tuple[Const, int]] = []
        for atom in rel:
            if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive:
                breakblock.append((elem if atom.args[0] == X else witness, int(atom.pred.name[len(EXT_PRED_PREFIX):])))
        return breakblock
    
    def backtrack() -> bool:
        elem, b_idx = find_next_block()
        if elem is None:
            return True

        for witness in candidate_witness[elem][b_idx]:
            pair_key = frozenset({elem, witness})
            if pair_key in relation_assignments:
                continue
            
            possible_rels = get_relations(elem, witness, b_idx)
            for rel in possible_rels:
                relation_assignments[pair_key] = rel
                to_clear = blocks_to_unblock(elem, witness, rel)

                changed_blocks: list[tuple[Const, int]] = []
                for (e_to_clear, idx_to_clear) in to_clear:
                    if current_blocks[e_to_clear][idx_to_clear]:
                        current_blocks[e_to_clear][idx_to_clear] = False
                        changed_blocks.append((e_to_clear, idx_to_clear))
                assert current_blocks[elem][b_idx] == False

                if backtrack():
                    return True

                for (e_prev, idx_prev) in changed_blocks:
                    current_blocks[e_prev][idx_prev] = True
                del relation_assignments[pair_key]

        return False
    
    return backtrack()

def build_two_tables(formula: QFFormula, cells: list[Cell]) \
                    -> tuple[list[frozenset[AtomicFormula]], dict[tuple[Cell, Cell], list[Relation]]]:
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

# def conditional_on_lit(evi: AtomicFormula, dnf:list[frozenset[AtomicFormula]], rm_evi: bool = False) -> list[frozenset[AtomicFormula]]:
#     if evi is None:
#         return dnf
#     conditioned_dnf: list[frozenset[AtomicFormula]] = []
#     for clause in dnf:
#         if evi not in clause and ~evi not in clause:
#             conditioned_dnf.append(clause)
#             continue
#         for lit in clause:
#             if lit.pred.name == evi.pred.name and lit.args == evi.args:
#                 if lit.positive == evi.positive:
#                     if rm_evi:
#                         clause = frozenset(filter(lambda atom: atom != evi, clause))
#                     conditioned_dnf.append(clause)
#                 break
#     return conditioned_dnf

# def conditional_on_lits(evidences: list[AtomicFormula], dnf:list[frozenset[AtomicFormula]], rm_evi: bool = False) -> list[frozenset[AtomicFormula]]:
#     if evidences is None:
#         return dnf
#     for evi in evidences:
#         conditioned_dnf = conditional_on_lit(evi, dnf, rm_evi)
#     return conditioned_dnf