import copy
import argparse
import logzero
from logzero import logger

from copy import deepcopy

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const
from wfomc.cell_graph.cell_graph import Cell

from circuit import NodeType, Node, NC
from context import group_relations_by_blocks, Context
from compilation_utils import *

# we use the relation info instead of cell info since some cells may have the same relations
PairWithRel = tuple[tuple[Const, Const], frozenset[Relation]]
PairSet = frozenset[PairWithRel]

class RecursionState:
    def __init__(self, block_status: dict[Const, list[bool]],
                 candidate_witness: dict[Const, list[set[Const]]], 
                 unprocessed_pairs: list[PairSet], 
                 depth: int = 0):
        self.depth = depth
        self.block_status = block_status
        self.unprocessed_pairs = unprocessed_pairs
        self.candidate_witness = candidate_witness

    def copy(self):
        return RecursionState(copy.deepcopy(self.block_status), 
                              copy.deepcopy(self.candidate_witness), 
                              copy.deepcopy(self.unprocessed_pairs), 
                              self.depth)

def is_isomorphic(state: RecursionState, state_cache: dict[RecursionState, int]):
    for key, value in state_cache.items():
        # state.candidate_witness == key.candidate_witness and \
        if state.block_status == key.block_status and \
            state.unprocessed_pairs == key.unprocessed_pairs:
            return value
    return None

def build_subcircuit_for_freepairs(ctx: Context, 
                                   FreePairsRecord: dict[PairSet, list[Node]]):    
    freepair_dict: dict[int, list[PairSet]] = {}
    for freepair_set in FreePairsRecord.keys():
        freepair_dict.setdefault(len(freepair_set), []).append(freepair_set)
        
    nodeidx_of_freepairs: dict[PairSet, int] = {}
    
    # process the freepair sets in order of their length
    vlist = sorted(freepair_dict.keys())
    processed_sets = set()
    for l in vlist:
        for freepair_set in freepair_dict[l]:
            if len(freepair_set) == 1:
                # if the freepairs is only one, we can directly use the subcircuit
                elem_tuple, rels = tuple(next(iter(freepair_set)))
                subcircuit_index = ctx.gound_rels_subcircuit(elem_tuple, rels)
                nodeidx_of_freepairs[freepair_set] = subcircuit_index
                if subcircuit_index is not None:
                    for node in FreePairsRecord[freepair_set]:
                        node.children.add(subcircuit_index)
            else:
                # if the freepairs is more than one, we need to build the AND node
                and_node = NC.create_node(NodeType.AND)
                for node in FreePairsRecord[freepair_set]:
                    node.children.add(and_node.index)
                nodeidx_of_freepairs[freepair_set] = and_node.index
                # add children to the AND node
                subsets, remaing_pairs = greedy_prize_cover(freepair_set, processed_sets)
                for subset in subsets:
                    assert subset in nodeidx_of_freepairs, f'Subset {subset} not in nodeidx_of_freepairs'
                    if nodeidx_of_freepairs[subset] is not None:
                        and_node.children.add(nodeidx_of_freepairs[subset])
                # TODO: postpone the remaining pairs
                for pair in remaing_pairs:
                    if pair in nodeidx_of_freepairs:
                        and_node.children.add(nodeidx_of_freepairs[pair])
                        continue
                    elem_tuple, rels = pair
                    subcircuit_index = ctx.gound_rels_subcircuit(elem_tuple, rels)
                    nodeidx_of_freepairs[pair] = subcircuit_index
                    if subcircuit_index is not None:
                        and_node.children.add(subcircuit_index)
                        
        processed_sets.update(freepair_dict[l])

def parse_args():
    parser = argparse.ArgumentParser(
        description='DNNF Compiler for FO2',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--input', '-i', type=str, required=True, help='sentence file')
    parser.add_argument('--domain-size', '-n', type=int, required=True, help='domain size')
    parser.add_argument('--debug', action='store_true', default=False)
    args = parser.parse_args()
    return args

def get_problem(args) -> WFOMCProblem:
    problem = parse_input(args.input)
    new_domain: list[Const] = [Const(f'{i}') for i in range(args.domain_size)]    
    problem.domain = new_domain
    return problem

def pair_recursion(ctx: Context, 
                   target_element: Const, domain_todo: list[Const], domain_done: list[Const], 
                   DomainToCell: dict[Const, Cell], subroot_node: Node, 
                   FreePairsRecord: dict[PairSet, list[Node]], StateCache: dict[RecursionState, int], 
                   rec_state: RecursionState):
    # if all elements are not blocked, we can skip it
    if all(not any(rec_state.block_status[element]) for element in [target_element] + domain_todo + domain_done):
        logger.info(f'{"    " * rec_state.depth} All elements are not blocked, end')    
        if rec_state.unprocessed_pairs:
            FreePairsRecord.setdefault(frozenset(rec_state.unprocessed_pairs), []).append(subroot_node)
        return
    
    if len(domain_todo) == 0:
        logger.info(f'{"    " * rec_state.depth} No more elements in domain, return')
        domain_recursion_rel(ctx, domain_done, DomainToCell,
                         subroot_node, FreePairsRecord, StateCache, rec_state)
        return
    
    rec_state.depth += 1
    
    cur_element = domain_todo[0]
    domain_todo = domain_todo[1:]
    domain_done = domain_done + [cur_element]
    
    def add_subcircuit(rec_state_: RecursionState, subcircuit_index_: int):
        # create the AND node
        subroot_node.mark = f'({target_element},{cur_element})'
        and_node = NC.create_node(NodeType.AND, mark=f'({target_element},{cur_element})')
        subroot_node.children.add(and_node.index)
        # add the subcircuit
        if subcircuit_index_ is not None:
            and_node.children.add(subcircuit_index_)
        # add the OR node for remaining (cache first)
        isomorphic_node_index = is_isomorphic(rec_state_, StateCache) 
        if isomorphic_node_index is not None:
            logger.info(f'{"    " * rec_state_.depth} Isomorphic:')
            and_node.children.add(isomorphic_node_index)
        else:
            new_subroot_node = NC.create_node(NodeType.OR)
            and_node.children.add(new_subroot_node.index)
            StateCache[rec_state_] = new_subroot_node.index
            pair_recursion(ctx, target_element, domain_todo.copy(), domain_done.copy(), DomainToCell,
                            new_subroot_node, FreePairsRecord, StateCache, rec_state_)
    
    cell_pair = (DomainToCell[target_element], DomainToCell[cur_element])
    grouped_relations: dict = group_relations_by_blocks(frozenset(ctx.rels_of_cells[cell_pair]), 
                                                (tuple(rec_state.block_status[target_element]), tuple(rec_state.block_status[cur_element])))
    
    for grouped_rel, post_blocks in grouped_relations.items():
        # TODO: avoid deepcopy
        rec_state_copy = rec_state.copy()
        rec_state_copy.block_status[target_element] = list(post_blocks[0])
        rec_state_copy.block_status[cur_element] = list(post_blocks[1])
        for i in range(len(post_blocks[0])):
            logger.info(f'{"    " * rec_state.depth} twotypes: {grouped_rel}, post_blocks: {post_blocks}')
            rec_state_copy.candidate_witness[target_element][i].discard(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].discard(target_element)
        # check satisfiability
        if not check_sat(DomainToCell, ctx.get_witness_relation, 
                            rec_state_copy.block_status, rec_state_copy.candidate_witness):
            logger.info(f'{"    " * rec_state.depth} NO SAT!')
            continue
        
        rec_state_copy.unprocessed_pairs.pop(0)
        subcircuit_index = ctx.gound_rels_subcircuit((target_element, cur_element), grouped_rel)
        if subcircuit_index is not None:
            add_subcircuit(rec_state_copy, subcircuit_index)

def domain_recursion_rel(ctx: Context, domain: list[Const], DomainToCell: dict[Const, Cell],
                     subroot_node: Node, FreePairsRecord: dict[PairSet, list[Node]], 
                     StateCache: dict[RecursionState, int], rec_state: RecursionState):
    # we don't need to process the case where the domain contains only one element
    # this case is covered by the pair_recursion function
    target_element = domain.pop(0)
    logger.info(f'{"    " * rec_state.depth} ego_element: {target_element}')
    pair_recursion(ctx = ctx, 
                    target_element=target_element,
                    domain_todo=domain,
                    domain_done=[],
                    DomainToCell=DomainToCell,
                    subroot_node=subroot_node,
                    FreePairsRecord=FreePairsRecord,
                    StateCache=StateCache,
                    rec_state=rec_state)

def domain_recursion_cell(ctx: Context, todo_domain: list[Const], 
                          DomainToCell: dict[Const, Cell],
                          root_node: Node, facts: set[AtomicFormula] = set()):
    if len(todo_domain) == 0:
        logger.info(f'cell assignment done')
        
        block_status: dict[Const, list[bool]] = {}
        for element in ctx.domain:
            block_status[element] = copy.deepcopy(ctx.blcok_of_cell[DomainToCell[element]])
        
        candidate_witness = init_candidate_witness(DomainToCell, ctx.get_witness_relation, block_status, ctx.domain)
        
        unprocessed_pairs: list[PairWithRel] = []
        for i in range(len(ctx.domain)):
            for j in range(i + 1, len(ctx.domain)):
                e1, e2 = ctx.domain[i], ctx.domain[j]
                c1, c2 = DomainToCell[e1], DomainToCell[e2]
                rels: frozenset[Relation] = frozenset(ctx.rels_of_cells[(c1, c2)])
                assert len(rels) > 0, f'No relations found for {e1}({c1}), {e2}({c2})'
                pair: tuple[tuple[Const, Const], frozenset[Relation]] = ((e1, e2), rels)
                unprocessed_pairs.append(pair)
        
        rec_state = RecursionState(block_status, candidate_witness, unprocessed_pairs)
        FreePairsRecord: dict[PairSet, list[Node]] = {}
        StateCache: dict[RecursionState, int] = {}
        domain_recursion_rel(ctx, copy.deepcopy(ctx.domain), DomainToCell, 
                        root_node, FreePairsRecord, StateCache, rec_state)
        build_subcircuit_for_freepairs(ctx, FreePairsRecord)
        return
    
    target_element = todo_domain.pop(0)
    for cell in ctx.cells:
        cell_evi = remove_aux_atom(cell.get_evidences(target_element))
        if not ctx.sat(facts | cell_evi):
            continue
        logger.info(f"set element {target_element} cell: {cell}")
        and_node = NC.create_node(NodeType.AND, mark=str([evi for evi in cell_evi if evi.positive][0]))
        or_node = NC.create_node(NodeType.OR)
        root_node.children.add(and_node.index)
        and_node.children.add(ctx.cell_subcircuit[cell][target_element])
        and_node.children.add(or_node.index)
        DomainToCell[target_element] = cell
        domain_recursion_cell(ctx, todo_domain, DomainToCell, or_node, facts | cell_evi)
    todo_domain.insert(0, target_element)  # backtrack
    

if __name__ == "__main__":
    # import sys
    # sys.setrecursionlimit(int(1e6))
    args = parse_args()
    logzero.loglevel(logzero.INFO)

    problem = get_problem(args)
    ctx = Context(problem)
    
    root_node = NC.ROOT
    DomainToCell: dict[Const, Cell] = {}
    domain_recursion_cell(ctx, copy.deepcopy(ctx.domain), DomainToCell, root_node)
    
    NC.simplify()
    NC.show_circuit()