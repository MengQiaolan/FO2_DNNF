import copy
import logging
import logzero
import argparse
from logzero import logger

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const
from wfomc.cell_graph.cell_graph import Cell

from circuit import NodeType, Node, NC
from context import group_relations_by_blocks, Context
from compilation_utils import *

class RecursionState:
    def __init__(self, block_status: dict[Const, list[bool]],
                 candidate_witness: dict[Const, list[set[Const]]], 
                 unprocessed_pair: set[frozenset[Const]], 
                 depth: int = 0):
        self.depth = depth
        self.block_status = block_status
        self.unprocessed_pair = unprocessed_pair
        self.candidate_witness = candidate_witness

    def copy(self):
        return RecursionState(copy.deepcopy(self.block_status), 
                              copy.deepcopy(self.candidate_witness), 
                              copy.deepcopy(self.unprocessed_pair), 
                              self.depth)

def is_isomorphic(state: RecursionState, state_cache: dict[RecursionState, int]):
    for key, value in state_cache.items():
        if state.block_status == key.block_status and \
                state.candidate_witness == key.candidate_witness and \
                state.unprocessed_pair == key.unprocessed_pair:
            return value
    return None

def build_subcircuit_for_freepairs(ctx: Context, DomainToCell: dict[Const, Cell],
                                   FreePairsRecord: dict[frozenset[frozenset[Const]], list[Node]]):
    orderedlist_freepairs: list[frozenset[frozenset[Const]]] = [key for key in FreePairsRecord.keys()]
    orderedlist_freepairs.sort(key=lambda x: len(x))
    # NOTE: the freepairs must be progressive, i.e., s_{i} is a subset of s_{i+1} and len(s_{i})+1 = len(s_{i+1})
    # this is guaranteed by the way we generate the freepairs in the recursion
    
    pre_freepairs = set()
    pre_subroot = None
    for freepairs in orderedlist_freepairs:
        e_1, e_2 = tuple(next(iter(freepairs - pre_freepairs)))
        rels = frozenset(ctx.rels_of_cells[(DomainToCell[e_1], DomainToCell[e_2])])
        cur_subroot = ctx.gound_rels_subcircuit((e_1, e_2), rels)
        
        if cur_subroot is not None and pre_subroot is not None:
            and_node = NC.create_node(NodeType.AND)
            and_node.children.update({pre_subroot, cur_subroot})
            new_subroot = and_node.index
        elif cur_subroot is not None:
            new_subroot = cur_subroot
        elif pre_subroot is not None:
            new_subroot = pre_subroot
        else:
            new_subroot = None
        
        if new_subroot is not None:
            for node in FreePairsRecord[freepairs]:
                node.children.add(new_subroot)
        pre_subroot = new_subroot
        pre_freepairs = freepairs

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
                   FreePairsRecord: dict[frozenset[frozenset[Const]], list[Node]], StateCache: dict[RecursionState, int], 
                   rec_state: RecursionState):
    # if all elements are not blocked, we can skip it
    if all(not any(rec_state.block_status[element]) for element in [target_element] + domain_todo + domain_done):
        logger.info(f'{"    " * rec_state.depth} All elements are not blocked, end')    
        if rec_state.unprocessed_pair:
            FreePairsRecord.setdefault(frozenset(rec_state.unprocessed_pair), []).append(subroot_node)
        return
    
    if len(domain_todo) == 0:
        logger.info(f'{"    " * rec_state.depth} No more elements in domain, return')
        domain_recursion(ctx, domain_done, DomainToCell,
                         subroot_node, FreePairsRecord, StateCache, rec_state)
        return
    
    rec_state.depth += 1
    
    cur_element = domain_todo[0]
    domain_todo = domain_todo[1:]
    domain_done = domain_done + [cur_element]
    
    def add_subcircuit(rec_state_: RecursionState, subcircuit_index_: int):
        # create the AND node
        subroot_node.mark = f'{target_element},{cur_element}'
        and_node = NC.create_node(NodeType.AND, mark=f'{target_element},{cur_element}')
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
        rec_state_copy = rec_state.copy()
        rec_state_copy.block_status[target_element] = list(post_blocks[0])
        rec_state_copy.block_status[cur_element] = list(post_blocks[1])
        for i in range(len(post_blocks[0])):
            logger.info(f'{"    " * rec_state.depth} twotypes: {grouped_rel}, post_blocks: {post_blocks}')
            rec_state_copy.candidate_witness[target_element][i].remove(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].remove(target_element)
        # check satisfiability
        if not check_sat(DomainToCell, ctx.get_witness_relation, 
                            rec_state_copy.block_status, rec_state_copy.candidate_witness):
            logger.info(f'{"    " * rec_state.depth} NO SAT!')
            continue
        rec_state_copy.unprocessed_pair.remove(frozenset([target_element, cur_element]))
        subcircuit_index = ctx.gound_rels_subcircuit((target_element, cur_element), grouped_rel)
        if subcircuit_index is not None:
            add_subcircuit(rec_state_copy, subcircuit_index)

def domain_recursion(ctx: Context, domain: list[Const], DomainToCell: dict[Const, Cell],
                     subroot_node: Node, FreePairsRecord: dict[frozenset[frozenset[Const]], list[Node]], 
                     StateCache: dict[RecursionState, int], rec_state: RecursionState):
    target_element = domain[0]
    domain = domain[1:]
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

if __name__ == "__main__":
    # import sys
    # sys.setrecursionlimit(int(1e6))
    args = parse_args()
    if args.debug:
        logzero.loglevel(logging.DEBUG)
    else:
        logzero.loglevel(logging.INFO)

    problem = get_problem(args)
    ctx = Context(problem)
    
    # assign cell to each element in the domain
    DomainToCell: dict[Const, Cell] = {}
    for element in ctx.domain:
        DomainToCell[element] = ctx.cells[0]
    
    # init
    block_status: dict[Const, list[bool]] = {}
    for element in ctx.domain:
        block_status[element] = copy.deepcopy(ctx.blcok_of_cell[DomainToCell[element]])
    
    candidate_witness = init_candidate_witness(DomainToCell, ctx.get_witness_relation, block_status, ctx.domain)
    
    unprocessed_pair = set()
    for i in range(len(ctx.domain)):
        for j in range(i + 1, len(ctx.domain)):
            unprocessed_pair.add(frozenset([ctx.domain[i], ctx.domain[j]]))
    
    rec_state = RecursionState(block_status, candidate_witness, unprocessed_pair)
    
    root_node = NC.ROOT
    FreePairsRecord: dict[frozenset[frozenset[Const]], list[Node]] = {}
    StateCache: dict[RecursionState, int] = {}
    
    domain_recursion(ctx, copy.deepcopy(ctx.domain), DomainToCell, 
                     root_node, FreePairsRecord, StateCache, rec_state)
    
    build_subcircuit_for_freepairs(ctx, DomainToCell, FreePairsRecord)
    NC.simplify()
    NC.show_circuit()