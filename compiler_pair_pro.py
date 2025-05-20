import os
import copy
import logging
import logzero
import argparse
import sympy
from logzero import logger
import functools

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const, X, Y
from wfomc.cell_graph.cell_graph import Cell, AtomicFormula

from circuit import NodeType, Node, NC

from context import Context
from compilation_utils import check_sat, RecursionState, init_candidate_witness, is_isomorphic, build_subcircuit_for_freepairs

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
        and_node = NC.create_node(NodeType.AND)
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
    
    # if the target element and the current element are not blocked, we don't need to branch further
    if not any(rec_state.block_status[target_element]) and not any(rec_state.block_status[cur_element]):
        rec_state_copy = rec_state.copy()
        rec_state_copy.unprocessed_pair.remove(frozenset([target_element, cur_element]))
        for i in range(len(rec_state_copy.block_status[target_element])):
            rec_state_copy.candidate_witness[target_element][i].remove(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].remove(target_element)
        rels = frozenset(ctx.rels_of_cells[(DomainToCell[target_element], DomainToCell[cur_element])])
        subcircuit_index = ctx.gound_rels_subcircuit((target_element, cur_element), rels)
        add_subcircuit(rec_state_copy, subcircuit_index)
        return
        
    logger.info(f'{"    " * rec_state.depth} other_element: {cur_element}, pair: {[target_element, cur_element]}')
    tgt_cell = DomainToCell[target_element]
    cur_cell = DomainToCell[cur_element]
    for subcircuit_index, expr, breakblock in ctx.get_all_subcircuit((tgt_cell, cur_cell), (target_element, cur_element)):
        rec_state_copy = rec_state.copy()
        # update the block status and candidate witness
        for i in range(len(breakblock[0])):
            rec_state_copy.candidate_witness[target_element][i].remove(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].remove(target_element)
            if breakblock[0][i]:
                rec_state_copy.block_status[target_element][i] = False
            if breakblock[1][i]:
                rec_state_copy.block_status[cur_element][i] = False
        logger.info(f'{"    " * rec_state.depth} expr: {expr}, block: {rec_state_copy.block_status}')
        # check satisfiability
        logger.info(f'{"    " * rec_state.depth} candidate_witness: {rec_state_copy.candidate_witness}')
        if not check_sat(DomainToCell, ctx.get_witness_relation, 
                            rec_state_copy.block_status, rec_state_copy.candidate_witness):
            logger.info(f'{"    " * rec_state.depth} NO SAT!')
            continue
        # remove the pair from unprocessed_pair
        rec_state_copy.unprocessed_pair.remove(frozenset([target_element, cur_element]))
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