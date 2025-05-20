import os
import copy
import logging
import logzero
import argparse
import sympy
from logzero import logger

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const, X, Y
from wfomc.cell_graph.cell_graph import Cell, AtomicFormula

from utils import NodeType, create_node, Node, print_circuit

import context
from context import EXT_PRED_PREFIX


class RecursionState:
    def __init__(self, block_status: dict[Const, list[bool]],
                 candidate_witness: dict[Const, list[list[Const]]], 
                 unprocessed_pair: set[frozenset[Const]], 
                 detetermined_facts: set[str],
                 depth: int = 0):
        
        self.depth = depth
        self.block_status = block_status
        self.unprocessed_pair = unprocessed_pair
        self.candidate_witness = candidate_witness
        self.detetermined_facts = detetermined_facts

    def copy(self):
        return RecursionState(copy.deepcopy(self.block_status), 
                              copy.deepcopy(self.candidate_witness), 
                              copy.deepcopy(self.unprocessed_pair), 
                              copy.deepcopy(self.detetermined_facts), 
                              self.depth)

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

def init_candidate_witness(domain_to_cell: dict[Const, context.Cell], 
                          rel_dict: dict[tuple[Cell, Cell], list[frozenset[AtomicFormula]]],
                          block_status: dict[Const, list[bool]],
                          domain: set[Const]):
    candidate_witness: dict[Const, list[list[Const]]] = {}
    for element in domain:
        candidate_witness[element] = []
        for idx_ext, block in enumerate(block_status[element]):
            if not block:
                candidate_witness[element].append(None)
                continue
            witness_list = []
            for wit in domain:
                if element == wit:
                    continue
                for _, rel in enumerate(rel_dict[(domain_to_cell[element], domain_to_cell[wit])]):
                    for atom in rel:
                        if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive and \
                                int(atom.pred.name[len(EXT_PRED_PREFIX):]) == idx_ext and atom.args[0] == X:
                            witness_list.append(wit)
            assert len(witness_list) != 0
            candidate_witness[element].append(witness_list)
    return candidate_witness

def check_sat(domain_to_cell: dict[Const, Cell],
              get_witness_relation: callable,
              block_status: dict[Const, list[bool]], 
              candidate_witness: dict[Const, list[list[Const]]]) -> bool:
    for ego_element, blocks in block_status.items():
        for block_idx, block in enumerate(blocks):
            if not block:
                continue
            if len(candidate_witness[ego_element][block_idx]) == 0:
                return False
            # 先只考虑一个 1-type 的情况
            for witness in candidate_witness[ego_element][block_idx]:
                for (rel, atom) in get_witness_relation(domain_to_cell[ego_element], domain_to_cell[witness], block_idx):
                    block_status_copy = copy.deepcopy(block_status)
                    candidate_witness_copy = copy.deepcopy(candidate_witness)
                    # update block status and candidate witness
                    for atom in rel:
                        if atom.pred.name.startswith(EXT_PRED_PREFIX) and atom.positive:
                            if atom.args[0] == X:
                                block_status_copy[ego_element][int(atom.pred.name[len(EXT_PRED_PREFIX):])] = False
                            else:
                                block_status_copy[witness][int(atom.pred.name[len(EXT_PRED_PREFIX):])] = False
                    for i in range(len(block_status[ego_element])):
                        candidate_witness_copy[witness][i].remove(ego_element)
                        candidate_witness_copy[ego_element][i].remove(witness)
                    if check_sat(domain_to_cell, get_witness_relation, block_status_copy, candidate_witness_copy):
                        return True  
    sat_flag = True
    for blocks in block_status.values():
        if not any(blocks):
            continue
        sat_flag = False
        break 
    return sat_flag

def is_isomorphic(state: RecursionState, state_cache: dict[RecursionState, int]):
    for key, value in state_cache.items():
        if state.block_status == key.block_status and \
                state.candidate_witness == key.candidate_witness and \
                state.unprocessed_pair == key.unprocessed_pair:
            return value
    return None

def pair_recursion(ctx: context.Context, 
                   target_element: Const, domain_todo: list[Const], domain_done: list[Const], 
                   DomainToCell: dict[Const, Cell], subroot_node: Node, 
                   FreePairRecord: dict[frozenset[frozenset[Const]], list[Node]], StateCache: dict[RecursionState, int], 
                   rec_state: RecursionState):
    if len(domain_todo) == 0:
        logger.info(f'{"    " * rec_state.depth} No more elements in domain, return')
        domain_recursion(ctx, domain_done, DomainToCell,
                         subroot_node, FreePairRecord, StateCache, rec_state)
        return
    # if all elements are not blocked, we can skip it
    if all(not any(rec_state.block_status[element]) for element in [target_element] + domain_todo + domain_done):
        logger.info(f'{"    " * rec_state.depth} All elements are not blocked, end')    
        remaining_pair_set = rec_state.unprocessed_pair
        if remaining_pair_set:
            if len(remaining_pair_set) == 1:
                subroot_node.children.add(ctx.pair_to_node_index[next(iter(remaining_pair_set))])
            else:
                FreePairRecord.setdefault(frozenset(remaining_pair_set), []).append(subroot_node)
        return
    
    rec_state.depth += 1
    
    cur_element = domain_todo[0]
    domain_todo = domain_todo[1:]
    domain_done = domain_done + [cur_element]
    
    def add_subcircuit(rec_state_: RecursionState, subcircuit_index_: int):
        and_node = create_node(NodeType.AND)
        subroot_node.children.add(and_node.index)
        and_node.children.add(subcircuit_index_)
        isomorphic_node_index = is_isomorphic(rec_state_, StateCache) 
        if isomorphic_node_index is not None:
            logger.info(f'{"    " * rec_state_.depth} Isomorphic: {rec_state_.detetermined_facts}')
            and_node.children.add(isomorphic_node_index)
        else:
            new_subroot_node = create_node(NodeType.OR)
            and_node.children.add(new_subroot_node.index)
            StateCache[rec_state_] = new_subroot_node.index
            pair_recursion(ctx, target_element, domain_todo.copy(), domain_done.copy(), DomainToCell,
                            new_subroot_node, FreePairRecord, StateCache, rec_state_)
        
    
    if not any(rec_state.block_status[target_element]) and not any(rec_state.block_status[cur_element]):
        rec_state_copy = rec_state.copy()
        rec_state_copy.unprocessed_pair.remove(frozenset([target_element, cur_element]))
        for i in range(len(rec_state_copy.block_status[target_element])):
            rec_state_copy.candidate_witness[target_element][i].remove(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].remove(target_element)
        
        # and_node = create_node(NodeType.AND)
        # subroot_node.children.add(and_node.index)
        # and_node.children.add(ctx.pair_to_node_index[frozenset([target_element, cur_element])])        
        # # add the OR node for remaining (cache first)
        # isomorphic_node_index = is_isomorphic(rec_state_copy, StateCache) 
        # if isomorphic_node_index is not None:
        #     logger.info(f'{"    " * rec_state.depth} Isomorphic: {rec_state_copy.detetermined_facts}')
        #     and_node.children.add(isomorphic_node_index)
        # else:
        #     new_subroot_node = create_node(NodeType.OR)
        #     and_node.children.add(new_subroot_node.index)
        #     StateCache[rec_state_copy] = new_subroot_node.index
        #     pair_recursion(ctx, target_element, domain_todo.copy(), domain_done.copy(), DomainToCell,
        #                     new_subroot_node, FreePairRecord, StateCache, rec_state_copy)
        add_subcircuit(rec_state_copy, ctx.pair_to_node_index[frozenset([target_element, cur_element])])
        return
        
    
    logger.info(f'{"    " * rec_state.depth} other_element: {cur_element}, pair: {[target_element, cur_element]}')
    tgt_cell = DomainToCell[target_element]
    cur_cell = DomainToCell[cur_element]
    for subcircuit_index, expr, breakblock in ctx.get_all_subcircuit((tgt_cell, cur_cell), (target_element, cur_element)):
        rec_state_copy = rec_state.copy()
        # update the block status and candidate witness
        for i in range(len(breakblock[0])):
            logger.info(f'{"    " * rec_state.depth} expr: {expr}, breakblock: {breakblock}')
            rec_state_copy.candidate_witness[target_element][i].remove(cur_element)
            rec_state_copy.candidate_witness[cur_element][i].remove(target_element)
            if breakblock[0][i]:
                rec_state_copy.block_status[target_element][i] = False
            if breakblock[1][i]:
                rec_state_copy.block_status[cur_element][i] = False 
        # check satisfiability
        if not check_sat(DomainToCell, ctx.get_witness_relation, 
                            rec_state_copy.block_status, rec_state_copy.candidate_witness):
            logger.info(f'{"    " * rec_state.depth} NO SAT!')
            continue
        
        # remove the pair from unprocessed_pair
        rec_state_copy.unprocessed_pair.remove(frozenset([target_element, cur_element]))
        
        # # create the AND node
        # and_node = create_node(NodeType.AND)
        # subroot_node.children.add(and_node.index)
        
        # # add the subcircuit
        # and_node.children.add(subcircuit_index)
        
        # # add the OR node for remaining (cache first)
        # isomorphic_node_index = is_isomorphic(rec_state_copy, StateCache) 
        # if isomorphic_node_index is not None:
        #     logger.info(f'{"    " * rec_state.depth} Isomorphic: {rec_state_copy.detetermined_facts}')
        #     and_node.children.add(isomorphic_node_index)
        # else:
        #     new_subroot_node = create_node(NodeType.OR)
        #     and_node.children.add(new_subroot_node.index)
        #     StateCache[rec_state_copy] = new_subroot_node.index
        #     pair_recursion(ctx, target_element, domain_todo.copy(), domain_done.copy(), DomainToCell,
        #                     new_subroot_node, FreePairRecord, StateCache, rec_state_copy)
        add_subcircuit(rec_state_copy, subcircuit_index)


def domain_recursion(ctx: context.Context, domain: list[Const], DomainToCell: dict[Const, Cell],
                     subroot_node: Node, FreePairRecord: dict[frozenset[frozenset[Const]], list[Node]], 
                     StateCache: dict[RecursionState, int], rec_state: RecursionState):
    if len(domain) == 1:
        remaining_pair_set = rec_state.unprocessed_pair
        if remaining_pair_set:
            if len(remaining_pair_set) == 1:
                subroot_node.children.add(ctx.pair_to_node_index[next(iter(remaining_pair_set))])
            else:
                FreePairRecord.setdefault(frozenset(remaining_pair_set), []).append(subroot_node)
        return

    target_element = domain[0]
    domain = domain[1:]
    logger.info(f'{"    " * rec_state.depth} ego_element: {target_element}')
    
    pair_recursion(ctx = ctx, 
                    target_element=target_element,
                    domain_todo=domain,
                    domain_done=[],
                    DomainToCell=DomainToCell,
                    subroot_node=subroot_node,
                    FreePairRecord=FreePairRecord,
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
    ctx = context.Context(problem)
    
    # assign cell to each element in the domain
    DomainToCell: dict[Const, context.Cell] = {}
    for element in ctx.domain:
        DomainToCell[element] = ctx.cells[0]
    
    # init
    block_status: dict[Const, list[bool]] = {}
    for element in ctx.domain:
        block_status[element] = copy.deepcopy(ctx.blcok_of_cell[DomainToCell[element]])
    
    candidate_witness = init_candidate_witness(DomainToCell, ctx.rels_of_cells, block_status, ctx.domain)
    
    unprocessed_pair = set()
    for idx, element in enumerate(ctx.domain):
        for idx_2 in range(idx + 1, len(ctx.domain)):
            if frozenset([element, ctx.domain[idx_2]]) not in unprocessed_pair:
                unprocessed_pair.add(frozenset([element, ctx.domain[idx_2]]))
    
    rec_state = RecursionState(block_status, candidate_witness, unprocessed_pair, set())
    
    root_node = create_node(NodeType.OR)
    
    FreePairRecord: dict[frozenset[frozenset[Const]], list[Node]] = {}
    StateCache: dict[RecursionState, int] = {}
    
    domain_recursion(ctx, copy.deepcopy(ctx.domain), DomainToCell, 
                     root_node, FreePairRecord, StateCache, rec_state)
    
    ordered_list_of_cset: list[frozenset[frozenset[Const]]] = []
    for key in FreePairRecord.keys():
        if len(key) > 1:
            ordered_list_of_cset.append(key)
    ordered_list_of_cset.sort(key=lambda x: len(x))    
    
    print("-----------------------------------")    
    print("-----------------------------------")
    
    min_size_dict: dict[frozenset[Const], int] = {}
    representation: dict[frozenset[Const], list[frozenset[Const]]] = {}
    cset_to_node_index: dict[frozenset[Const], int] = {}
    
    def build_subcircuit_for_C(s: frozenset[Const]) -> tuple:
        if len(s) == 0:
            return 0, set()
        # if the set only contains one pair, return the node index directly
        if len(s) == 1:
            return 1, {ctx.pair_to_node_index[next(iter(s))]}
        # if the set is already processed, return the size and the node index
        if s in cset_to_node_index:
            return 1, {cset_to_node_index[s]}
        
        min_size = len(s)
        children = set()
        for pair in s:
            children.add(ctx.pair_to_node_index[pair])
        for smaller_set in ordered_list_of_cset:
            if len(smaller_set) >= len(s): # 这里使用>= 而不是 >，因为如果s就在ordered_list_of_cset中的话，在前面一个if就会判断出来
                break
            if smaller_set.issubset(s):
                diffset_size, diffset_node = build_subcircuit_for_C(frozenset(s - smaller_set))
                if min_size > 1 + diffset_size:
                    min_size = 1 + diffset_size
                    children = diffset_node | {cset_to_node_index[smaller_set]}
                    if min_size == 2: # the optimal case, we can stop here
                        break
        # TODO: whether create an AND node for the remaining pairs
        if s in ordered_list_of_cset:
            and_node = create_node(NodeType.AND)
            for child in children:
                and_node.children.add(child)
            cset_to_node_index[s] = and_node.index
            return min_size, {cset_to_node_index[s]}
        else:
            return len(s), set(ctx.pair_to_node_index[pair] for pair in s)
    
    for cset in ordered_list_of_cset:
        node_index = build_subcircuit_for_C(cset)
        for node in FreePairRecord[cset]:
            node.children.add(cset_to_node_index[cset])

    print_circuit(root_node)