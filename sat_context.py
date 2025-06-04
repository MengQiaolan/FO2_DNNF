import os
import copy
import logzero
from logzero import logger
import argparse
from itertools import product
import sympy

from sympy.logic.inference import satisfiable

from pysat.solvers import Solver

from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import X, Y, QFFormula

def init_expr(problem: WFOMCProblem):
    domain = problem.domain
    uni_formula: QFFormula = copy.deepcopy(problem.sentence.uni_formula)
    ext_formulas: list[QFFormula] = copy.deepcopy(problem.sentence.ext_formulas)
    while not isinstance(uni_formula, QFFormula):
        uni_formula = uni_formula.quantified_formula
    for i in range(len(ext_formulas)):
        ext_formulas[i] = ext_formulas[i].quantified_formula.quantified_formula
    
    cnf_expr: sympy.Expr = sympy.true
    
    for (e1, e2) in product(domain, repeat=2):
        ground_uni_formula: QFFormula = uni_formula.substitute({X: e1, Y: e2}) & uni_formula.substitute({X: e2, Y: e1})
        cnf_uni_expr = sympy.to_cnf(ground_uni_formula.expr, simplify=True)
        cnf_expr = sympy.And(cnf_expr, cnf_uni_expr)
    
    for ext_formula in ext_formulas:
        for e1 in domain:
            ext_expr = sympy.false
            for e2 in domain:
                ground_ext_formula = ext_formula.substitute({X: e1, Y: e2})
                ext_expr = sympy.Or(ext_expr, ground_ext_formula.expr)
            ext_expr = sympy.to_cnf(ext_expr, simplify=True)
            cnf_expr = sympy.And(cnf_expr, ext_expr)
    
    assert satisfiable(cnf_expr, algorithm="minisat22") != False
    return cnf_expr

class SatContext:
    def __init__(self, problem: WFOMCProblem):
        
        self.sympy_cnf: sympy.Expr = init_expr(problem)
        
        self.vmap: dict[sympy.Symbol, int] = {}
        self.inv_vmap: dict[int, sympy.Symbol] = {}
        for i, var in enumerate(self.sympy_cnf.free_symbols):
            self.vmap[var] = i+1
            self.inv_vmap[i+1] = var
        
        self.cnf = self.init_cnf()
        self.solver: Solver = Solver(name='m22', bootstrap_with=self.cnf)

            
    def init_cnf(self):
        cnf_clauses = []
        if isinstance(self.sympy_cnf, sympy.And):
            for clause in self.sympy_cnf.args:
                cnf_clauses.append(self.sympy_clause_to_ints(clause))
        else:
            cnf_clauses.append(self.sympy_clause_to_ints(self.sympy_cnf))
        return cnf_clauses
    
    def sympy_clause_to_ints(self, clause):
        if isinstance(clause, sympy.Or):
            return [self.lit_to_int(arg) for arg in clause.args]
        else:
            return [self.lit_to_int(clause)]

    def lit_to_int(self, literal):
        if isinstance(literal, sympy.Not):
            return -self.vmap[literal.args[0]]
        else:
            return self.vmap[literal]


    def sat(self, atom_list: set[sympy.Symbol]):
        assumptions = []
        for atom in atom_list:
            if atom in self.vmap:
                assumptions.append(self.vmap[atom])
            elif ~atom in self.vmap:
                assumptions.append(-self.vmap[~atom])
            else:
                raise ValueError(f"Atom {atom} not found in variable map.")
        return self.solver.solve(assumptions=assumptions)