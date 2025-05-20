import os
import copy
import logging
import logzero
import argparse
from itertools import product
import sympy

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const, X, Y, QFFormula

def parse_args():
    parser = argparse.ArgumentParser(
        description='WFOMC for MLN',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--input', '-i', type=str, required=True, help='sentence file')
    parser.add_argument('--domain-size', '-n', type=int, required=True, help='domain size')
    parser.add_argument('--build', default=True, action='store_true', help='build the circuit')
    parser.add_argument('--show', default=True, action='store_true', help='show the circuit')
    parser.add_argument('--debug', action='store_true', default=False)
    args = parser.parse_args()
    return args

def get_problem(args) -> WFOMCProblem:
    problem = parse_input(args.input)
    new_domain: set[Const] = set()
    for i in range(args.domain_size):
        new_domain.add(Const(f'{i}'))
    problem.domain = new_domain
    return problem

if __name__ == "__main__":
    args = parse_args()
    if args.debug:
        logzero.loglevel(logging.DEBUG)
    else:
        logzero.loglevel(logging.INFO)
    problem = get_problem(args)
    
    # remove the quantifier
    uni_formula: QFFormula = copy.deepcopy(problem.sentence.uni_formula)
    ext_formulas: list[QFFormula] = copy.deepcopy(problem.sentence.ext_formulas)
    while not isinstance(uni_formula, QFFormula):
        uni_formula = uni_formula.quantified_formula
    for i in range(len(ext_formulas)):
        ext_formulas[i] = ext_formulas[i].quantified_formula.quantified_formula
    
    atom_to_sym: dict[str, sympy.Symbol] = {}
    sym_to_digit: dict[sympy.Symbol, int] = {}
    expr: sympy.Expr = sympy.true
    
    domain = problem.domain
    # element pair in the domain
    for (e1, e2) in product(domain, repeat=2):
        # TODO: now ignore the same element pair (only consider one cell)
        if e1 == e2:
            continue
        
        element_pair_expr = sympy.false
        ground_uni_formula = uni_formula.substitute({X: e1, Y: e2}) & uni_formula.substitute({X: e2, Y: e1})
        for model in ground_uni_formula.models():
            model_clause: sympy.Expr = sympy.true
            for lit in model:
                if lit.args[0] == lit.args[1]:
                    continue # TODO: now only consider one cell
                if lit.positive:
                    if lit.__str__() not in atom_to_sym:
                        new_sym = sympy.Symbol(lit.__str__())
                        atom_to_sym[lit.__str__()] = new_sym
                        sym_to_digit[new_sym] = len(atom_to_sym)
                    model_clause = sympy.And(model_clause, atom_to_sym[lit.__str__()])
                else:
                    if (~lit).__str__() not in atom_to_sym:
                        new_sym = sympy.Symbol((~lit).__str__())
                        atom_to_sym[(~lit).__str__()] = new_sym
                        sym_to_digit[new_sym] = len(atom_to_sym)
                    model_clause = sympy.And(model_clause, ~atom_to_sym[(~lit).__str__()])
            element_pair_expr = sympy.Or(element_pair_expr, model_clause)
        expr = sympy.And(expr, element_pair_expr)
        
    for e1 in domain:
        for ext_formula in ext_formulas:
            ext_expr = sympy.false
            for e2 in domain:
                if e1 == e2:
                    continue # TODO
                model_expr = sympy.false
                ground_ext_formula = ext_formula.substitute({X: e1, Y: e2})
                for model in ground_ext_formula.models():
                    model_clause: sympy.Expr = sympy.true
                    for lit in model:
                        if lit.args[0] == lit.args[1]:
                            continue # TODO
                        if lit.positive:
                            if lit.__str__() not in atom_to_sym:
                                new_sym = sympy.Symbol(lit.__str__())
                                atom_to_sym[lit.__str__()] = new_sym
                                sym_to_digit[new_sym] = len(atom_to_sym)
                            model_clause = sympy.And(model_clause, atom_to_sym[lit.__str__()])
                        else:
                            if (~lit).__str__() not in atom_to_sym:
                                new_sym = sympy.Symbol((~lit).__str__())
                                atom_to_sym[(~lit).__str__()] = new_sym
                                sym_to_digit[new_sym] = len(atom_to_sym)
                            model_clause = sympy.And(model_clause, ~atom_to_sym[(~lit).__str__()])
                    model_expr = sympy.Or(model_expr, model_clause)
                ext_expr = sympy.Or(ext_expr, model_expr)
            expr = sympy.And(expr, ext_expr)
    # To simplify a logical expression with more than 8 variables may take a long time
    expr = sympy.to_cnf(expr, simplify=False)
    
    klist = list(sym_to_digit.keys())
    vlist = list(sym_to_digit.values())
    kstr = f'c {" ".join([str(k) for k in klist])}\n'
    vstr = f'c {" ".join([str(v) for v in vlist])}\n'
    # print cnf file
    cnf_file = open(os.path.join(os.path.dirname(args.input), f'{os.path.basename(args.input)[0:-7]}_{len(domain)}.cnf'), 'w')
    cnf_file.write(kstr)
    cnf_file.write(vstr)
    cnf_file.write(f"p cnf {len(atom_to_sym)} {len(expr.args)}\n")
    for clause in expr.args:
        clause_str = ""
        for atom in clause.args:
            if isinstance(atom, sympy.Symbol):
                clause_str += str(sym_to_digit[atom]) + " "
            else:
                clause_str += str(-sym_to_digit[~atom]) + " "
        cnf_file.write(clause_str.strip() + " 0\n")
    cnf_file.close()
    
    # build the circuit by Bella
    # ./Bella -w -ph -i sentence/{input}.cnf -o sentence/{input}.cir
    os.system(f'./Bella -w -ph \
            -i {os.path.join(os.path.dirname(args.input), f"{os.path.basename(args.input)[0:-7]}_{len(domain)}.cnf")} \
            -o {os.path.join(os.path.dirname(args.input), f"{os.path.basename(args.input)[0:-7]}_{len(domain)}.cir")}')

    # show the circuit
    # python view.py -i sentence/{input}
    os.system(f'python view.py -i {os.path.join(os.path.dirname(args.input), f"{os.path.basename(args.input)[0:-7]}_{len(domain)}")}')