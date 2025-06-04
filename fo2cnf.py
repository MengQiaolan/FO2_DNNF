import os
import copy
import logzero
from logzero import logger
import argparse
from itertools import product
import sympy

from wfomc import parse_input
from wfomc.problems import WFOMCProblem
from wfomc.fol.syntax import Const, X, Y, QFFormula, AtomicFormula

def parse_args():
    parser = argparse.ArgumentParser(
        description='Convert a first-order logic sentence to CNF',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('--input', '-i', type=str, required=True, help='sentence file')
    parser.add_argument('--domain-size', '-n', type=int, required=True, help='domain size')
    parser.add_argument('--show', '-s', action='store_true', help='show the circuit')
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
    logzero.loglevel(logzero.INFO)
    args = parse_args()
    sentence_dir = os.path.dirname(args.input)
    sentence_base = os.path.basename(args.input)
    
    problem = get_problem(args)
    # remove the quantifier
    uni_formula: QFFormula = copy.deepcopy(problem.sentence.uni_formula)
    ext_formulas: list[QFFormula] = copy.deepcopy(problem.sentence.ext_formulas)
    while not isinstance(uni_formula, QFFormula):
        uni_formula = uni_formula.quantified_formula
    for i in range(len(ext_formulas)):
        ext_formulas[i] = ext_formulas[i].quantified_formula.quantified_formula
    
    atom_to_digit: dict[AtomicFormula, int] = {}
    atomsym_to_digit: dict[sympy.Symbol, int] = {}
    expr: sympy.Expr = sympy.true
    
    domain = problem.domain
    for (e1, e2) in product(domain, repeat=2):
        ground_uni_formula: QFFormula = uni_formula.substitute({X: e1, Y: e2}) & uni_formula.substitute({X: e2, Y: e1})
        cnf_formula = sympy.to_cnf(ground_uni_formula.expr, simplify=True)
        expr = sympy.And(expr, cnf_formula)

        for atom in ground_uni_formula.atoms():
            if atom not in atom_to_digit:
                atom_to_digit[atom] = len(atom_to_digit)+1
                atomsym_to_digit[atom.expr] = len(atomsym_to_digit)+1
    
    for e1 in domain:
        for ext_formula in ext_formulas:
            ext_expr = sympy.false
            for e2 in domain:
                ground_ext_formula = ext_formula.substitute({X: e1, Y: e2})
                ext_expr = sympy.Or(ext_expr, ground_ext_formula.expr)
                for atom in ground_ext_formula.atoms():
                    if atom not in atom_to_digit:
                        atom_to_digit[atom] = len(atom_to_digit)+1
                        atomsym_to_digit[atom.expr] = len(atomsym_to_digit)+1
            expr = sympy.And(expr, ext_expr)
    # To simplify a logical expression with more than 8 variables may take a long time
    expr = sympy.to_cnf(expr)
    
    klist = list(atom_to_digit.keys())
    vlist = list(atom_to_digit.values())
    kstr = f'c {" ".join([str(k) for k in klist])}\n'
    vstr = f'c {" ".join([str(v) for v in vlist])}\n'
    # print cnf file
    cnf_file_path = os.path.join(sentence_dir, f'{sentence_base[0:-7]}_{len(domain)}.cnf')
    cnf_file = open(cnf_file_path, 'w')
    cnf_file.write(kstr)
    cnf_file.write(vstr)
    cnf_file.write(f"p cnf {len(atom_to_digit)} {len(expr.args)}\n")
    for clause in expr.args:
        clause_str = ""
        
        if isinstance(clause, sympy.Not):
            clause_str += str(-atomsym_to_digit[~clause]) + " "
        elif isinstance(clause, sympy.Symbol):
            clause_str += str(atomsym_to_digit[clause]) + " "
        else:
            for atom in clause.args:
                if isinstance(atom, sympy.Symbol):
                    clause_str += str(atomsym_to_digit[atom]) + " "
                elif isinstance(atom, sympy.Not):
                    clause_str += str(-atomsym_to_digit[~atom]) + " "
                else:
                    raise RuntimeError(f'Unknown atom type: {atom}')
        
        cnf_file.write(clause_str.strip() + " 0\n")
    cnf_file.close()
    logger.info('CNF file written to %s', cnf_file_path)
    
    if not args.show:
        exit(0)
    
    # build the circuit by Bella
    # ./Bella -w -ph -i sentence/{input}.cnf -o sentence/{input}.cir
    os.system(f'./Bella -w -ph \
            -i {cnf_file_path} \
            -o {cnf_file_path}.cir')

    # show the circuit
    # python view.py -i sentence/{input}
    os.system(f'python cnfcir_view.py -i {cnf_file_path[:-4]}')