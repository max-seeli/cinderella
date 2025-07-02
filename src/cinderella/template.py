from itertools import product
from typing import List

import sympy as sp


def get_template(coeffs_name: str, variables: List[sp.Symbol], degree: int, c: int, d: int) -> sp.Expr:
    """
    Get a template over the given variables with the given degree.
    Coefficients are named with the given name and indexed for unique identification.
    The template is a CNF formula with c conjunctions of d disjunctions.

    Parameters
    ----------
    coeffs_name : str
        The name of the coefficients.
    variables : List[sp.Symbol]
        The variables of the template expression.
    degree : int
        The degree of the template expression.
    c : int
        The number of conjunctions in the template.
    d : int
        The number of disjunctions in the template.

    Returns
    -------
    sp.Expr
        The template expression.
    """
    if degree == 1:
        get_expression = lambda name: get_linear_expression(name, variables)
    else:
        get_expression = lambda name: get_polynomial_expression(name, variables, degree)
    expressions = [get_expression(f'{coeffs_name}_{i}') >= 0 for i in range(c * d)]
    conjunctions = [sp.Or(*expressions[i * d:(i + 1) * d]) for i in range(c)]
    return sp.And(*conjunctions)

def get_linear_expression(coeffs_name: str, variables: List[sp.Symbol]) -> sp.Expr:
    """
    Get a linear expression given the coefficients and the variables.

    Parameters
    ----------
    coeffs_name : str
        The name of the coefficients.
    variables : List[sp.Symbol]
        The variables of the linear expression.

    Returns
    -------
    sp.Expr
        The linear expression.
    """
    coeffs = [sp.Symbol(f'{coeffs_name}_{i}')
              for i in range(len(variables) + 1)]
    return coeffs[0] + sum([coeff * variable for variable, coeff in zip(variables, coeffs[1:])])


def get_polynomial_expression(coeffs_name: str, variables: List[sp.Symbol], degree: int) -> sp.Expr:
    """
    Get a polynomial expression over the given variables with the given degree.
    Coefficients are named with the given name and indexed for unique identification. 

    Parameters
    ----------
    coeffs_name : str
        The name of the coefficients.
    variables : List[sp.Symbol]
        The variables of the polynomial expression.
    degree : int
        The degree of the polynomial expression.

    Returns
    -------
    sp.Expr
        The polynomial expression.
    """
    monomials = get_all_monomials(variables, degree)
    coeffs = [sp.Symbol(f'{coeffs_name}_{i}')
              for i in range(len(monomials))]
    return sum([coeff * monomial for coeff, monomial in zip(coeffs, monomials)])


def get_all_monomials(variables: List[sp.Symbol], degree: int) -> List[sp.Expr]:
    """
    Get all monomials of a given degree over the variables.

    Parameters
    ----------
    variables : List[sp.Symbol]
        The variables of the monomials.
    degree : int
        The degree of the monomials.

    Returns
    -------
    List[sp.Expr]
        The list of monomials.
    """
    monomials = []
    for exponents in product(range(degree + 1), repeat=len(variables)):
        if sum(exponents) <= degree:
            monomials.append(sp.prod(
                [variable**exponent for variable, exponent in zip(variables, exponents)]))
    return monomials
