"""
for debugging hardcoded derivatives
"""

from sympy import symbols,expand,solve,diff

if __name__ == '__main__':
    t = symbols('t')
    s = t*(1-t)
    terms = [(1-t),t,(1-t)*s,t*s,(1-t)*s**2,t*s**2]
    dterms = [-1,1,(1-4*t+3*t**2),2*t-3*t**2,2*t-9*t**2+12*t**3-5*t**4,5*t**4-8*t**3+3*t**2]
    for (cur_term,cur_derivative) in zip(terms,dterms):
        x = expand(diff(cur_term,t))
        y = expand(cur_derivative)
        print(x)
        print(y)
        assert x == y
    basis_coeffs = symbols("a b c d e f")
    to_solve = sum((basis_coeffs[idx]*terms[idx] for idx in range(6)))
    for idx in range(6):
        solution = solve(to_solve-dterms[idx],basis_coeffs,dict=True)
        print(solution)
