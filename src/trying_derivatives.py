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
    terms.append((1-t)*s**3)
    terms.append(t*s**3)
    print(expand(diff(terms[6],t)))
    dterms.append(diff(terms[6],t))
    dterms.append(diff(terms[7],t))
    basis_coeffs = symbols("a b c d e f g h")
    to_solve = sum((basis_coeffs[idx]*terms[idx] for idx in range(8)))
    solution = solve(to_solve-dterms[6],basis_coeffs,dict=True)[0]
    print(solution)
    solution_expanded = sum((solution[basis_coeffs[idx]]*terms[idx] for idx in range(8)))
    print(solution_expanded)
    print(expand(solution_expanded))
    print(expand(diff(terms[6],t)))
    print(terms[6])
    print(expand(terms[6]))

    print("Here")
    print(expand(terms[6] - (1-t)*s**3))
    diff_6_0 = -s**3
    diff_6_1 = 3*(1-t)*(1-t)*s**2
    diff_6_2 = -3*(1-t)*t*s**2
    print(expand(diff_6_0+diff_6_1+diff_6_2))
    print(expand(dterms[6]))
