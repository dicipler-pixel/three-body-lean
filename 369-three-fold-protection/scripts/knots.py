# SCRIPT: SM369-KNOTS — Alexander polynomial (Fox calculus on the Wirtinger presentation) and Fox p-colourings from PD codes
import snappy, sympy as sp
t = sp.symbols('t')
def arcs_of(pd):
    edges = sorted({e for c in pd for e in c}); parent = {e: e for e in edges}
    def f(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a, b, c, d in pd: parent[f(b)] = f(d)          # over-strand edges b, d are one arc
    roots = sorted({f(e) for e in edges}); idx = {r: i for i, r in enumerate(roots)}
    return (lambda e: idx[f(e)]), len(roots)
def alexander(name):
    L = snappy.Link(name); pd = L.PD_code(); A, n = arcs_of(pd); signs = [cr.sign for cr in L.crossings]
    M = sp.zeros(len(pd), n)
    for r, ((a, b, c, d), s) in enumerate(zip(pd, signs)):
        k, i, j = A(b), A(a), A(c)
        if s > 0: M[r, k] += 1 - t; M[r, i] += t; M[r, j] += -1
        else:     M[r, k] += 1 - t; M[r, i] += -1; M[r, j] += t
    D = sp.factor(sp.expand(M[1:, 1:].det()))
    P = sp.Poly(sp.expand(D), t); cs = P.all_coeffs()
    while cs and cs[-1] == 0: cs = cs[:-1]
    if cs and cs[0] < 0: cs = [-x for x in cs]
    return cs, pd, A, n
def colourings(pd, A, n, p):
    # Fox colouring: 2*over - under_in - under_out = 0 mod p ; count = p^(n - rank_p)
    M = sp.zeros(len(pd), n)
    for r, (a, b, c, d) in enumerate(pd): M[r, A(b)] += 2; M[r, A(a)] -= 1; M[r, A(c)] -= 1
    rk = sp.Matrix(M).applyfunc(lambda x: x % p)
    # rank over GF(p)
    from sympy import GF
    from sympy.polys.matrices import DomainMatrix
    dm = DomainMatrix.from_Matrix(rk).convert_to(GF(p))
    return p ** (n - dm.rank())
if __name__ == '__main__':
    for name, label in [('K3a1', 'trefoil 3_1'), ('K4a1', 'figure-eight 4_1'), ('K5a1', '5_2 (K5a1)'), ('K11n34', 'Conway knot 11n34'), ('K11n42', 'Kinoshita-Terasaka 11n42'), ('K9a40', 'K9a40 (det 27)'), ('K6a3','6_1 stevedore')]:
        try:
            cs, pd, A, n = alexander(name); det = abs(sum(c*(-1)**k for k, c in enumerate(cs)))
            print(f'{label:28s} crossings={len(pd):2d} Delta coeffs={cs} det=|Delta(-1)|={det}  det mod 3={det%3}  det mod 9={det%9}  #3-colourings={colourings(pd,A,n,3)}  #5-colourings={colourings(pd,A,n,5)}')
        except Exception as e: print(label, 'ERR', e)
