#!/usr/bin/env python3
"""Exact checks behind the nilpotent-principle notes.

Two objects, both claimed to sit on the wall where the trace form tr(T^2) vanishes on a traceless
2x2 matrix:
  (1) the peel loop's shifted matrix W+1 (Light Keeps the Ledger, LoopWall/ExceptionalPoint*.lean),
      the COMPLEX member;
  (2) the circular-orbit generator A = [[0,1],[-k^2,0]] of bh_isco_10.py, the REAL member, whose
      unfolding constant is claimed to be sqrt(2 V'''(6)) = sqrt2/18.
Also checks the eigenvector condition number law kappa^2 delta = 2 + 2 delta + O(delta^2), with
delta = tanh^2(r/2) - 1/2 as defined in ExceptionalPoint.lean (def dd).

Run: python3 notes/scripts/peel-isco-nilpotent-checks.py
"""
import numpy as np
import sympy as sp

I = sp.I

# ---------------------------------------------------------------- (1) the peel wall, exactly
c, s = sp.sqrt(2), sp.Integer(1)          # cosh(r/2), sinh(r/2) at the wall r = log(3 + 2 sqrt2)
Bx = sp.Matrix([[c, s], [s, c]])
By = sp.Matrix([[c, -s*I], [s*I, c]])
Bxi = sp.Matrix([[c, -s], [-s, c]])
Byi = sp.Matrix([[c, s*I], [-s*I, c]])
W = sp.simplify(Bx * By * Bxi * Byi)
T = sp.simplify(W + sp.eye(2))
print("peel, at the wall:")
print("  W+1        =", T.tolist())
print("  trace      =", sp.simplify(T.trace()))
print("  det        =", sp.simplify(T.det()))
print("  (W+1)^2    =", sp.simplify(T * T).tolist())
print("  nonzero    =", T != sp.zeros(2, 2), "   complex entries =", any(sp.im(e) != 0 for e in T))
assert sp.simplify(T.trace()) == 0 and sp.simplify(T.det()) == 0
assert sp.simplify(T * T) == sp.zeros(2, 2) and T != sp.zeros(2, 2)

# eigenvector condition number vs delta, six decades on both signs
def Wnumpy(r):
    ch, sh = np.cosh(r/2), np.sinh(r/2)
    return (np.array([[ch, sh], [sh, ch]], complex)
            @ np.array([[ch, -sh*1j], [sh*1j, ch]], complex)
            @ np.array([[ch, -sh], [-sh, ch]], complex)
            @ np.array([[ch, sh*1j], [-sh*1j, ch]], complex))

print("\n  delta        r        kappa      kappa^2*delta   kappa*sqrt|delta|")
for d in [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, -1e-2, -1e-3, -1e-4, -1e-5, -1e-6]:
    r = 2*np.arctanh(np.sqrt(d + 0.5))
    ev, V = np.linalg.eig(Wnumpy(r))
    V = V / np.linalg.norm(V, axis=0)
    k = np.linalg.cond(V)
    print(f"  {d:10.0e} {r:9.6f} {k:11.6f} {k*k*d:15.10f} {k*np.sqrt(abs(d)):17.10f}")
print("  sqrt2 =", np.sqrt(2))

# ---------------------------------------------------------------- (2) the ISCO generator
rr, L2 = sp.symbols('r L2', positive=True)
V = (1 - 2/rr) * (1 + L2/rr**2)                      # bh_isco_10.py, G = c = M = 1
L2c = sp.solve(sp.Eq(sp.diff(V, rr), 0), L2)[0]      # circular orbits: L^2 = r^2/(r-3)
k2 = sp.simplify(sp.diff(V, rr, 2).subs(L2, L2c)/2)  # the script's W = V''/2
A = sp.Matrix([[0, 1], [-k2, 0]])                    # B13's generator, z = -k^2
print("\nISCO:")
print("  L^2 on the circular family =", sp.simplify(L2c))
print("  k^2 = V''/2               =", sp.factor(k2))
print("  A^2 + k^2 I               =", sp.simplify(A*A + k2*sp.eye(2)).tolist())
A6 = A.subs(rr, 6)
print("  at r=6: A =", A6.tolist(), " A^2 =", (A6*A6).tolist(), " nonzero =", A6 != sp.zeros(2, 2))
V3 = sp.diff(V, rr, 3).subs({L2: 12, rr: 6})
slope = sp.diff(k2, rr).subs(rr, 6)
print("  V'''(6) at L^2=12         =", sp.nsimplify(V3))
print("  slope of V''/2 at r=6     =", slope, " (dL^2/dr at 6 =", sp.diff(L2c, rr).subs(rr, 6), ")")
print("  sqrt(2 V'''(6))           =", sp.nsimplify(sp.sqrt(2*V3)), " = sqrt2/18:",
      sp.simplify(sp.sqrt(2*V3) - sp.sqrt(2)/18) == 0)
print("  gap/sqrt(d) -> 2 sqrt(slope) =", sp.simplify(2*sp.sqrt(slope)))
assert sp.simplify(sp.sqrt(2*V3) - sp.sqrt(2)/18) == 0

# ---------------------------------------------------------------- (3) why the symmetric slice is not on the wall
a, b = sp.symbols('a b', real=True)
S = sp.Matrix([[a, b], [b, -a]])
print("\nsymmetric traceless slice: tr(S^2) =", sp.simplify((S*S).trace()),
      " -> vanishes only at a = b = 0, so the null cone of the trace form misses it")
