# SCRIPT: SM369-BATTERY — straw man to the max for the 3-6-9 rule. Each test prints its KILL CONDITION before its result.
import numpy as np, math, itertools
from scipy.linalg import expm
rng = np.random.default_rng(369)
def head(s, kill): print('\n=== ' + s + '\n    kill condition: ' + kill)

# ---------- T1: angular momentum conserved mod n under n-fold rotational symmetry ----------
head('T1 OAM on a ring, potential with n-fold symmetry: is l conserved mod n?',
     'population leaving the starting class l mod n exceeds 1e-10 (symmetric case) -> rule dead; control must leak when symmetry is broken')
L = np.arange(-27, 28); N = len(L)
def ring_H(n_fold, eps_break=0.0):
    H = np.diag(L**2/2.0).astype(complex)
    for m in range(1, 4):                       # Fourier components at multiples of n_fold only
        amp = rng.normal() + 1j*rng.normal(); q = m*n_fold
        for i, l in enumerate(L):
            j = np.where(L == l + q)[0]
            if len(j): H[j[0], i] += amp; H[i, j[0]] += np.conj(amp)
    if eps_break:                               # a cos(phi) term breaks the symmetry
        for i, l in enumerate(L):
            j = np.where(L == l + 1)[0]
            if len(j): H[j[0], i] += eps_break; H[i, j[0]] += eps_break
    return H
for n_fold, l0, br in [(9, 3, 0), (9, 1, 0), (3, 3, 0), (3, 1, 0), (9, 3, 0.3), (3, 3, 0.3)]:
    H = ring_H(n_fold, br); psi = (L == l0).astype(complex); U = expm(-1j*H*5.0); psi = U @ psi
    cls = (L - l0) % n_fold == 0; leak = float(np.sum(abs(psi[~cls])**2))
    print(f'    {n_fold}-fold, start l={l0:2d}, symmetry broken={br}: population outside l≡{l0%n_fold} (mod {n_fold}) = {leak:.2e}')
# the {0,3,6} mod 9 class = modes unchanged by a 120 degree turn
print('    modes with exp(2πi l/3)=1 among l mod 9:', [r for r in range(9) if abs(np.exp(2j*np.pi*r/3)-1) < 1e-12])

# ---------- T2: is protection special to l in {0,3,6} mod 9? ----------
head('T2 winding of a vortex field under random smooth perturbation, l = 1,2,3,4,6,9',
     'if l=1 or l=2 winding changes under small continuous perturbation while l=3,6,9 hold -> 3-6-9 protection survives; if all hold -> protection is universal, the 3-6-9 restriction dies')
xs = np.linspace(-1, 1, 201); X, Y = np.meshgrid(xs, xs); Z = X + 1j*Y
def winding(field, r=0.8, m=2000):
    th = np.linspace(0, 2*np.pi, m, endpoint=False); px, py = r*np.cos(th), r*np.sin(th)
    ix = np.clip(((px+1)/2*200).round().astype(int), 0, 200); iy = np.clip(((py+1)/2*200).round().astype(int), 0, 200)
    ph = np.unwrap(np.angle(field[iy, ix])); return int(round((ph[-1]-ph[0] + (ph[1]-ph[0]))/(2*np.pi)))
for l in [1, 2, 3, 4, 6, 9]:
    res = []
    for k in range(20):
        pert = sum(rng.normal()*0.25*np.exp(1j*rng.uniform(0, 2*np.pi))*X**a*Y**b for a in range(3) for b in range(3))
        res.append(winding(Z**l*(1 + 0.3*pert) + 0.02*pert))
    print(f'    l={l}: windings after 20 random perturbations = {sorted(set(res))}')

# ---------- T3: what {0,3,6} mod 9 actually is ----------
head('T3 the residue set {0,3,6} mod 9', 'none (identity check)')
print('    l mod 9 in {0,3,6}  <=>  3 | l :', all(((l % 9) in (0, 3, 6)) == (l % 3 == 0) for l in range(-10000, 10000)))
print('    digit sum ≡ n (mod 9) for n<10^5:', all(sum(map(int, str(n))) % 9 == n % 9 for n in range(100000)))

# ---------- T4: Solfeggio numbers and units ----------
head('T4 Solfeggio 528/639/741/852/963 Hz', 'a physical selection rule must survive a change of units; if residues mod 9 change when the unit changes, the residue is not physical')
f = [528, 639, 741, 852, 963]
print('    in Hz: mod 9 =', [x % 9 for x in f], ' all divisible by 3:', all(x % 3 == 0 for x in f), ' step =', f[1]-f[0], '= 3·37')
print('    period in microseconds (1e6/f):', [round(1e6/x, 3) for x in f])
print('    in cycles per 7 seconds:', [7*x for x in f], 'mod 9 =', [7*x % 9 for x in f])
print('    in units of 1/2 Hz:', [2*x for x in f], 'mod 9 =', [2*x % 9 for x in f], ' (divisibility by 3 survives integer rescaling; the residues 3 vs 6 do not)')
print('    musical ratios 639/528 =', round(639/528, 4), ' 741/528 =', round(741/528, 4), ' (equal-tempered minor third 1.1892, major third 1.2599)')

# ---------- T5: lattices with 3-fold symmetry — shell counts mod 3 ----------
head('T5 sphere-packing lattices: shell counts mod 3 and mod 9',
     'claim "every shell count of an Eisenstein (Z[ω]) lattice is ≡ 0 mod 3" dies if any count (n≥1) is not; control: Z^2 and Z^8 (no free 3-fold symmetry) should hit other residues')
def sigma(n, k): return sum(d**k for d in range(1, n+1) if n % d == 0)
E8 = [240*sigma(n, 3) for n in range(1, 41)]
print('    E8 shells (240·σ3(n)), n=1..40: mod 9 residues =', sorted(set(x % 9 for x in E8)), ' first:', E8[:5])
# A2 hexagonal lattice x^2+xy+y^2 = n
A2 = [sum(1 for a in range(-60, 61) for b in range(-60, 61) if a*a+a*b+b*b == n) for n in range(1, 61)]
print('    A2 hexagonal shells n=1..60 (nonzero): mod 9 residues =', sorted(set(x % 9 for x in A2 if x)), ' first:', A2[:7])
Z2 = [sum(1 for a in range(-60, 61) for b in range(-60, 61) if a*a+b*b == n) for n in range(1, 61)]
print('    control Z^2 shells (nonzero): mod 3 residues =', sorted(set(x % 3 for x in Z2 if x)), ' first:', Z2[:5])
# Leech: theta = E12 - (65520/691) Delta
from fractions import Fraction
M = 30
def qexp_E12(M): return [1] + [Fraction(65520, 691)*sigma(n, 11) for n in range(1, M)]
def qexp_Delta(M):
    c = [0]*M; c[0] = 1
    for n in range(1, M):                     # prod (1-q^n)^24
        for _ in range(24):
            for i in range(M-1, n-1, -1): c[i] -= c[i-n]
    return [0] + c[:M-1]
E12, D = qexp_E12(M), qexp_Delta(M)
Leech = [E12[n] - Fraction(65520, 691)*D[n] for n in range(M)]
Lc = [int(x) for x in Leech]; assert all(Fraction(x) == y for x, y in zip(Lc, Leech))
print('    Leech: counts at norm 2,4,6 =', Lc[1:4], ' (expect 0? norm 2 = 0, then 196560, 16773120)')
print('    Leech shells n=1..29 nonzero: mod 9 residues =', sorted(set(x % 9 for x in Lc[1:] if x)))
# control: Z^8
from collections import Counter
r8 = [0]*20
for v in itertools.product(range(-3, 4), repeat=4):
    pass
def rk(n, k):   # number of ways n as sum of k squares (small n)
    from functools import lru_cache
    @lru_cache(None)
    def f(n, k):
        if k == 0: return 1 if n == 0 else 0
        s = 0; a = 0
        while a*a <= n:
            s += f(n-a*a, k-1)*(1 if a == 0 else 2); a += 1
        return s
    return f(n, k)
Z8 = [rk(n, 8) for n in range(1, 21)]
print('    control Z^8 shells n=1..20: mod 3 residues =', sorted(set(x % 3 for x in Z8)), ' first:', Z8[:4])
# the reason: a fixed-point-free order-3 symmetry. E8 Coxeter element w (h=30), w^10 has eigenvalues exp(2πi m/3), m = exponents
expo = [1, 7, 11, 13, 17, 19, 23, 29]
print('    E8 exponents mod 3 =', [m % 3 for m in expo], ' -> w^10 has no eigenvalue 1: fixed-point-free order 3 =', all(m % 3 for m in expo))

# ---------- T6: Apollonian curvatures mod 3 and mod 9 ----------
head('T6 integral Apollonian packing (-1,2,2,3): curvature residues', 'claim "Apollonian curvatures are confined to {0,3,6} mod 9" dies if other residues occur; record what IS restricted (mod 24, mod 3)')
seen = set(); stack = [(-1, 2, 2, 3)]; curv = Counter(); LIM = 20000
while stack:
    q = stack.pop(); key = tuple(sorted(q))
    if key in seen: continue
    seen.add(key)
    for i in range(4):
        r = list(q); r[i] = 2*(sum(q) - q[i]) - q[i]
        if r[i] > max(q) and r[i] <= LIM: curv[r[i]] += 1; stack.append(tuple(r))
cs = sorted(set(list(curv) + [-1, 2, 3]))
print('    distinct curvatures up to', LIM, ':', len(cs))
for m in [3, 9, 24]: print(f'    residues mod {m}:', sorted(set(c % m for c in cs)))

# ---------- T7: Catalan (triangulation) counts mod 2, 3, 5, 9 ----------
head('T7 triangulations of an (n+2)-gon = Catalan C_n (Tr φ³ tree diagrams): residues', 'claim "triangulation counts single out 3" dies if the same density-1 divisibility holds for 2 and 5')
C = [1]
for n in range(1, 3000): C.append(C[-1]*2*(2*n-1)//(n+1))
for m in [2, 3, 5, 9]: print(f'    fraction of C_n ≡ 0 mod {m}, n<3000: {sum(1 for c in C if c % m == 0)/len(C):.3f}')
print('    C_n mod 9 for n=1..20:', [c % 9 for c in C[1:21]])

# ---------- T8: three-body shape sphere carries the triangle group D3 ----------
head('T8 permuting three bodies acts on the shape sphere (Hopf base) as D3', 'dies if the cyclic relabelling is not a 120° rotation about the equilateral (polar) axis')
def shape(r):
    s2 = math.sqrt(2); p1 = (r[1]-r[0])/s2; p2 = math.sqrt(2/3)*(r[2]-(r[0]+r[1])/2)
    N = abs(p1)**2+abs(p2)**2; z = p1*np.conj(p2); return np.array([(abs(p1)**2-abs(p2)**2)/N, 2*z.real/N, 2*z.imag/N])
worst = 0; ang = []
for k in range(200):
    r = rng.normal(size=3) + 1j*rng.normal(size=3); w = shape(r); wc = shape(np.roll(r, 1))
    th = math.atan2(wc[1], wc[0]) - math.atan2(w[1], w[0]); ang.append(round(math.degrees(th) % 360, 6)); worst = max(worst, abs(wc[2]-w[2]))
print('    rotation angle of the cyclic relabelling about the polar axis:', sorted(set(ang))[:3], '…  change in height (signed area):', f'{worst:.1e}')
r = np.array([0, 1, 0.5+1j*math.sqrt(3)/2]); print('    equilateral triangle maps to the pole:', np.round(shape(r), 12))
