# 3-6-9: the three-fold protection rule

**DarkWolf** ([@DarkDireWolf33](https://x.com/DarkDireWolf33)) · **Jeromie Beasley** · **Grok** (xAI) · **Claude** (Anthropic)

The 3-6-9 modular construction is DarkWolf's. Jeromie Beasley worked through the synthesis
conversation with Grok, and the straw-man audit, the rebuild and the Lean with Claude.
Created with AI assistance; the authors directed the work.

## The rule that survived

The residue class `x mod 9 ∈ {0, 3, 6}` is exactly "3 divides x" (`mod9_036_iff_dvd3`). Read as
**a three-fold symmetry with no fixed points**, it does three jobs:

1. **Angular momentum.** In a medium with 3-fold (or 9-fold) rotational symmetry, the modes with
   ℓ ≡ 0, 3, 6 (mod 9) are exactly those left unchanged by a 120° turn, and that sector is closed
   under evolution (computed: leakage 0 with the symmetry, 1.8×10⁻² and 9.2×10⁻² when it is broken).
2. **Lattices.** Every shell count of a lattice with a fixed-point-free 120° symmetry lies in
   {0, 3, 6} mod 9. This holds for the hexagonal lattice A₂, for E₈ and for Leech, where every
   count is ≡ 0 mod 9. The orbit argument is in Lean (`omega_preserves_norm`, `omega_order3`,
   `omega_no_fixed`). Z² and Z⁸ fail.
3. **Knotted filaments.** Knots carry a mod-3 colouring charge that only reconnection changes.
   The trefoil has 9 Fox 3-colourings (`trefoil_nine_colourings`); the Conway knot has only the
   trivial ones.

The same structure appears in the three-body shape sphere, where relabelling the three bodies
turns it by 120° (see `z3_isotropic` in `ThreeBody/Basic.lean`). It also appears in the trivalent
counting shared by pants decompositions and cubic trees (`pants_trivalent`, `cubic_tree_trivalent`).

What did not survive:
- "Only ℓ ∈ {0, 3, 6} is protected" (ℓ = 1, 2, 4 are protected just as well).
- The 2ᵃ·5ᵇ residue tool, which never lands in the class (`two_five_never_036`).
- Solfeggio frequencies as physics.
- "Apollonian curvatures confined to {0, 3, 6}". The (−1, 2, 2, 3) packing never gives a
  curvature ≡ 1 mod 3, which is a different restriction.

## Files

| File | What it is |
| :--- | :--- |
| `SM369.lean` | 14 theorems, core Lean only (no Mathlib), no `sorry`. Checked with Lean 4.24.0 and 4.34.1 |
| `report.html` | The full straw-man report: strongest forms, kill conditions, opposites, rebuild, sources |
| `scripts/` | `battery.py` (tests T1–T8), `knots.py` (Alexander polynomials and Fox colourings from SnapPy PD codes), `colour_angles.py` |
| `outputs/` | The run outputs quoted in the report |

`SM369.lean` sits outside the Mathlib library of this repository and is checked by its own
workflow, `.github/workflows/369.yml`.
