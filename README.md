<div align="center">

# The Three-Body Problem, Operator-First: A Complete Spectral Anatomy of Relational Transport on the Shape Sphere — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/three-body-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/three-body-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-22-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.20764188-blue)](https://doi.org/10.5281/zenodo.20764188)

Jeromie Beasley

</div>

---

## The idea in one line

The three mutual distances of a planar triangle are a projection of its shape onto three
directions at 120°. The Gram operator of that projection has spectrum `{cos² ϑ, 1}` exactly, so
its two degeneracies are of different species: at syzygy it loses rank while its gap is widest,
and at the equilateral points its gap closes (quadratically, not conically) while it stays
invertible. Lean states the pole limits at `ϑ = 0`.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Eq. (1) | The side coefficients are unit vectors at mutual 120° and sum to zero | `u_unit`, `u_inner`, `sides_sum` |
| Theorem 1 | `dΦ(e_ϑ) = (cos ϑ cos φ, cos ϑ sin φ)`, `dΦ(e_φ) = (−sin φ, cos φ)`; `M = diag(cos² ϑ, 1)`, `det M = cos² ϑ`, `tr M = cos² ϑ + 1` | `dPhi_theta₁`, `dPhi_theta₂`, `dPhi_phi₁`, `dPhi_phi₂`, `gram_eq`, `gram_det_trace` |
| Prop. 3 | At syzygy `λ_min = 0` and the gap `sin² ϑ` reaches its maximum 1 | `gap_eq`, `syzygy_rank_drop` |
| Prop. 4 | At the pole `ϑ = 0`, `det M → 1` while the gap `→ 0` (the pole `ϑ = π` is not stated separately) | `pole_gap_closes` |
| Theorem 5 | The gap closes quadratically at `ϑ = 0`: `gap/ϑ² → 1` | `sin_div_self_tendsto`, `gap_quadratic` |
| Remark 7 | A symmetric 2-tensor commuting with the 120° rotation is a multiple of the identity | `z3_isotropic` |
| Prop. 8 | The fold: `λ_min(π/2 + ε) = sin² ε` and `λ_min/ε² → 1` | `fold_lambda`, `fold_quadratic` |
| Theorem 9 | `A = D_t − g tᵀ` satisfies `Aᵀ B = B A` with `B = diag(t/g)`; for every right eigenvector `R`, `Aᵀ(BR) = μ BR` (that `BR ≠ 0` is not stated) | `reciprocity`, `left_eigenvector` |
| Theorem 10 | The shifted ledger `log(1 + λ_min) + log 2` is `≥ log 2`, with equality exactly at `λ_min = 0` | `ledger_min` |
| Prop. 17 | At a collinear configuration every transverse motion leaves every squared distance stationary | `transverse_stationary` |

The file is [`ThreeBody/Basic.lean`](ThreeBody/Basic.lean). What is not proved is in
[`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*The Three-Body Problem, Operator-First: A Complete Spectral Anatomy of Relational Transport on the Shape Sphere*, Jeromie Beasley. DOI
[10.5281/zenodo.20764188](https://doi.org/10.5281/zenodo.20764188) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
