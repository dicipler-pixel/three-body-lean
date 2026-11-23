/-
The Three-Body Problem, Operator-First (Jeromie Beasley, DOI 10.5281/zenodo.20764188):
the exact results.

Shape sphere coordinates `w = (sin ϑ cos φ, sin ϑ sin φ, cos ϑ)`; the relational map is
`Φ(w) = (w₁, w₂)` (Eq. 1), and the object of study is the Gram operator `M = dΦᵀ dΦ` (Eq. 2)
read in the orthonormal frame `{e_ϑ, e_φ}`.

* Eq. (1): the three side coefficients are unit vectors at mutual 120°, summing to zero.
* Theorem 1: `dΦ(e_ϑ) = (cos ϑ cos φ, cos ϑ sin φ)`, `dΦ(e_φ) = (−sin φ, cos φ)` and
  `M = diag(cos² ϑ, 1)`, with no dependence on `φ`.
* Propositions 3 and 4: at syzygy `λ_min = 0` and the gap `sin² ϑ` is maximal; at the pole
  `ϑ = 0` the gap closes while `det M → 1`.
* Theorem 5: the gap closes quadratically at `ϑ = 0`, `gap/ϑ² → 1`.
* Remark 7: a symmetric 2-tensor commuting with the 120° rotation is a multiple of the identity
  (pointwise; it says nothing about the first-order term of a family). `commute_iff_invariant`
  turns the paper's invariant tensor into that hypothesis, and `gram_even` records that the
  operator is even at the pole, which is what makes the closing quadratic.
* Remark 7, the counterexample side: `Q` is a `D₃`-invariant family, positive definite near the
  pole, with a linear gap (`Q_gap_linear`) and an eigenline that returns negated after one circuit
  (`evec_flip`); with the norm fixed the flip is forced (`evec_monodromy`). So the quadratic closing
  is a property of `gram`, not of the symmetry.
* Proposition 8: near syzygy `λ_min = sin² ε` (the fold), with `λ_min/ε² → 1`.
* Theorem 9: with `g ≠ 0` pointwise, `A = D_t − g tᵀ` satisfies `Aᵀ B = B A` for `B = diag(t/g)`,
  and for every right eigenvector `R`, `ℓ = B R` satisfies `Aᵀ ℓ = μ ℓ` (that `ℓ ≠ 0` is not
  stated).
* Theorem 10 (the exact part): for `λ_min ≥ 0`, the shifted ledger `log(1+λ_min) + log 2` is at
  least `log 2`, with equality exactly at `λ_min = 0`.
* Proposition 17 (the key step): at a collinear configuration every transverse motion leaves every
  squared distance stationary.
-/
import Mathlib

namespace ThreeBody

open Real Filter Topology Matrix

/-! ## Eq. (1): three directions at 120° -/

/-- The three side-coefficient vectors of Eq. (1). -/
noncomputable def u : Fin 3 → ℝ × ℝ :=
  ![(1, 0), (-1 / 2, √3 / 2), (-1 / 2, -(√3 / 2))]

theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Each coefficient vector is a unit vector. -/
theorem u_unit (k : Fin 3) : (u k).1 ^ 2 + (u k).2 ^ 2 = 1 := by
  fin_cases k <;> simp [u] <;> nlinarith [sqrt3_sq]

/-- Distinct coefficient vectors meet at 120°: their inner product is `−1/2`. -/
theorem u_inner (j k : Fin 3) (h : j ≠ k) : (u j).1 * (u k).1 + (u j).2 * (u k).2 = -1 / 2 := by
  fin_cases j <;> fin_cases k <;> simp [u] at h ⊢ <;> nlinarith [sqrt3_sq]

/-- The three coefficient vectors sum to zero, so the normalised squared distances sum to 3. -/
theorem sides_sum (w₁ w₂ : ℝ) :
    (1 + w₁) + (1 - 1 / 2 * w₁ + √3 / 2 * w₂) + (1 - 1 / 2 * w₁ - √3 / 2 * w₂) = 3 := by
  ring

/-! ## Theorem 1: the exact spectrum of the Gram operator -/

/-- `∂_ϑ` of the first component of `Φ` on the sphere. -/
theorem dPhi_theta₁ (ϑ φ : ℝ) :
    HasDerivAt (fun x => sin x * cos φ) (cos ϑ * cos φ) ϑ :=
  (hasDerivAt_sin ϑ).mul_const _

/-- `∂_ϑ` of the second component of `Φ` on the sphere. -/
theorem dPhi_theta₂ (ϑ φ : ℝ) :
    HasDerivAt (fun x => sin x * sin φ) (cos ϑ * sin φ) ϑ :=
  (hasDerivAt_sin ϑ).mul_const _

/-- `∂_φ` of the first component is `sin ϑ · (−sin φ)`: dividing by the frame length `sin ϑ`
gives `dΦ(e_φ)₁ = −sin φ`. -/
theorem dPhi_phi₁ (ϑ φ : ℝ) :
    HasDerivAt (fun y => sin ϑ * cos y) (sin ϑ * -sin φ) φ :=
  (hasDerivAt_cos φ).const_mul _

/-- `∂_φ` of the second component is `sin ϑ · cos φ`. -/
theorem dPhi_phi₂ (ϑ φ : ℝ) :
    HasDerivAt (fun y => sin ϑ * sin y) (sin ϑ * cos φ) φ :=
  (hasDerivAt_sin φ).const_mul _

/-- The Gram matrix of `dΦ` in the frame `{e_ϑ, e_φ}`. -/
noncomputable def gram (ϑ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(cos ϑ * cos φ) ^ 2 + (cos ϑ * sin φ) ^ 2,
      (cos ϑ * cos φ) * -sin φ + (cos ϑ * sin φ) * cos φ;
     -sin φ * (cos ϑ * cos φ) + cos φ * (cos ϑ * sin φ),
      (-sin φ) ^ 2 + cos φ ^ 2]

/-- **Theorem 1.** `M = diag(cos² ϑ, 1)`, with no dependence on `φ`. -/
theorem gram_eq (ϑ φ : ℝ) : gram ϑ φ = !![cos ϑ ^ 2, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram] <;>
    first
    | linear_combination cos ϑ ^ 2 * sin_sq_add_cos_sq φ
    | linear_combination sin_sq_add_cos_sq φ
    | ring

/-- **Theorem 1, spectrum.** `det M = cos² ϑ` and `tr M = cos² ϑ + 1`. -/
theorem gram_det_trace (ϑ φ : ℝ) :
    (gram ϑ φ).det = cos ϑ ^ 2 ∧ (gram ϑ φ).trace = cos ϑ ^ 2 + 1 := by
  rw [gram_eq]
  refine ⟨by simp [det_fin_two], by simp [trace, Fin.sum_univ_two]⟩

/-- **Remark 7, the part that is about `M`.** The Gram operator is even at the pole: the antipode
`(π - ϑ, φ + π)` carries the same operator, `M(-w) = M(w)`. So `M` depends on the shape only
through the unoriented tangent plane, the term linear in the distance from the pole vanishes, and
the quadratic term is the anisotropy of `gram_eq`. -/
theorem gram_even (ϑ φ : ℝ) : gram ϑ φ = gram (π - ϑ) (φ + π) := by
  rw [gram_eq, gram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cos_pi_sub] <;> ring

/-! ## Propositions 3 and 4, Theorem 5: two degeneracies of different species -/

/-- The spectral gap `1 − cos² ϑ` equals `sin² ϑ`. -/
theorem gap_eq (ϑ : ℝ) : 1 - cos ϑ ^ 2 = sin ϑ ^ 2 := by
  linear_combination -(sin_sq_add_cos_sq ϑ)

/-- **Proposition 3.** At syzygy `λ_min = 0` and the gap equals 1, its maximum. -/
theorem syzygy_rank_drop :
    cos (π / 2) ^ 2 = 0 ∧ 1 - cos (π / 2) ^ 2 = 1 ∧ ∀ ϑ, 1 - cos ϑ ^ 2 ≤ 1 := by
  refine ⟨by simp, by simp, fun ϑ => by nlinarith [sq_nonneg (cos ϑ)]⟩

/-- **Proposition 4.** At the pole `ϑ = 0` the gap closes while `det M → 1`. -/
theorem pole_gap_closes :
    Tendsto (fun ϑ => cos ϑ ^ 2) (𝓝 0) (𝓝 1) ∧
      Tendsto (fun ϑ => 1 - cos ϑ ^ 2) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun ϑ => cos ϑ ^ 2) (𝓝 0) (𝓝 (cos 0 ^ 2)) :=
    ((continuous_cos.pow 2).tendsto 0)
  rw [cos_zero, one_pow] at h
  refine ⟨h, ?_⟩
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- `sin x / x → 1` as `x → 0`, from the derivative of `sin` at 0. -/
theorem sin_div_self_tendsto : Tendsto (fun x => sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_sin (0 : ℝ))
  rw [cos_zero] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp [slope_def_field]

/-- **Theorem 5.** The gap closes quadratically at a pole: `gap/ϑ² → 1`. -/
theorem gap_quadratic : Tendsto (fun ϑ => (1 - cos ϑ ^ 2) / ϑ ^ 2) (𝓝[≠] 0) (𝓝 1) := by
  have h := sin_div_self_tendsto.pow 2
  rw [one_pow] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [gap_eq, div_pow]

/-! ## Remark 7: at the fixed point the invariant 2-tensor is scalar -/

/-- Rotation by 120°. -/
noncomputable def rot : Matrix (Fin 2) (Fin 2) ℝ := !![-1 / 2, -(√3 / 2); √3 / 2, -1 / 2]

/-- **Remark 7.** A symmetric 2-tensor commuting with the `ℤ₃` rotation is a multiple of the
identity. Pointwise only: this constrains the tensor *at* the fixed point and says nothing about
the first-order term of a family. The quadratic closing (`gap_quadratic`, from `gap_eq`) is therefore a fact about this
particular `M`, not a consequence of the `ℤ₃` symmetry. -/
theorem z3_isotropic (a b d : ℝ) (h : rot * !![a, b; b, d] = !![a, b; b, d] * rot) :
    b = 0 ∧ a = d := by
  have hs : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [rot, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  have hb : b * √3 = 0 := by linarith
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact absurd h hs.ne'
  refine ⟨hb0, ?_⟩
  subst hb0
  have had : (a - d) * √3 = 0 := by linarith
  rcases mul_eq_zero.mp had with h | h
  · linarith
  · exact absurd h hs.ne'

/-- The scalar-multiple form of `z3_isotropic`: the tensor is `a • 1`. -/
theorem z3_isotropic_multiple (a b d : ℝ)
    (h : rot * !![a, b; b, d] = !![a, b; b, d] * rot) :
    ∃ c : ℝ, !![a, b; b, d] = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rcases z3_isotropic a b d h with ⟨hb, had⟩
  refine ⟨a, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, had]

/-- `rot` is orthogonal: it is a rotation, not a reflection. -/
theorem rot_orthogonal : rotᵀ * rot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [sqrt3_sq]

/-- The other orthogonality identity for `rot`. -/
theorem rot_orthogonal_right : rot * rotᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [sqrt3_sq]

/-- **The paper's word for the hypothesis.** A symmetric 2-tensor is invariant under the
relabelling, `rotᵀ M rot = M`, exactly when it commutes with it. The bridge is orthogonality of
`rot`; without it the two notions differ (a non-orthogonal order-three example is in the audit
notes). -/
theorem commute_iff_invariant (M : Matrix (Fin 2) (Fin 2) ℝ) :
    rot * M = M * rot ↔ rotᵀ * M * rot = M := by
  constructor
  · intro h
    calc rotᵀ * M * rot = rotᵀ * (M * rot) := Matrix.mul_assoc _ _ _
      _ = rotᵀ * (rot * M) := by rw [h]
      _ = (rotᵀ * rot) * M := (Matrix.mul_assoc _ _ _).symm
      _ = M := by rw [rot_orthogonal, Matrix.one_mul]
  · intro h
    calc rot * M = rot * (rotᵀ * M * rot) := by rw [h]
      _ = (rot * rotᵀ) * (M * rot) := by simp only [Matrix.mul_assoc]
      _ = M * rot := by rw [rot_orthogonal_right, Matrix.one_mul]

/-- **Remark 7, in the form the claim is stated.** An invariant symmetric 2-tensor is a multiple
of the identity — with the invariance written as the paper writes it. -/
theorem invariant_isotropic (a b d : ℝ)
    (h : rotᵀ * !![a, b; b, d] * rot = !![a, b; b, d]) :
    ∃ c : ℝ, !![a, b; b, d] = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine z3_isotropic_multiple a b d ((commute_iff_invariant _).mpr h)

/-! ## Remark 7 is pointwise: an equivariant family with a conical point

The statement above is pointwise, and this section records what it cannot be upgraded to. `Q` is
symmetric, positive definite near the pole, invariant under the full `D₃` stabiliser (`rot` and the
reflection `S`), and its eigenvalues are `1 ± √(x² + y²)/2`: the gap is linear, and the eigenline
has monodromy `−1`. So the quadratic closing of `gap_eq` is a fact about `gram`, not a consequence
of the `ℤ₃` symmetry.

The monodromy is not a matter of choosing a convenient field. Once the norm is fixed, the flip is
forced: a continuous unit eigenvector field for the larger eigenvalue must return negated
(`evec_monodromy`). Without the unit-norm hypothesis the claim is false, since any nonvanishing
scalar multiple of `evec` is again an eigenvector field. -/

/-- A symmetric `2 × 2` real matrix with positive trace and positive determinant is positive
definite. The proof is division-free: with `a = M 0 0`, `b = M 0 1`, `d = M 1 1`,
`a (vᵀ M v) = (a v₀ + b v₁)² + (a d − b²) v₁²`, and `a > 0` follows from trace and determinant. -/
theorem posDef_of_trace_det {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : Mᵀ = M)
    (htr : 0 < M.trace) (hdet : 0 < M.det) :
    ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < v 0 * (M *ᵥ v) 0 + v 1 * (M *ᵥ v) 1 := by
  intro v hv
  have htel : M 1 0 = M 0 1 := by
    have h := congrFun (congrFun hM 1) 0
    simpa [Matrix.transpose_apply] using h.symm
  have htr' : 0 < M 0 0 + M 1 1 := by
    have := htr
    simpa [Matrix.trace, Fin.sum_univ_two] using this
  have hdet' : 0 < M 0 0 * M 1 1 - M 0 1 * M 0 1 := by
    have := hdet
    rw [Matrix.det_fin_two, htel] at this
    exact this
  have ha : 0 < M 0 0 := by nlinarith
  have h0 : (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (M *ᵥ v) 1 = M 0 1 * v 0 + M 1 1 * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, htel]
  rw [h0, h1]
  have key : M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1))
      = (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 0 1) * v 1 ^ 2 := by
    ring
  have hpos : 0 < M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) := by
    rw [key]
    rcases eq_or_ne (v 1) 0 with hv1 | hv1
    · rw [hv1]
      have hv0 : v 0 ≠ 0 := by
        intro h; apply hv; funext i; fin_cases i <;> simp [h, hv1]
      have hne : M 0 0 * v 0 ≠ 0 := mul_ne_zero (ne_of_gt ha) hv0
      have hsq : 0 < (M 0 0 * v 0) * (M 0 0 * v 0) := mul_self_pos.mpr hne
      simpa [pow_two] using hsq
    · have : 0 < (M 0 0 * M 1 1 - M 0 1 * M 0 1) * v 1 ^ 2 := by
        have hvv : 0 < v 1 ^ 2 := by positivity
        exact mul_pos hdet' hvv
      nlinarith [sq_nonneg (M 0 0 * v 0 + M 0 1 * v 1)]
  nlinarith [ha, hpos]

/-- The counterexample family `Q(x,y) = [[1 + x/2, −y/2], [−y/2, 1 − x/2]]`. -/
noncomputable def Q (p : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + p 0 / 2, -(p 1 / 2); -(p 1 / 2), 1 - p 0 / 2]

/-- The reflection `diag(1, −1)`; with `rot` it generates the full `D₃` stabiliser of the pole. -/
noncomputable def S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem sqrt3_cube : (√3 : ℝ) ^ 3 = 3 * √3 := by
  have h : (√3 : ℝ) ^ 3 = √3 ^ 2 * √3 := by ring
  rw [h, sqrt3_sq]

theorem Q_symm (p : Fin 2 → ℝ) : (Q p)ᵀ = Q p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q]

theorem Q_trace (p : Fin 2 → ℝ) : (Q p).trace = 2 := by
  simp [Q, Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem Q_det (p : Fin 2 → ℝ) : (Q p).det = 1 - (p 0 ^ 2 + p 1 ^ 2) / 4 := by
  simp [Q, Matrix.det_fin_two]
  ring

/-- `Q` is invariant under the relabelling rotation. -/
theorem Q_equivariant (p : Fin 2 → ℝ) : Q (rot *ᵥ p) = rot * Q p * rotᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, rot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;>
    ring_nf <;> simp [sqrt3_sq, sqrt3_cube] <;> ring

/-- `Q` is invariant under the reflection too, so under all of `D₃`. -/
theorem Q_reflection (p : Fin 2 → ℝ) : Q (S *ᵥ p) = S * Q p * Sᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Q, S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;> ring

/-- The gap is `√(x² + y²)`, not its square: trace `2` and determinant `1 − r²/4`. -/
theorem Q_gap_linear (p : Fin 2 → ℝ) :
    (Q p).trace ^ 2 - 4 * (Q p).det = p 0 ^ 2 + p 1 ^ 2 := by
  rw [Q_trace, Q_det]
  ring

/-- **`Q` is positive definite inside the disc `x² + y² < 4`.** -/
theorem Q_posDef (p v : Fin 2 → ℝ) (hr : p 0 ^ 2 + p 1 ^ 2 < 4) (hv : v ≠ 0) :
    0 < v 0 * (Q p *ᵥ v) 0 + v 1 * (Q p *ᵥ v) 1 := by
  refine posDef_of_trace_det (Q_symm p) ?_ ?_ v hv
  · rw [Q_trace]; norm_num
  · rw [Q_det]; nlinarith

/-- The continuous unit eigenvector field of `Q` on the circle: `v(φ) = (cos φ/2, −sin φ/2)`. -/
noncomputable def evec (φ : ℝ) : Fin 2 → ℝ := ![cos (φ / 2), -sin (φ / 2)]

theorem evec_unit (φ : ℝ) : evec φ 0 * evec φ 0 + evec φ 1 * evec φ 1 = 1 := by
  simp [evec]
  nlinarith [sin_sq_add_cos_sq (φ / 2)]

/-- **One full circuit returns the vector negated**: the `−1` eigenline monodromy. -/
theorem evec_flip (φ : ℝ) : evec (φ + 2 * π) = -evec φ := by
  have h1 : (φ + 2 * π) / 2 = φ / 2 + π := by ring
  ext i
  fin_cases i <;>
    simp [evec, h1, Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi] <;> ring

/-- A half circuit puts the field on the orthogonal line. -/
theorem evec_half_orthogonal (φ : ℝ) :
    evec φ 0 * evec (φ + π) 0 + evec φ 1 * evec (φ + π) 1 = 0 := by
  have h1 : (φ + π) / 2 = φ / 2 + π / 2 := by ring
  simp [evec, h1, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- `v(φ)` is an eigenvector of `Q` at `φ`, for the larger eigenvalue `1 + r/2`. -/
theorem Q_eigen (r φ : ℝ) :
    Q ![r * cos φ, r * sin φ] *ᵥ evec φ = (1 + r / 2) • evec φ := by
  have hc : cos φ * cos (φ / 2) + sin φ * sin (φ / 2) = cos (φ / 2) := by
    rw [← Real.cos_sub]; ring_nf
  have hs : sin φ * cos (φ / 2) - cos φ * sin (φ / 2) = sin (φ / 2) := by
    rw [← Real.sin_sub]; ring_nf
  have hc2 : (r / 2) * (cos φ * cos (φ / 2) + sin φ * sin (φ / 2)) = (r / 2) * cos (φ / 2) := by
    rw [hc]
  have hs2 : (r / 2) * (sin φ * cos (φ / 2) - cos φ * sin (φ / 2)) = (r / 2) * sin (φ / 2) := by
    rw [hs]
  ext i
  fin_cases i <;>
    simp [Q, evec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hc2, hs2]

/-- At the same `φ`, `v(φ + π)` is an eigenvector for the smaller eigenvalue `1 − r/2`: half a
circuit swaps the two eigenlines. -/
theorem Q_eigen_minus (r φ : ℝ) :
    Q ![r * cos φ, r * sin φ] *ᵥ evec (φ + π) = (1 - r / 2) • evec (φ + π) := by
  have hc : cos (φ / 2 + π / 2) = -sin (φ / 2) := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hs : sin (φ / 2 + π / 2) = cos (φ / 2) := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h1 : (φ + π) / 2 = φ / 2 + π / 2 := by ring
  have hsp : (r / 2) * (sin φ * cos (φ / 2) - cos φ * sin (φ / 2)) = (r / 2) * sin (φ / 2) := by
    rw [← Real.sin_sub]; ring_nf
  have hcp : (r / 2) * (sin φ * sin (φ / 2) + cos φ * cos (φ / 2)) = (r / 2) * cos (φ / 2) := by
    have hmain : sin φ * sin (φ / 2) + cos φ * cos (φ / 2) = cos (φ / 2) := by
      rw [add_comm, ← Real.cos_sub]; ring_nf
    rw [hmain]
  ext i
  fin_cases i <;>
    simp [Q, evec, h1, hc, hs, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hsp, hcp]

/-- `Q` is symmetric as a bilinear form: the dot product can be moved across it. -/
theorem Q_dot_comm (p u v : Fin 2 → ℝ) :
    dotProduct (Q p *ᵥ u) v = dotProduct u (Q p *ᵥ v) := by
  have h10 : Q p 1 0 = Q p 0 1 := by
    have h := congrFun (congrFun (Q_symm p) 1) 0
    simpa [Matrix.transpose_apply] using h.symm
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, h10]
  ring

/-- A unit eigenvector for the larger eigenvalue is orthogonal to the smaller eigenline. -/
theorem Q_eigen_orth (r φ : ℝ) (hr : 0 < r) (v : Fin 2 → ℝ)
    (heig : Q ![r * cos φ, r * sin φ] *ᵥ v = (1 + r / 2) • v) :
    dotProduct v (evec (φ + π)) = 0 := by
  have h1 : dotProduct (Q ![r * cos φ, r * sin φ] *ᵥ v) (evec (φ + π))
      = (1 + r / 2) * dotProduct v (evec (φ + π)) := by
    rw [heig]
    simp [dotProduct, Fin.sum_univ_two]
    ring
  have h2 : dotProduct v (Q ![r * cos φ, r * sin φ] *ᵥ evec (φ + π))
      = (1 - r / 2) * dotProduct v (evec (φ + π)) := by
    rw [Q_eigen_minus r φ]
    simp [dotProduct, Fin.sum_univ_two]
    ring
  have h3 := Q_dot_comm ![r * cos φ, r * sin φ] v (evec (φ + π))
  have hD : r * dotProduct v (evec (φ + π)) = 0 := by
    rw [h1, h2] at h3
    linarith
  exact (mul_eq_zero.mp hD).resolve_left (ne_of_gt hr)

/-- The sign of `w φ` relative to the eigenline `evec φ`. -/
noncomputable def esign (w : ℝ → Fin 2 → ℝ) (φ : ℝ) : ℝ :=
  w φ 0 * cos (φ / 2) - w φ 1 * sin (φ / 2)

/-- A unit eigenvector for the larger eigenvalue is `± evec φ`. -/
theorem Q_unit_eigen (r φ : ℝ) (hr : 0 < r) (v : Fin 2 → ℝ)
    (hunit : v 0 * v 0 + v 1 * v 1 = 1)
    (heig : Q ![r * cos φ, r * sin φ] *ᵥ v = (1 + r / 2) • v) :
    v = evec φ ∨ v = -evec φ := by
  have hD := Q_eigen_orth r φ hr v heig
  have hhalf : (φ + π) / 2 = φ / 2 + π / 2 := by ring
  have hcos : cos ((φ + π) / 2) = -sin (φ / 2) := by
    rw [hhalf, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsin : sin ((φ + π) / 2) = cos (φ / 2) := by
    rw [hhalf, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  simp [evec, hcos, hsin, dotProduct, Fin.sum_univ_two] at hD
  set u := cos (φ / 2) with hu
  set t := sin (φ / 2) with ht
  have hu2t2 : u ^ 2 + t ^ 2 = 1 := by
    rw [hu, ht]; nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
  have hS : t * v 0 + u * v 1 = 0 := by linarith
  have hSt : t * (t * v 0 + u * v 1) = 0 := by rw [hS]; ring
  have hSu : u * (t * v 0 + u * v 1) = 0 := by rw [hS]; ring
  set c := v 0 * u - v 1 * t with hc
  have hv0 : v 0 = c * u := by
    rw [hc]
    linear_combination hSt - (v 0) * hu2t2
  have hv1 : v 1 = -c * t := by
    rw [hc]
    linear_combination hSu - (v 1) * hu2t2
  have hc2 : c ^ 2 = 1 := by nlinarith [hv0, hv1, hunit, hu2t2]
  rcases sq_eq_one_iff.mp hc2 with h1 | h1
  · left
    ext i
    fin_cases i <;> simp [evec, hu, ht, hv0, hv1, h1]
  · right
    ext i
    fin_cases i <;> simp [evec, hu, ht, hv0, hv1, h1]

/-- **The unit-norm form of the monodromy.** A continuous unit eigenvector field for the larger
eigenvalue, followed once around the circle, comes back negated: once the norm is fixed there is no
continuous choice that avoids the flip. (Without the unit-norm hypothesis the statement is false —
a variable scalar multiple of `evec` is still an eigenvector field.) -/
theorem evec_monodromy (r : ℝ) (hr : 0 < r) (w : ℝ → Fin 2 → ℝ) (hw : Continuous w)
    (hunit : ∀ φ, w φ 0 * w φ 0 + w φ 1 * w φ 1 = 1)
    (heig : ∀ φ, Q ![r * cos φ, r * sin φ] *ᵥ w φ = (1 + r / 2) • w φ) :
    ∀ φ, w (φ + 2 * π) = -w φ := by
  have hpm : ∀ φ, (w φ = evec φ ∧ esign w φ = 1) ∨ (w φ = -evec φ ∧ esign w φ = -1) := by
    intro φ
    rcases Q_unit_eigen r φ hr (w φ) (hunit φ) (heig φ) with h | h
    · left
      refine ⟨h, ?_⟩
      simp only [esign]
      rw [h]
      simp [evec]
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
    · right
      refine ⟨h, ?_⟩
      simp only [esign]
      rw [h]
      simp [evec]
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
  have hcont : Continuous fun φ : ℝ => esign w φ := by
    have h0 : Continuous fun φ : ℝ => w φ 0 := (continuous_apply 0).comp hw
    have h1 : Continuous fun φ : ℝ => w φ 1 := (continuous_apply 1).comp hw
    have hc : Continuous fun φ : ℝ => cos (φ / 2) :=
      Real.continuous_cos.comp (continuous_id.div_const 2)
    have hs : Continuous fun φ : ℝ => sin (φ / 2) :=
      Real.continuous_sin.comp (continuous_id.div_const 2)
    exact (h0.mul hc).sub (h1.mul hs)
  have hval : ∀ φ, esign w φ = 1 ∨ esign w φ = -1 := by
    intro φ
    rcases hpm φ with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hconst : ∀ a b, esign w a = esign w b := by
    have key : ∀ a b, esign w a ≤ 0 → 0 ≤ esign w b → False := by
      intro a b ha hb
      obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge (c := (0 : ℝ))
        (f := fun φ : ℝ => esign w φ) hcont ⟨a, ha⟩ ⟨b, hb⟩
      have hx' : esign w x = 0 := by simpa using hx
      rcases hval x with hx1 | hx1 <;> rw [hx1] at hx' <;> norm_num at hx'
    intro a b
    rcases hval a with ha | ha <;> rcases hval b with hb | hb
    · rw [ha, hb]
    · exfalso; exact key b a (by rw [hb]; norm_num) (by rw [ha]; norm_num)
    · exfalso; exact key a b (by rw [ha]; norm_num) (by rw [hb]; norm_num)
    · rw [ha, hb]
  have hw_eq : ∀ ψ, w ψ = esign w ψ • evec ψ := by
    intro ψ
    rcases hpm ψ with ⟨h, hs⟩ | ⟨h, hs⟩
    · rw [h, hs, one_smul]
    · rw [h, hs]
      simp
  intro φ
  calc w (φ + 2 * π) = esign w (φ + 2 * π) • evec (φ + 2 * π) := hw_eq _
    _ = esign w φ • (-evec φ) := by rw [hconst (φ + 2 * π) φ, evec_flip]
    _ = -(esign w φ • evec φ) := by rw [smul_neg]
    _ = -w φ := by rw [hw_eq]

/-! ## Proposition 8: the fold -/

/-- **Proposition 8.** At `ϑ = π/2 + ε`, `λ_min = sin² ε`. -/
theorem fold_lambda (ε : ℝ) : cos (π / 2 + ε) ^ 2 = sin ε ^ 2 := by
  rw [cos_add, cos_pi_div_two, sin_pi_div_two]
  ring

/-- **Proposition 8, simple zero.** `λ_min/ε² → 1` at the fold; the paper reads this as
`R = λ_min⁻² ∼ ε⁻⁴`. -/
theorem fold_quadratic :
    Tendsto (fun ε => cos (π / 2 + ε) ^ 2 / ε ^ 2) (𝓝[≠] 0) (𝓝 1) := by
  have h := sin_div_self_tendsto.pow 2
  rw [one_pow] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [fold_lambda, div_pow]

/-! ## Theorem 9: reciprocity of the transport operator -/

section Reciprocity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The transport operator `A = D_t − g tᵀ`. -/
def transport (t g : n → ℝ) : Matrix n n ℝ := diagonal t - of fun i j => g i * t j

/-- The pairing `B = diag(t/g)`. -/
noncomputable def pairing (t g : n → ℝ) : Matrix n n ℝ := diagonal fun i => t i / g i

/-- **Theorem 9.** `A` is symmetric for the pairing `B`: `Aᵀ B = B A`. -/
theorem reciprocity (t g : n → ℝ) (hg : ∀ i, g i ≠ 0) :
    (transport t g)ᵀ * pairing t g = pairing t g * transport t g := by
  ext i j
  rw [pairing, mul_diagonal, diagonal_mul]
  simp only [transport, transpose_apply, Matrix.sub_apply, Matrix.of_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    ring
  · have hji : j ≠ i := Ne.symm hij
    rw [if_neg hji, if_neg hij, div_eq_mul_inv, div_eq_mul_inv]
    calc (0 - g j * t i) * (t j * (g j)⁻¹) = -(t i * t j) * (g j * (g j)⁻¹) := by ring
      _ = -(t i * t j) * (g i * (g i)⁻¹) := by
        rw [mul_inv_cancel₀ (hg j), mul_inv_cancel₀ (hg i)]
      _ = t i * (g i)⁻¹ * (0 - g i * t j) := by ring

/-- **Theorem 9, left eigenvectors.** If `A R = λ R` then `ℓ = B R` satisfies `Aᵀ ℓ = λ ℓ`. -/
theorem left_eigenvector (t g : n → ℝ) (hg : ∀ i, g i ≠ 0) (R : n → ℝ) (μ : ℝ)
    (hR : transport t g *ᵥ R = μ • R) :
    (transport t g)ᵀ *ᵥ (pairing t g *ᵥ R) = μ • (pairing t g *ᵥ R) := by
  rw [mulVec_mulVec, reciprocity t g hg, ← mulVec_mulVec, hR, mulVec_smul]

end Reciprocity

/-! ## Theorem 10: the shifted ledger -/

/-- The shifted trace-log of the spectrum `{λ, 1}` with shift `η = 1`. -/
noncomputable def ledger (lam : ℝ) : ℝ := log (1 + lam) + log (1 + 1)

/-- **Theorem 10, exact part.** For `λ_min ≥ 0` the shifted ledger is finite and at least
`log 2`, with equality exactly at the syzygy `λ_min = 0`. -/
theorem ledger_min (lam : ℝ) (h : 0 ≤ lam) :
    log 2 ≤ ledger lam ∧ (ledger lam = log 2 ↔ lam = 0) := by
  have h1 : 0 ≤ log (1 + lam) := log_nonneg (by linarith)
  have h2 : log (1 + 1 : ℝ) = log 2 := by norm_num
  unfold ledger
  rw [h2]
  refine ⟨by linarith, fun hz => ?_, fun hz => by simp [hz]⟩
  have h0 : log (1 + lam) = 0 := by linarith
  rcases log_eq_zero.mp h0 with h' | h' | h' <;> linarith

/-! ## Proposition 17: transverse motions at a collinear configuration -/

/-- **Proposition 17, key step.** At a collinear configuration (all `y = 0`), moving the bodies
transversely by `τ v` leaves every squared distance stationary: `∂_τ r²_ij = 0` at `τ = 0`. -/
theorem transverse_stationary {N : ℕ} (x v : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun τ : ℝ => (x i - x j) ^ 2 + (τ * v i - τ * v j) ^ 2) 0 0 := by
  have h := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul ((v i - v j) ^ 2)).const_add ((x i - x j) ^ 2)
  convert h using 1
  · funext τ
    ring
  · simp

end ThreeBody
