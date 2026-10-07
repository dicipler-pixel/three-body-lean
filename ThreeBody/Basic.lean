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
* Remark 7: a symmetric 2-tensor commuting with the 120° rotation is a multiple of the identity.
* Proposition 8: near syzygy `λ_min = sin² ε` (the fold), with `λ_min/ε² → 1`.
* Theorem 9: `A = D_t − g tᵀ` satisfies `Aᵀ B = B A` for `B = diag(t/g)`, and for every right
  eigenvector `R`, `ℓ = B R` satisfies `Aᵀ ℓ = μ ℓ` (that `ℓ ≠ 0` is not stated).
* Theorem 10 (the exact part): the shifted ledger `log(1+λ_min) + log 2` is at least `log 2`,
  with equality exactly at `λ_min = 0`.
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

/-! ## Remark 7: the 120° symmetry forbids anisotropy -/

/-- Rotation by 120°. -/
noncomputable def rot : Matrix (Fin 2) (Fin 2) ℝ := !![-1 / 2, -(√3 / 2); √3 / 2, -1 / 2]

/-- **Remark 7.** A symmetric 2-tensor commuting with the `ℤ₃` rotation is a multiple of the
identity: no linear anisotropy survives at the equilateral point. -/
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
