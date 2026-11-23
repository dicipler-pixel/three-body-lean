import ThreeBody.Basic
-- The monodromy claim needs the unit-norm hypothesis. Without it the statement is FALSE, and that
-- is what this control guards.
--
-- At r = 1 the field w φ = (2 + sin (φ/2)) • evec φ is continuous and nowhere zero, and it is an
-- eigenvector field for the larger eigenvalue 1 + r/2 at every φ: scalar multiples of an
-- eigenvector are eigenvectors, so a nonvanishing field may carry any positive magnitude. It does
-- not return negated, though: w (3π) = (0, 1) while −w π = (0, 3).
--
-- The repository therefore proves the normalised statement only (evec_monodromy, which carries
-- hunit : ∀ φ, w φ 0 * w φ 0 + w φ 1 * w φ 1 = 1). The two examples below state the un-normalised
-- version and the concrete instance that refutes it; both must be rejected.
example (r : ℝ) (hr : 0 < r) (w : ℝ → Fin 2 → ℝ) (hw : Continuous w)
    (hne : ∀ φ, w φ ≠ 0)
    (heig : ∀ φ, Matrix.mulVec (ThreeBody.Q ![r * Real.cos φ, r * Real.sin φ]) (w φ)
      = (1 + r / 2) • w φ) :
    ∀ φ, w (φ + 2 * Real.pi) = -w φ := by
  intro φ

-- The refutation in numbers: at φ = π the field above satisfies w (3π) = (0, 1) but
-- −w π = (0, 3).
example : (2 + Real.sin (3 * Real.pi / 2)) • ThreeBody.evec (3 * Real.pi)
    = -((2 + Real.sin (Real.pi / 2)) • ThreeBody.evec Real.pi) := by
  simp [ThreeBody.evec]
