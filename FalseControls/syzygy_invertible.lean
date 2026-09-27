import ThreeBody.Basic
-- The Gram operator is not invertible at syzygy: λ_min = cos²(π/2) = 0, not 1.
example : Real.cos (Real.pi / 2) ^ 2 = 1 := by simp
