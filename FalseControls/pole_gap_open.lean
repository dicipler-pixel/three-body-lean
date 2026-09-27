import ThreeBody.Basic
-- The gap closes at the pole: 1 − cos² 0 = 0, not 1.
example : (1 : ℝ) - Real.cos 0 ^ 2 = 1 := by simp
