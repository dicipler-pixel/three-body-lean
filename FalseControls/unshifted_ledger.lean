import ThreeBody.Basic
-- At syzygy the shifted ledger is log 2, not 0.
example : ThreeBody.ledger 0 = 0 := by simp [ThreeBody.ledger]; norm_num
