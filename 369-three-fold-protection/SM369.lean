/- SM369.lean — straw-man checks for the 3-6-9 rule, core Lean 4 (no Mathlib), kernel-checked.
   Authors: DarkWolf (@DarkDireWolf33) · Jeromie Beasley · Grok (xAI) · Claude (Anthropic)
   The 3-6-9 modular construction: DarkWolf. Synthesis: Jeromie Beasley with Grok.
   Audit, rebuild and Lean: Jeromie Beasley with Claude. Created with AI assistance. -/

/-- The residue set {0,3,6} mod 9 is exactly "divisible by 3". -/
theorem mod9_036_iff_dvd3 (l : Nat) : (l % 9 = 0 ∨ l % 9 = 3 ∨ l % 9 = 6) ↔ l % 3 = 0 := by omega

/-- The same for integers (negative winding numbers included). -/
theorem int_mod9_036_iff_dvd3 (l : Int) : (l % 9 = 0 ∨ l % 9 = 3 ∨ l % 9 = 6) ↔ l % 3 = 0 := by omega

/-- {0,3,6} is closed under addition mod 9 (the order-3 subgroup of ℤ/9). -/
theorem class036_add (a b : Nat) (ha : a % 3 = 0) (hb : b % 3 = 0) :
    (a + b) % 9 = 0 ∨ (a + b) % 9 = 3 ∨ (a + b) % 9 = 6 := by omega

/-- The class is closed under multiplication by any integer factor. -/
theorem class036_mul (a k : Nat) (ha : a % 3 = 0) : (k * a) % 3 = 0 := by
  rw [Nat.mul_mod, ha]; simp

theorem mul_not_dvd3 (x y : Nat) (hx : x % 3 ≠ 0) (hy : y % 3 ≠ 0) : (x * y) % 3 ≠ 0 := by
  rw [Nat.mul_mod]
  have h1 : x % 3 < 3 := Nat.mod_lt _ (by decide)
  have h2 : y % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize x % 3 = u at *
  generalize y % 3 = v at *
  match u, v, h1, h2, hx, hy with
  | 1, 1, _, _, _, _ => decide
  | 1, 2, _, _, _, _ => decide
  | 2, 1, _, _, _, _ => decide
  | 2, 2, _, _, _, _ => decide
  | 0, _, _, _, h, _ => exact absurd rfl h
  | _, 0, _, _, _, h => exact absurd rfl h
  | u+3, _, h, _, _, _ => omega
  | _, v+3, _, h, _, _ => omega

theorem pow_not_dvd3 (b a : Nat) (hb : b % 3 ≠ 0) : (b ^ a) % 3 ≠ 0 := by
  induction a with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ]; exact mul_not_dvd3 _ _ ih hb

/-- The synthesis's own "2^a × 5^b factorization filter" can never land in {0,3,6} mod 9. -/
theorem two_five_never_036 (a b : Nat) :
    ¬ ((2 ^ a * 5 ^ b) % 9 = 0 ∨ (2 ^ a * 5 ^ b) % 9 = 3 ∨ (2 ^ a * 5 ^ b) % 9 = 6) := by
  rw [mod9_036_iff_dvd3]
  exact mul_not_dvd3 _ _ (pow_not_dvd3 2 a (by decide)) (pow_not_dvd3 5 b (by decide))

/-- Multiplication by ω = e^{2πi/3} on the Eisenstein lattice ℤ[ω], written in the basis {1, ω}:
    a + bω ↦ ω(a + bω) = −b + (a − b)ω.  It preserves the norm |a + bω|² = a² − ab + b². -/
theorem omega_preserves_norm (a b : Int) :
    (-b) * (-b) - (-b) * (a - b) + (a - b) * (a - b) = a * a - a * b + b * b := by
  simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  rw [Int.mul_comm b a]; omega

/-- ω has order 3: applying it three times returns every lattice point. -/
theorem omega_order3 (a b : Int) :
    let w := fun (p : Int × Int) => ((-p.2), p.1 - p.2)
    w (w (w (a, b))) = (a, b) := by
  simp only [Prod.mk.injEq]; constructor <;> omega

/-- ω fixes no lattice point except the origin, so it splits every nonzero shell into orbits of size exactly 3:
    every shell count of an ℤ[ω]-lattice is divisible by 3, i.e. lies in {0,3,6} mod 9. -/
theorem omega_no_fixed (a b : Int) (h : ((-b), a - b) = (a, b)) : a = 0 ∧ b = 0 := by
  simp only [Prod.mk.injEq] at h; omega

/-- Fox 3-colourings of the trefoil diagram (arcs x y z; at each crossing 2·over = under₁ + under₂ mod 3): exactly 9. -/
def trefoilOK (x y z : Fin 3) : Bool :=
  (2 * x.val) % 3 == (y.val + z.val) % 3 && (2 * y.val) % 3 == (x.val + z.val) % 3 && (2 * z.val) % 3 == (x.val + y.val) % 3
theorem trefoil_nine_colourings :
    ((List.finRange 3).flatMap fun x => (List.finRange 3).flatMap fun y => (List.finRange 3).filter fun z => trefoilOK x y z).length = 9 := by
  decide

/-- Trivalent counting (Mirzakhani's pants): a pants decomposition of a genus-g surface with n boundaries has
    2g−2+n pants and 3g−3+n curves; each pants has 3 cuffs, each curve is shared by 2 pants, each boundary by 1. -/
theorem pants_trivalent (g n : Int) : 3 * (2 * g - 2 + n) = 2 * (3 * g - 3 + n) + n := by omega

/-- So the number of cutting curves is ≡ n (mod 3). -/
theorem pants_curves_mod3 (g n : Int) : (3 * g - 3 + n) % 3 = n % 3 := by omega

/-- The same identity for planar cubic (Tr φ³) trees with n legs: n−2 vertices, n−3 propagators. -/
theorem cubic_tree_trivalent (n : Int) : 3 * (n - 2) = 2 * (n - 3) + n := by omega
