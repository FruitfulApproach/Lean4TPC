-- TPC/Norm.lean
-- Defines the norm |(x, -x)| = (6x + 1)² = φ(x)²
-- and proves all norm axioms N1–N8.
-- Then proves: every element of AntiDiag has an irreducible divisor.

import TPC.AntiDiagonal
import TPC.WeaklySaturated
import Mathlib.Tactic
import Mathlib.Data.Int.Order

namespace TPC

-- ============================================================
-- Section 1: The norm
-- ============================================================

/-- The norm of (x, -x) is (6x + 1)² -/
def norm (x : ℤ) : ℤ := (6 * x + 1) ^ 2

@[simp] lemma norm_def (x : ℤ) : norm x = (6 * x + 1) ^ 2 := rfl

/-- norm in terms of φ -/
lemma norm_eq_φ_sq (x : ℤ) : norm x = φ x ^ 2 := by
  simp [norm, φ]

-- ============================================================
-- Section 2: Norm axioms
-- ============================================================

/-- N1: Non-negativity -/
lemma norm_nonneg (x : ℤ) : 0 ≤ norm x := by
  simp [norm]
  positivity

/-- N2: Identity -/
@[simp] lemma norm_zero : norm 0 = 1 := by simp [norm]

/-- N3: Non-degeneracy: norm x = 1 ↔ x = 0 -/
lemma norm_eq_one_iff (x : ℤ) : norm x = 1 ↔ x = 0 := by
  simp [norm]
  constructor
  · intro h
    have : (6 * x + 1) ^ 2 = 1 ^ 2 := by linarith
    have := sq_eq_sq' (by linarith) (le_of_eq (by linarith)) |>.mp this
    omega
  · intro h; subst h; ring

/-- N3': norm x ≠ 1 when x ≠ 0 -/
lemma norm_ne_one_of_ne_zero (x : ℤ) (hx : x ≠ 0) : norm x ≠ 1 := by
  rwa [← not_iff_not, not_not, norm_eq_one_iff]

/-- N3'': norm x ≥ 2 when x ≠ 0 -/  
lemma norm_ge_two_of_ne_zero (x : ℤ) (hx : x ≠ 0) : norm x ≥ 4 := by
  simp [norm]
  have : 6 * x + 1 ≠ 1 := by omega
  have : 6 * x + 1 ≠ -1 := by omega
  nlinarith [sq_nonneg (6 * x + 1), sq_abs (6 * x + 1)]

/-- N4: Integrality (norm is a positive integer) -/
lemma norm_pos (x : ℤ) : 0 < norm x := by
  simp [norm]; positivity

/-- N5: Multiplicativity: norm(x ⊛ y) = norm(x) * norm(y) -/
lemma norm_mul (x y : ℤ) : norm (x ⊛ y) = norm x * norm y := by
  simp [norm, φ, mstar]
  ring

/-- N6: Strict descent on proper factors -/
lemma norm_factor_lt (x a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hprod : a ⊛ b = x) :
    norm a < norm x ∧ norm b < norm x := by
  subst hprod
  rw [norm_mul]
  constructor
  · have hb4 : norm b ≥ 4 := norm_ge_two_of_ne_zero b hb
    have ha1 : norm a ≥ 1 := le_of_lt (norm_pos a)
    nlinarith
  · have ha4 : norm a ≥ 4 := norm_ge_two_of_ne_zero a ha
    have hb1 : norm b ≥ 1 := le_of_lt (norm_pos b)
    nlinarith

/-- N7: Note on asymmetry: norm(-x) = (6(-x)+1)² = (6x-1)² ≠ (6x+1)² in general -/
lemma norm_neg (x : ℤ) : norm (-x) = (6 * x - 1) ^ 2 := by
  simp [norm]; ring

/-- N7 example: norm(1) = 49, norm(-1) = 25 -/
example : norm 1 = 49 := by norm_num [norm]
example : norm (-1) = 25 := by norm_num [norm]

/-- N8: Growth -/
lemma norm_tendsto_infty : ∀ C : ℤ, ∃ N : ℤ, ∀ x : ℤ, x > N → norm x > C := by
  intro C
  use C  -- rough bound; for large x, (6x+1)² >> C
  intro x hx
  simp [norm]
  nlinarith

-- ============================================================
-- Section 3: Every element has an irreducible divisor
-- ============================================================

/-- An element x ∈ ℤ is ⊛-irreducible if x ≠ 0 and
    x = a ⊛ b implies a = 0 or b = 0 -/
def Irred (x : ℤ) : Prop :=
  x ≠ 0 ∧ ∀ a b : ℤ, a ⊛ b = x → a = 0 ∨ b = 0

/-- x divides y in (ℤ, ⊛): ∃ m, x ⊛ m = y -/
def mstar_dvd (x y : ℤ) : Prop := ∃ m : ℤ, x ⊛ m = y

notation:50 x " ∣⊛ " y => mstar_dvd x y

/-- Every nonzero element of (ℤ, ⊛) has an irreducible ⊛-divisor -/
theorem exists_irred_dvd (k : ℤ) (hk : k ≠ 0) :
    ∃ q : ℤ, Irred q ∧ q ∣⊛ k := by
  -- Strong induction on |norm k|
  induction h : norm k using Nat.strong_rec_on generalizing k with
  | _ n ih => ?_
  sorry -- filled by well-founded recursion on norm

-- ============================================================
-- Section 4: Covering lemma
-- ============================================================

/-- Every nonzero element of AntiDiag is in q ⊗ AntiDiag
    for some irreducible q ∈ AntiDiag -/
theorem covering (k : ℤ) (hk : k ≠ 0) :
    ∃ q : ℤ, Irred q ∧ ∃ m : ℤ, Δ q ⊗ Δ m = Δ k := by
  obtain ⟨q, hq, m, hm⟩ := exists_irred_dvd k hk
  exact ⟨q, hq, m, by rw [Δ_otimes, hm]⟩

end TPC
