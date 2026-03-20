-- TPC/Basic.lean
-- Defines the two monoid operations * and ⋆ on ℤ,
-- proves they are commutative monoids, and establishes
-- the isomorphisms φ : N* → (6ℤ+1, ·) and ψ : N⋆ → (6ℤ-1, ⊙).

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace TPC

-- ============================================================
-- Section 1: The two operations
-- ============================================================

/-- The * operation: x * y = 6xy + x + y -/
def mstar (x y : ℤ) : ℤ := 6 * x * y + x + y

/-- The ⋆ operation: x ⋆ y = -6xy + x + y -/
def sstar (x y : ℤ) : ℤ := -6 * x * y + x + y

-- Notation
notation:70 x " ⊛ " y => mstar x y
notation:70 x " ⋆ " y => sstar x y

-- ============================================================
-- Section 2: Basic algebraic identities
-- ============================================================

@[simp] lemma mstar_def (x y : ℤ) : x ⊛ y = 6 * x * y + x + y := rfl

@[simp] lemma sstar_def (x y : ℤ) : x ⋆ y = -6 * x * y + x + y := rfl

/-- The identity element of ⊛ is 0 -/
@[simp] lemma mstar_zero_right (x : ℤ) : x ⊛ 0 = x := by
  simp [mstar]

@[simp] lemma mstar_zero_left (x : ℤ) : 0 ⊛ x = x := by
  simp [mstar]

/-- The identity element of ⋆ is 0 -/
@[simp] lemma sstar_zero_right (x : ℤ) : x ⋆ 0 = x := by
  simp [sstar]

@[simp] lemma sstar_zero_left (x : ℤ) : 0 ⋆ x = x := by
  simp [sstar]

/-- Commutativity of ⊛ -/
lemma mstar_comm (x y : ℤ) : x ⊛ y = y ⊛ x := by
  simp [mstar]; ring

/-- Commutativity of ⋆ -/
lemma sstar_comm (x y : ℤ) : x ⋆ y = y ⋆ x := by
  simp [sstar]; ring

/-- Associativity of ⊛ -/
lemma mstar_assoc (x y z : ℤ) : (x ⊛ y) ⊛ z = x ⊛ (y ⊛ z) := by
  simp [mstar]; ring

/-- Associativity of ⋆ -/
lemma sstar_assoc (x y z : ℤ) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) := by
  simp [sstar]; ring

-- ============================================================
-- Section 3: The isomorphism maps φ and ψ
-- ============================================================

/-- φ : ℤ → ℤ, φ(x) = 6x + 1 -/
def φ (x : ℤ) : ℤ := 6 * x + 1

/-- ψ : ℤ → ℤ, ψ(x) = 6x - 1 -/
def ψ (x : ℤ) : ℤ := 6 * x - 1

/-- φ is a monoid homomorphism: φ(x ⊛ y) = φ(x) * φ(y) -/
lemma φ_mul (x y : ℤ) : φ (x ⊛ y) = φ x * φ y := by
  simp [φ, mstar]; ring

/-- φ sends identity to identity: φ(0) = 1 -/
@[simp] lemma φ_zero : φ 0 = 1 := by simp [φ]

/-- ψ is a monoid homomorphism into (6ℤ-1, ⊙) where x ⊙ y = -(xy) -/
-- We express this as: ψ(x ⋆ y) = -(ψ(x) * ψ(y))
lemma ψ_mul (x y : ℤ) : ψ (x ⋆ y) = -(ψ x * ψ y) := by
  simp [ψ, sstar]; ring

/-- ψ sends identity to -1: ψ(0) = -1 -/
@[simp] lemma ψ_zero : ψ 0 = -1 := by simp [ψ]

-- ============================================================
-- Section 4: The η involution
-- ============================================================

/-- η : ℤ → ℤ, η(x) = -x -/
def η (x : ℤ) : ℤ := -x

/-- η is an isomorphism N* → N⋆: η(x ⊛ y) = η(x) ⋆ η(y) -/
lemma η_mstar_sstar (x y : ℤ) : η (x ⊛ y) = η x ⋆ η y := by
  simp [η, mstar, sstar]; ring

/-- η is its own inverse -/
@[simp] lemma η_η (x : ℤ) : η (η x) = x := by simp [η]

/-- Key identity: (-x) ⋆ (-y) = -(x ⊛ y) -/
lemma neg_sstar_neg (x y : ℤ) : (-x) ⋆ (-y) = -(x ⊛ y) := by
  simp [sstar, mstar]; ring

-- ============================================================
-- Section 5: No zero divisors
-- ============================================================

/-- ⊛ has no zero divisors: if u ⊛ v = 0 and u ≠ 0 then v = 0 -/
lemma mstar_no_zero_div (u v : ℤ) (hu : u ≠ 0) (hv : u ⊛ v = 0) : v = 0 := by
  -- u ⊛ v = 0 iff (6u+1)(6v+1) = 1
  have hphi : φ u * φ v = 1 := by
    have := φ_mul u v
    simp [mstar, φ] at this ⊢
    linarith [hv.symm ▸ this]
  -- In ℤ, ab = 1 implies a = b = 1 or a = b = -1
  have := Int.eq_one_or_neg_one_of_mul_eq_one' hphi
  simp [φ] at this
  cases this with
  | inl h =>
    obtain ⟨h1, h2⟩ := h
    linarith
  | inr h =>
    obtain ⟨h1, h2⟩ := h
    have : u = -1/3 := by linarith
    norm_num at this

/-- ⋆ has no zero divisors -/
lemma sstar_no_zero_div (u v : ℤ) (hu : u ≠ 0) (hv : u ⋆ v = 0) : v = 0 := by
  -- u ⋆ v = 0 iff (6u-1)(6v-1) = 0
  have hpsi : ψ u * ψ v = 0 := by
    have := ψ_mul u v
    simp [sstar, ψ] at this ⊢
    linarith [hv.symm ▸ (show -(ψ u * ψ v) = 0 from by linarith)]
  rcases Int.mul_eq_zero.mp hpsi with h | h
  · simp [ψ] at h; linarith
  · simp [ψ] at h; linarith

-- ============================================================
-- Section 6: Images of φ and ψ
-- ============================================================

/-- φ(x) ≡ 1 (mod 6) -/
lemma φ_mod_6 (x : ℤ) : φ x % 6 = 1 := by
  simp [φ]; omega

/-- ψ(x) ≡ -1 (mod 6) -/  
lemma ψ_mod_6 (x : ℤ) : ψ x % 6 = -1 % 6 := by
  simp [ψ]; omega

end TPC
