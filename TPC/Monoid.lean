-- TPC/Monoid.lean
-- Packages ⊛ and ⋆ as Lean CommMonoid instances,
-- and defines the product monoid M = (ℤ², ⊗).

import TPC.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

namespace TPC

-- ============================================================
-- Section 1: CommMonoid instance for (ℤ, ⊛)
-- ============================================================

/-- The type ℤ equipped with ⊛ as its multiplication -/
def Nstar := ℤ

instance : One Nstar := ⟨(0 : ℤ)⟩
instance : Mul Nstar := ⟨mstar⟩

instance : CommMonoid Nstar where
  mul_assoc := mstar_assoc
  one_mul   := mstar_zero_left
  mul_one   := mstar_zero_right
  mul_comm  := mstar_comm

-- ============================================================
-- Section 2: CommMonoid instance for (ℤ, ⋆)
-- ============================================================

/-- The type ℤ equipped with ⋆ as its multiplication -/
def Nsstar := ℤ

instance : One Nsstar := ⟨(0 : ℤ)⟩
instance instMulNsstar : Mul Nsstar := ⟨sstar⟩

instance : CommMonoid Nsstar where
  mul_assoc := sstar_assoc
  one_mul   := sstar_zero_left
  mul_one   := sstar_zero_right
  mul_comm  := sstar_comm

-- ============================================================
-- Section 3: The product monoid M = (ℤ², ⊗)
-- ============================================================

/-- The product operation on ℤ² -/
def otimes (p q : ℤ × ℤ) : ℤ × ℤ :=
  (mstar p.1 q.1, sstar p.2 q.2)

notation:70 p " ⊗ " q => otimes p q

@[simp] lemma otimes_def (a b c d : ℤ) :
    (a, b) ⊗ (c, d) = (a ⊛ c, b ⋆ d) := rfl

/-- Identity of ⊗ is (0, 0) -/
@[simp] lemma otimes_one_left (p : ℤ × ℤ) : (0, 0) ⊗ p = p := by
  simp [otimes, mstar, sstar]

@[simp] lemma otimes_one_right (p : ℤ × ℤ) : p ⊗ (0, 0) = p := by
  simp [otimes, mstar, sstar]

/-- ⊗ is associative -/
lemma otimes_assoc (p q r : ℤ × ℤ) : (p ⊗ q) ⊗ r = p ⊗ (q ⊗ r) := by
  simp [otimes, mstar_assoc, sstar_assoc]

/-- ⊗ is commutative -/
lemma otimes_comm (p q : ℤ × ℤ) : p ⊗ q = q ⊗ p := by
  simp [otimes, mstar_comm, sstar_comm]

/-- M = (ℤ², ⊗) is a commutative monoid -/
instance : CommMonoid (ℤ × ℤ) where
  mul       := otimes
  mul_assoc := otimes_assoc
  one       := (0, 0)
  one_mul   := otimes_one_left
  mul_one   := otimes_one_right
  mul_comm  := otimes_comm

-- ============================================================
-- Section 4: φ as a monoid hom Nstar → (ℤ, ·)
-- ============================================================

/-- φ is a monoid homomorphism (ℤ, ⊛) → (ℤ, ·) -/
def φHom : MonoidHom Nstar ℤ where
  toFun    := φ
  map_one' := φ_zero
  map_mul' := φ_mul

end TPC
