-- TPC/Monoid.lean
-- Packages ⊛ and ⋆ as Lean CommMonoid instances,
-- defines the monoid tensor product M = (ℤ, ⊛) ⊗_Mon (ℤ, ⋆),
-- and the diagonal submonoid N = ⟨{k ⊗ k : k ∈ ℤ}⟩.

import TPC.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Submonoid.Basic
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
-- Section 3: The monoid tensor product M = (ℤ, ⊛) ⊗_Mon (ℤ, ⋆)
-- ============================================================

/-- The monoid tensor product of (ℤ, ⊛) and (ℤ, ⋆).
    Elements are equivalence classes of formal products of pure tensors z ⊗ w,
    subject to bilinearity:
      (a ⊛ b) ⊗ w = (a ⊗ w) * (b ⊗ w)
      z ⊗ (c ⋆ d) = (z ⊗ c) * (z ⊗ d)
      z ⊗ 0 = 0 ⊗ w = 1  (identity)

    Since Mathlib does not have a direct MonoidTensorProduct construction,
    we axiomatize the type and its key properties. -/

axiom MonTensor : Type

/-- Pure tensor: z ⊗ w -/
axiom MonTensor.mk : ℤ → ℤ → MonTensor

/-- Monoid multiplication on MonTensor -/
axiom MonTensor.mul : MonTensor → MonTensor → MonTensor

/-- Identity element of MonTensor -/
axiom MonTensor.one : MonTensor

instance : Mul MonTensor := ⟨MonTensor.mul⟩
instance : One MonTensor := ⟨MonTensor.one⟩

/-- MonTensor forms a commutative monoid -/
instance : CommMonoid MonTensor := sorry

-- ============================================================
-- Section 4: Bilinearity axioms
-- ============================================================

/-- Left bilinearity: (a ⊛ b) ⊗ w = (a ⊗ w) * (b ⊗ w) -/
axiom bilin_left (a b w : ℤ) :
  MonTensor.mk (mstar a b) w = MonTensor.mk a w * MonTensor.mk b w

/-- Right bilinearity: z ⊗ (c ⋆ d) = (z ⊗ c) * (z ⊗ d) -/
axiom bilin_right (z c d : ℤ) :
  MonTensor.mk z (sstar c d) = MonTensor.mk z c * MonTensor.mk z d

/-- Left absorption: 0 ⊗ w = 1 (identity element) -/
axiom tensor_zero_left (w : ℤ) : MonTensor.mk 0 w = 1

/-- Right absorption: z ⊗ 0 = 1 (identity element) -/
axiom tensor_zero_right (z : ℤ) : MonTensor.mk z 0 = 1

-- ============================================================
-- Section 5: Derived properties of MonTensor
-- ============================================================

/-- The identity tensor is MonTensor.one -/
lemma tensor_one_eq : MonTensor.mk 0 0 = 1 := tensor_zero_left 0

/-- Expansion of a pure tensor product via bilinearity:
    (a ⊗ c) * (b ⊗ d) can be related to (a ⊛ b) ⊗ (c ⋆ d)
    through intermediate steps -/

-- ============================================================
-- Section 6: The diagonal submonoid N = ⟨{k ⊗ k : k ∈ ℤ}⟩
-- ============================================================

/-- The diagonal generator: k ↦ k ⊗ k -/
def diagGen (k : ℤ) : MonTensor := MonTensor.mk k k

/-- diagGen(0) = 1 -/
@[simp] lemma diagGen_zero : diagGen 0 = 1 := tensor_zero_left 0

/-- The diagonal submonoid N = ⟨{k ⊗ k : k ∈ ℤ}⟩ -/
def N : Submonoid MonTensor := Submonoid.closure (Set.range diagGen)

/-- Every diagonal generator is in N -/
lemma diagGen_mem_N (k : ℤ) : diagGen k ∈ N :=
  Submonoid.subset_closure ⟨k, rfl⟩

/-- The identity is in N -/
lemma one_mem_N : (1 : MonTensor) ∈ N := N.one_mem

-- ============================================================
-- Section 7: φ as a monoid hom Nstar → (ℤ, ·)
-- ============================================================

/-- φ is a monoid homomorphism (ℤ, ⊛) → (ℤ, ·) -/
def φHom : MonoidHom Nstar ℤ where
  toFun    := φ
  map_one' := φ_zero
  map_mul' := φ_mul

-- ============================================================
-- Section 8: The universal bilinear map β
-- ============================================================

/-- The universal bilinear map β : ℤ × ℤ → MonTensor -/
def β : ℤ × ℤ → MonTensor := fun ⟨z, w⟩ => MonTensor.mk z w

@[simp] lemma β_def (z w : ℤ) : β (z, w) = MonTensor.mk z w := rfl

/-- β is "bilinear" in the monoid sense -/
lemma β_bilin_left (a b w : ℤ) :
    β (mstar a b, w) = β (a, w) * β (b, w) := bilin_left a b w

lemma β_bilin_right (z c d : ℤ) :
    β (z, sstar c d) = β (z, c) * β (z, d) := bilin_right z c d

end TPC
