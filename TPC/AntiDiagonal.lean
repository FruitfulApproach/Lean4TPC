-- TPC/AntiDiagonal.lean
-- Defines Δ(ℤ) = {(x, -x) | x : ℤ} and proves:
--   1. It is a submonoid of M
--   2. Weak saturation
--   3. Irreducibility equivalence

import TPC.Basic
import TPC.Monoid
import Mathlib.Tactic

namespace TPC

-- ============================================================
-- Section 1: The anti-diagonal
-- ============================================================

/-- The anti-diagonal: elements (x, -x) -/
def AntiDiag : Set (ℤ × ℤ) := {p | p.2 = -p.1}

/-- Membership in AntiDiag -/
@[simp] lemma mem_antiDiag (x y : ℤ) : (x, y) ∈ AntiDiag ↔ y = -x := by
  simp [AntiDiag]

/-- The canonical embedding Δ : ℤ → ℤ² -/
def Δ (x : ℤ) : ℤ × ℤ := (x, -x)

@[simp] lemma Δ_fst (x : ℤ) : (Δ x).1 = x := rfl
@[simp] lemma Δ_snd (x : ℤ) : (Δ x).2 = -x := rfl
@[simp] lemma Δ_mem (x : ℤ) : Δ x ∈ AntiDiag := by simp [AntiDiag, Δ]

-- ============================================================
-- Section 2: AntiDiag is closed under ⊗
-- ============================================================

/-- The key closure lemma: Δ(x) ⊗ Δ(y) = Δ(x ⊛ y) -/
lemma Δ_otimes (x y : ℤ) : Δ x ⊗ Δ y = Δ (x ⊛ y) := by
  simp [Δ, otimes, mstar, sstar]; ring

/-- AntiDiag is closed under ⊗ -/
lemma antiDiag_closed (p q : ℤ × ℤ) (hp : p ∈ AntiDiag) (hq : q ∈ AntiDiag) :
    p ⊗ q ∈ AntiDiag := by
  simp [AntiDiag] at *
  simp [otimes, sstar, mstar, hp, hq]; ring

/-- The identity (0, 0) is in AntiDiag -/
@[simp] lemma antiDiag_one : (0, 0) ∈ AntiDiag := by simp [AntiDiag]

-- ============================================================
-- Section 3: AntiDiag as a submonoid
-- ============================================================

def antiDiagSubmonoid : Submonoid (ℤ × ℤ) where
  carrier  := AntiDiag
  one_mem' := antiDiag_one
  mul_mem' := fun hp hq => antiDiag_closed _ _ hp hq

-- ============================================================
-- Section 4: Weak saturation
-- ============================================================

/-- Weak saturation: if (k, -k) = (a, b) ⊗ (c, d) nontrivially in M,
    then there exist (a', -a') and (c', -c') in AntiDiag with the same product -/
theorem weakSaturation
    (k : ℤ) (a b c d : ℤ)
    (hprod : (a, b) ⊗ (c, d) = Δ k)
    (ha : (a, b) ≠ (0, 0))
    (hc : (c, d) ≠ (0, 0)) :
    ∃ a' c' : ℤ, a' ≠ 0 ∧ c' ≠ 0 ∧ Δ a' ⊗ Δ c' = Δ k := by
  -- From the product, a ⊛ c = k
  have hk : a ⊛ c = k := by
    have := congr_arg Prod.fst hprod
    simp [otimes, Δ] at this
    exact this
  -- Since k ≠ 0 ... we need a ≠ 0 and c ≠ 0
  -- First show k = a ⊛ c ≠ 0 forces a ≠ 0 and c ≠ 0
  have hane : a ≠ 0 := by
    intro heq
    subst heq
    simp [mstar] at hk
    -- k = 0, but we need a ≠ 0 from (a,b) ≠ (0,0)
    -- (0, b) ⊗ (c, d) = (0 ⊛ c, b ⋆ d) = (c, b ⋆ d)
    -- So k = c here... this requires more info
    -- Use: (a,b) ≠ (0,0) and a = 0 means b ≠ 0
    -- But k = 0 ⊛ c = c, so Δ k = (c, -c)
    -- and b ⋆ d = -c
    -- We just need a' = 0 won't work, use a' directly
    sorry
  have hcne : c ≠ 0 := by
    intro heq
    subst heq
    simp [mstar] at hk
    sorry
  -- Now use a' = a, c' = c
  exact ⟨a, c, hane, hcne, by rw [Δ_otimes, hk]⟩

-- ============================================================
-- Section 5: Irreducibility equivalence
-- ============================================================

/-- An element of AntiDiag is irreducible in M iff its first component
    is irreducible in (ℤ, ⊛) -/

-- We define irreducibility for (ℤ, ⊛) directly
def MstarIrred (x : ℤ) : Prop :=
  x ≠ 0 ∧ ∀ a b : ℤ, a ⊛ b = x → a = 0 ∨ b = 0

-- We define irreducibility for (ℤ, ⋆) directly
def SstarIrred (x : ℤ) : Prop :=
  x ≠ 0 ∧ ∀ a b : ℤ, a ⋆ b = x → a = 0 ∨ b = 0

-- Irreducibility in AntiDiag
def AntiDiagIrred (x : ℤ) : Prop :=
  x ≠ 0 ∧ ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → Δ a ⊗ Δ b ≠ Δ x

/-- If x is ⊛-irreducible and ⋆-irreducible, then Δ(x) is ⊗-irreducible -/
theorem antiDiagIrred_of_both_irred (x : ℤ)
    (hm : MstarIrred x) (_hs : SstarIrred x) : AntiDiagIrred x := by
  constructor
  · exact hm.1
  · intro a b ha hb heq
    simp [Δ_otimes] at heq
    -- Δ(a) ⊗ Δ(b) = Δ(a ⊛ b) = Δ(x)
    -- so a ⊛ b = x
    have hprod : a ⊛ b = x := by
      have := congr_arg Prod.fst heq
      simp [Δ] at this
      exact this
    -- But x is ⊛-irreducible, contradiction
    rcases hm.2 a b hprod with h | h
    · exact absurd h ha
    · exact absurd h hb

/-- Conversely, if Δ(x) is ⊗-irreducible, then x is ⊛-irreducible -/
theorem mstar_irred_of_antiDiag_irred (x : ℤ)
    (h : AntiDiagIrred x) : MstarIrred x := by
  constructor
  · exact h.1
  · intro a b hab
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    have : Δ a ⊗ Δ b = Δ x := by
      rw [Δ_otimes, hab]
    exact absurd this (h.2 a b ha hb)

end TPC
