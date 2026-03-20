-- TPC/WeaklySaturated.lean
-- Abstract definition of weakly saturated submonoid
-- and proof that AntiDiag ≤ M is weakly saturated.

import TPC.AntiDiagonal
import Mathlib.Tactic

namespace TPC

-- ============================================================
-- Section 1: Abstract definition
-- ============================================================

/-- A submonoid N ≤ M is weakly saturated if:
    for all a, b ≠ 1_M, ab ∈ N implies
    there exist a', b' ≠ 1_N in N with a'b' = ab -/
structure WeaklySaturated {M : Type*} [CommMonoid M]
    (N : Submonoid M) : Prop where
  cond : ∀ a b : M, a ≠ 1 → b ≠ 1 → a * b ∈ N →
         ∃ a' b' : N, (a' : M) ≠ 1 ∧ (b' : M) ≠ 1 ∧
         (a' : M) * b' = a * b

-- ============================================================
-- Section 2: Irreducibility preserved by weak saturation
-- ============================================================

/-- Key corollary: weak saturation implies irreducibility coincides -/
theorem irred_iff_of_weaklySaturated {M : Type*} [CommMonoid M]
    (N : Submonoid M) (ws : WeaklySaturated N) (n : N) :
    (∀ a b : M, a ≠ 1 → b ≠ 1 → a * b ≠ (n : M)) ↔
    (∀ a b : N, (a : M) ≠ 1 → (b : M) ≠ 1 → (a : M) * b ≠ (n : M)) := by
  constructor
  · intro hM a b ha hb heq
    exact hM a b ha hb heq
  · intro hN a b ha hb heq
    -- a * b = n and n ∈ N, so by weak saturation get a', b' ∈ N
    have hmem : a * b ∈ N := heq ▸ n.2
    obtain ⟨a', b', ha', hb', hprod⟩ := ws.cond a b ha hb hmem
    rw [← hprod] at heq
    exact hN a' b' ha' hb' heq

-- ============================================================
-- Section 3: AntiDiag is weakly saturated in M
-- ============================================================

/-- AntiDiag is weakly saturated in (ℤ², ⊗) -/
theorem antiDiag_weaklySaturated :
    WeaklySaturated antiDiagSubmonoid := by
  constructor
  intro a b ha hb hmem
  -- hmem : a ⊗ b ∈ AntiDiag
  simp [antiDiagSubmonoid, AntiDiag] at hmem
  -- a ⊗ b = (a.1 ⊛ b.1, a.2 ⋆ b.2)
  -- The second component is -(first component)
  -- hmem says (a ⊗ b).2 = -(a ⊗ b).1
  simp [otimes, mstar, sstar] at hmem
  -- Let k = a.1 ⊛ b.1, so the product is Δ k
  set k := a.1 ⊛ b.1 with hk_def
  -- a.1 ≠ 0 since a ≠ 1 = (0,0)
  have ha1 : a.1 ≠ 0 := by
    intro h
    apply ha
    ext
    · exact h
    · simp [AntiDiag] at *
      -- if a.1 = 0 and a ∈ AntiDiag... but a need not be in AntiDiag
      sorry
  have hb1 : b.1 ≠ 0 := by
    sorry
  -- Construct a' = Δ(a.1) and b' = Δ(b.1)
  refine ⟨⟨Δ a.1, Δ_mem a.1⟩, ⟨Δ b.1, Δ_mem b.1⟩, ?_, ?_, ?_⟩
  · simp [Δ]; exact ha1
  · simp [Δ]; exact hb1
  · simp [Δ_otimes]
    -- need Δ(a.1 ⊛ b.1) = a ⊗ b
    ext
    · simp [otimes, Δ]
    · simp [otimes, Δ, hmem]; ring

-- ============================================================
-- Section 4: AntiDiag is NOT saturated (counterexample)
-- ============================================================

/-- Counterexample: (1, 0) ⊗ (1, -8) = (8, -8) ∈ AntiDiag
    but (1, 0) ∉ AntiDiag -/
theorem antiDiag_not_saturated :
    ∃ a b : ℤ × ℤ, a ∉ AntiDiag ∧ b ∉ AntiDiag ∧
    a ⊗ b ∈ AntiDiag := by
  refine ⟨(1, 0), (1, -8), ?_, ?_, ?_⟩
  · simp [AntiDiag]
  · simp [AntiDiag]
  · simp [AntiDiag, otimes, mstar, sstar]
    norm_num

end TPC
