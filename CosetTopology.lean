-- TPC/CosetTopology.lean  [github.com/FruitfulApproach/Lean4TPC/blob/main/TPC/CosetTopology.lean]
-- Central argument:
--   Lem 3.1: q̂ ⊗ M is clopen in M (arithmetic progression in each component)
--   Thm 3.2: For q̂ ∈ Irr(N), q̂ ⊗ N = N ∩ (q̂ ⊗ M)
--   Cor 3.3: q̂ ⊗ N is clopen in N (subspace topology)
--   Lem 3.4: q̂ ⊗ N is infinite

import TPC.Basic
import TPC.Monoid
import Mathlib.Tactic

namespace TPC

-- ── §1: q̂ ⊗ M is clopen ────────────────────────────────────

/-- The left coset of M by (a₁, a₂):
    (a₁, a₂) ⊗ M = (a₁ + (6a₁+1)ℤ) × (a₂ + (6a₂-1)ℤ) -/
def cosetM (a₁ a₂ : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ x y : ℤ, p = (a₁ ⊛ x, a₂ ⋆ y)}

lemma cosetM_eq_arith_prog (a₁ a₂ : ℤ) :
    cosetM a₁ a₂ =
    {p | ∃ z : ℤ, p.1 = a₁ + (6*a₁+1)*z} ×ˢ
    {p | ∃ z : ℤ, p.2 = a₂ + (6*a₂-1)*z} := by
  ext ⟨x, y⟩
  simp [cosetM, mstar, sstar, Set.mem_prod]
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨⟨u, by ring⟩, v, by ring⟩
  · rintro ⟨⟨u, hu⟩, v, hv⟩
    exact ⟨u, v, by constructor <;> linarith⟩

/-- (a₁, a₂) ⊗ M is clopen in M (product of two arithmetic progressions) -/
theorem cosetM_isClopen (a₁ a₂ : ℤ) (ha : (a₁, a₂) ≠ (0,0)) :
    IsClopen (cosetM a₁ a₂) := by
  rw [cosetM_eq_arith_prog]
  -- Each factor is an arithmetic progression, hence clopen in Furstenberg topology
  apply IsClopen.prod
  · constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨a₁, 6*a₁+1, by omega, rfl⟩
    · sorry -- complement is finite union of translates, hence open
  · constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨a₂, 6*a₂-1, by omega, rfl⟩
    · sorry

-- ── §2: Coset Identity ─────────────────────────────────────

/-- Irreducible elements of N = ⟨G⟩ -/
def IsIrred (p : ℤ × ℤ) : Prop :=
  p ∈ N ∧ p ≠ (0,0) ∧
  ∀ a b : ℤ × ℤ, a ∈ N → b ∈ N → a ≠ (0,0) → b ≠ (0,0) → a ⊗ b ≠ p

/-- For q̂ = (q,q) ∈ Irr(N) with φ(q) prime:
    q̂ ⊗ N = N ∩ (q̂ ⊗ M)
    
    KEY LEMMA: this makes q̂ ⊗ N clopen in N (subspace topology),
    since q̂ ⊗ M is clopen in M. -/
theorem coset_identity (q : ℤ) (hq : IsIrred (q, q))
    (hprime : (6 * q + 1).natAbs.Prime) :
    (fun p => (q,q) ⊗ p) '' (N : Set (ℤ × ℤ)) =
    (N : Set (ℤ × ℤ)) ∩ cosetM q q := by
  ext ⟨z, w⟩
  simp [cosetM, Set.mem_image]
  constructor
  -- (⊆): q̂ ⊗ N ⊆ N ∩ (q̂ ⊗ M)
  · rintro ⟨⟨p, r⟩, hp, rfl⟩
    constructor
    · exact N.mul_mem (hq.1) hp
    · exact ⟨p, r, rfl⟩
  -- (⊇): N ∩ (q̂ ⊗ M) ⊆ q̂ ⊗ N
  · rintro ⟨hmem, x, y, hzw⟩
    -- (z,w) ∈ N: z = k₁ ⊛ ⋯ ⊛ kₛ, w = k₁ ⋆ ⋯ ⋆ kₛ same sequence
    -- (z,w) ∈ q̂ ⊗ M: q ⊛ x = z
    -- Since φ(q) prime divides φ(z) = φ(k₁)⋯φ(kₛ),
    -- φ(q) divides φ(kᵢ) for some i, so kᵢ = q.
    -- By commutativity, reorder to get (z,w) = (q,q) ⊗ (remainder ∈ N).
    sorry

-- ── §3: Clopenness and Infinitude ──────────────────────────

/-- q̂ ⊗ N is clopen in the subspace topology on N -/
theorem cosetN_isClopen (q : ℤ) (hq : IsIrred (q, q))
    (hprime : (6 * q + 1).natAbs.Prime) :
    IsClopen ((fun p => (q,q) ⊗ p) '' (N : Set (ℤ × ℤ))) := by
  rw [coset_identity q hq hprime]
  -- N ∩ clopen = clopen in subspace topology
  exact (cosetM_isClopen q q (by simp [hq.2.1])).inter_right _

/-- q̂ ⊗ N is infinite (left mult by q̂ is injective) -/
theorem cosetN_infinite (q : ℤ) (hq : IsIrred (q, q)) :
    ((fun p => (q,q) ⊗ p) '' (N : Set (ℤ × ℤ))).Infinite := by
  apply Set.infinite_image_of_injective
  -- Injectivity: (q,q) ⊗ a = (q,q) ⊗ b → a = b
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp [otimes] at h
  obtain ⟨h1, h2⟩ := h
  -- φ(q)·φ(a₁) = φ(q)·φ(b₁), and φ(q) ≠ 0
  have hφq : φ q ≠ 0 := by simp [φ]; omega
  have ha1 : φ a₁ = φ b₁ := by
    have := congr_arg φ h1
    rw [φ_mul, φ_mul] at this
    exact mul_left_cancel₀ hφq this
  ext
  · exact φ_injective ha1
  · have := congr_arg ψ h2
    simp [ψ_mul] at this
    have hψq : ψ q ≠ 0 := by simp [ψ]; omega
    exact ψ_injective (mul_right_cancel₀ hψq (by linarith))
  -- N is infinite (contains all generators Δ k for k ∈ ℤ)
  exact Set.infinite_range_of_injective (fun a b h => by simp [Δ] at h; exact h) |>.mono
    (Set.range_subset_iff.mpr Δ_mem_N)

end TPC
