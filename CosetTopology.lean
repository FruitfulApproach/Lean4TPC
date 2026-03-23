-- TPC/CosetTopology.lean  [github.com/FruitfulApproach/Lean4TPC/blob/main/TPC/CosetTopology.lean]
-- Corrected topology argument:
--   Def: S_q = (q + φ(q)ℤ) × (q + ψ(q)ℤ) — the "clopen envelope" of q̂·N
--   Lem (containment): q̂ ⊗ N ⊆ N ∩ S_q
--   Lem (identity excluded): e = (0,0) ∉ S_q
--   Thm (clopenness): N ∩ S_q is clopen in N (subspace topology from ℤ²)
--
-- Note: The old "Coset Identity" (Thm 3.2 in earlier versions) claimed q̂⊗N = N ∩ (q̂⊗M).
-- This is FALSE: e.g. (36,36) ∈ N ∩ (cosetM 1 1) but (36,36) ∉ (1,1)⊗N.
-- The Furstenberg argument only needs containment + identity-exclusion, not equality.

import TPC.Basic
import TPC.Monoid
import Mathlib.Tactic

namespace TPC

-- ── §1: The clopen envelope S_q ─────────────────────────────

/-- The clopen envelope of (q,q)·N in ℤ²:
    S_q = (q + φ(q)ℤ) × (q + |ψ(q)|ℤ) = (q + (6q+1)ℤ) × (q + (6q-1)ℤ) -/
def clopenEnv (q : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ a b : ℤ, p = (q + (6*q+1)*a, q + (6*q-1)*b)}

lemma clopenEnv_eq (q : ℤ) :
    clopenEnv q =
    {p | ∃ a : ℤ, p.1 = q + (6*q+1)*a} ×ˢ
    {p | ∃ b : ℤ, p.2 = q + (6*q-1)*b} := by
  ext ⟨x, y⟩
  simp [clopenEnv, Set.mem_prod]
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨⟨a, rfl⟩, b, rfl⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩; exact ⟨a, b, Prod.ext ha hb⟩

/-- S_q is clopen in ℤ² (product of two arithmetic progressions) -/
theorem clopenEnv_isClopen (q : ℤ) (hq_ne : q ≠ 0) :
    IsClopen (clopenEnv q) := by
  rw [clopenEnv_eq]
  apply IsClopen.prod
  · constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨q, 6*q+1, by omega, rfl⟩
    · sorry -- complement is finite union of arithmetic progressions
  · constructor
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨q, 6*q-1, by omega, rfl⟩
    · sorry

-- ── §2: Irreducibles and the key lemmas ──────────────────────

/-- Irreducible elements of N = ⟨G⟩ -/
def IsIrred (p : ℤ × ℤ) : Prop :=
  p ∈ N ∧ p ≠ (0,0) ∧
  ∀ a b : ℤ × ℤ, a ∈ N → b ∈ N → a ≠ (0,0) → b ≠ (0,0) → a ⊗ b ≠ p

/-- Containment Lemma (a): for any n ∈ N, (q,q) ⊗ n ∈ clopenEnv q.
    Proof: π₁((q,q)⊗n) = q ⊛ n.1, so φ(q) | φ(q ⊛ n.1) = φ(q)·φ(n.1),
    giving π₁ ∈ q + φ(q)ℤ. Similarly for π₂. -/
theorem containment (q : ℤ) (n : ℤ × ℤ) (hn : n ∈ N) :
    (q, q) ⊗ n ∈ clopenEnv q := by
  simp [clopenEnv, otimes, mstar, sstar]
  -- (q ⊛ n.1) = q + (6q+1)*n.1, (q ⋆ n.2) = q + (6q-1)*n.2
  exact ⟨n.1, n.2, by constructor <;> ring⟩

/-- Identity excluded (b): e = (0,0) ∉ clopenEnv q when q ≠ 0.
    Proof: 0 ∈ q + (6q+1)ℤ requires (6q+1) | q, but |6q+1| > |q| for all q ≠ 0. -/
theorem identity_not_in_env (q : ℤ) (hq : q ≠ 0) :
    (0 : ℤ × ℤ) ∉ clopenEnv q := by
  simp [clopenEnv]
  intro a b h
  -- h.1: 0 = q + (6q+1)*a → q = -(6q+1)*a
  have h1 : q = -(6*q+1)*a := by linarith [h.1]
  -- If a = 0 then q = 0, contradiction. If a ≠ 0 then |6q+1| ≤ |q| / |a| ≤ |q|.
  rcases eq_or_ne a 0 with rfl | ha
  · simp at h1; exact hq h1
  · have : (6*q+1)^2 * a^2 = q^2 := by nlinarith
    nlinarith [sq_nonneg (6*q+1), sq_nonneg a, sq_nonneg q,
              Int.sq_nonneg a, mul_self_nonneg (6*q+1)]

-- ── §3: Clopenness in the subspace topology ──────────────────

/-- N ∩ clopenEnv q is clopen in N (subspace topology from ℤ²).
    This follows from clopenEnv_isClopen and the definition of the subspace topology. -/
theorem cosetEnv_isClopen_in_N (q : ℤ) (hq_ne : q ≠ 0) :
    IsClopen ((N : Set (ℤ × ℤ)) ∩ clopenEnv q) := by
  exact (clopenEnv_isClopen q hq_ne).inter_left _

/-- The coset (q,q)⊗N is contained in N ∩ clopenEnv q -/
theorem cosetN_subset_env (q : ℤ) :
    (fun p => (q,q) ⊗ p) '' (N : Set (ℤ × ℤ)) ⊆ (N : Set (ℤ × ℤ)) ∩ clopenEnv q := by
  intro p ⟨n, hn, rfl⟩
  exact ⟨N.mul_mem (Δ_mem_N q) hn, containment q n hn⟩

-- ── §4: Infinitude ───────────────────────────────────────────

/-- q̂ ⊗ N is infinite (left multiplication by q̂ is injective) -/
theorem cosetN_infinite (q : ℤ) (hq : IsIrred (q, q)) :
    ((fun p => (q,q) ⊗ p) '' (N : Set (ℤ × ℤ))).Infinite := by
  apply Set.infinite_image_of_injective
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp [otimes] at h
  obtain ⟨h1, h2⟩ := h
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
  exact Set.infinite_range_of_injective (fun a b h => by simp [Δ] at h; exact h) |>.mono
    (Set.range_subset_iff.mpr Δ_mem_N)

end TPC
