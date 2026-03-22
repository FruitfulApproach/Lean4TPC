-- TPC/Topology.lean
-- Coarsest coset-closed topology on N = ⟨G⟩^⊗.
-- Proves:
--   (H2) Every translate a ⊗ N is closed (by definition)
--   (H3) {(0,0)} is not open ⟺ |G| = ∞

import TPC.Basic
import TPC.Monoid
import TPC.Diagonal
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite

namespace TPC

-- ============================================================
-- Section 1: The coarsest coset-closed topology on N
-- ============================================================

/-- The topology on ℤ × ℤ where every translate a ⊗ N is closed.
    This is the coarsest topology making {a ⊗ r | r ∈ N} closed
    for each a ∈ N.

    Equivalently: the sub-basic open sets are N \ (a ⊗ N) for a ≠ (0,0).
    We define this via TopologicalSpace.generateOpen on the complements. -/

/-- The translate a ⊗ N -/
def translateN (a : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {x | ∃ r ∈ N, a ⊗ r = x}

/-- The collection of complements of translates: sub-basic opens -/
def cosetOpenBasis : Set (Set (ℤ × ℤ)) :=
  {s | ∃ a : ℤ × ℤ, a ∈ N ∧ s = (translateN a)ᶜ}

/-- The coarsest coset-closed topology -/
instance cosetTopology : TopologicalSpace (ℤ × ℤ) :=
  TopologicalSpace.generateFrom cosetOpenBasis

-- ============================================================
-- Section 2: (H2) Every translate is closed — by definition
-- ============================================================

/-- (H2): a ⊗ N is closed for every a ∈ N -/
theorem translate_isClosed (a : ℤ × ℤ) (ha : a ∈ N) :
    IsClosed (translateN a) := by
  rw [← isOpen_compl_iff]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, ha, rfl⟩

/-- In particular, g ⊗ N is closed for every generator g ∈ G -/
theorem generator_coset_isClosed (g : ℤ × ℤ) (hg : g ∈ G) :
    IsClosed (translateN g) :=
  translate_isClosed g (G_subset_N hg)

-- ============================================================
-- Section 3: Identity is not in any nontrivial translate
-- ============================================================

/-- a ⊗ r = (0,0) implies a = (0,0) -/
lemma otimes_eq_zero_left {a r : ℤ × ℤ} (h : a ⊗ r = (0, 0)) :
    a = (0, 0) := by
  have h1 : a.1 ⊛ r.1 = 0 := congr_arg Prod.fst h
  have h2 : a.2 ⋆ r.2 = 0 := congr_arg Prod.snd h
  -- φ(a.1) * φ(r.1) = φ(0) = 1
  have hφ : φ a.1 * φ r.1 = 1 := by
    have := φ_mul a.1 r.1; rw [h1, φ_zero] at this; linarith
  -- φ(x) = 6x+1 = ±1 gives x = 0 or x = -1/3
  have : φ a.1 = 1 ∨ φ a.1 = -1 :=
    Int.isUnit_iff.mp (IsUnit.of_mul_eq_one (φ r.1) hφ)
  have ha1 : a.1 = 0 := by simp [φ] at this; omega
  -- Similarly for second component via ψ
  have hψ : ψ a.2 * ψ r.2 = 1 := by
    have := ψ_mul a.2 r.2; rw [h2, ψ_zero] at this; linarith
  have : ψ a.2 = 1 ∨ ψ a.2 = -1 :=
    Int.isUnit_iff.mp (IsUnit.of_mul_eq_one (ψ r.2) hψ)
  have ha2 : a.2 = 0 := by simp [ψ] at this; omega
  exact Prod.ext ha1 ha2

/-- (0,0) ∉ translateN a for any a ≠ (0,0) -/
lemma zero_not_in_translate {a : ℤ × ℤ} (ha : a ≠ (0, 0)) :
    (0, 0) ∉ translateN a := by
  intro ⟨r, _, har⟩
  exact ha (otimes_eq_zero_left har)

-- ============================================================
-- Section 4: (H3) — {(0,0)} open iff N\{e} is a finite
--            union of translates iff G is finite
-- ============================================================

/-- N \ {(0,0)} = ⋃_{g ∈ G} translateN g -/
lemma N_minus_zero_eq_union_translates :
    {p : ℤ × ℤ | p ∈ N ∧ p ≠ (0, 0)} =
    ⋃ (g : ℤ × ℤ) (_ : g ∈ G), translateN g := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, translateN]
  constructor
  · intro ⟨hx, hne⟩
    obtain ⟨g, hg, r, hr, hgr⟩ := N_divisible_by_gen hx hne
    exact ⟨g, hg, r, hr, hgr⟩
  · intro ⟨g, hg, r, hr, hgr⟩
    constructor
    · rw [← hgr]; exact N_mul (G_subset_N hg) hr
    · intro h; rw [h] at hgr
      have := otimes_eq_zero_left hgr
      simp [G, IsTwinPrimeGen] at hg
      obtain ⟨k, ⟨hk, _, _⟩, rfl⟩ := hg
      simp [Prod.ext_iff] at this
      exact hk this.1

/-- If a generator g = (m,m) ∈ G is in translateN a for a ≠ (0,0),
    then a = g. (Because φ(m) is prime and can't factor nontrivially.) -/
theorem generator_in_translate_forces_eq
    {g a : ℤ × ℤ} (hg : g ∈ G) (ha_mem : a ∈ N) (ha_ne : a ≠ (0, 0))
    (h : g ∈ translateN a) : a = g := by
  obtain ⟨r, hr, har⟩ := h
  obtain ⟨m, hm, rfl⟩ := hg
  -- a ⊗ r = (m, m), so a.1 ⊛ r.1 = m
  have h1 : a.1 ⊛ r.1 = m := congr_arg Prod.fst har
  -- φ(a.1) * φ(r.1) = φ(m), which is ±prime
  have hφ_prod : φ a.1 * φ r.1 = φ m := by rw [← φ_mul, h1]
  have hprime := gen_φ_prime hm  -- (φ m).natAbs.Prime
  -- |φ(a.1)| * |φ(r.1)| = |φ(m)| (prime)
  have habs : (φ a.1).natAbs * (φ r.1).natAbs = (φ m).natAbs := by
    rw [← Int.natAbs_mul, hφ_prod]
  -- a ≠ (0,0), so by no-zero-component, a.1 ≠ 0
  -- hence |φ(a.1)| ≥ 5
  -- If r ≠ (0,0), then r.1 ≠ 0 (by no-zero-component if r ∈ N),
  -- so |φ(r.1)| ≥ 5, product ≥ 25, but |φ(m)| is prime → contradiction
  -- So r = (0,0), hence a = g
  sorry

/-- Finite covering of N\{e} by translates forces G to be finite -/
theorem finite_cover_forces_finite_G
    (S : Finset (ℤ × ℤ))
    (hS : ∀ s ∈ S, s ∈ N ∧ s ≠ (0, 0))
    (hcov : ∀ p : ℤ × ℤ, p ∈ N → p ≠ (0, 0) → ∃ a ∈ S, p ∈ translateN a) :
    ∀ g : ℤ × ℤ, g ∈ G → g ∈ S := by
  intro g hg
  have hg_mem := G_subset_N hg
  have hg_ne : g ≠ (0, 0) := by
    intro h; rw [h] at hg; simp [G, IsTwinPrimeGen] at hg
  obtain ⟨a, ha_mem, ha_trans⟩ := hcov g hg_mem hg_ne
  have ha := (hS a ha_mem)
  have := generator_in_translate_forces_eq hg ha.1 ha.2 ha_trans
  rwa [this]

end TPC
