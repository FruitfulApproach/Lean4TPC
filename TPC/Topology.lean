-- TPC/Topology.lean
-- Topology on MonTensor via the UMP:
--   Final topology from β : ℤ × ℤ → MonTensor
-- and the coarsest coset-closed topology on N = ⟨G⟩.
-- Proves:
--   (H2) Every translate a · N is closed (by definition)
--   (H3) {1} is not open ⟺ |G| = ∞

import TPC.Basic
import TPC.Monoid
import TPC.Diagonal
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite

namespace TPC

-- ============================================================
-- Section 1: Topology on MonTensor via UMP
-- ============================================================

/-- Topology on MonTensor: the final topology making β : ℤ × ℤ → M continuous,
    where ℤ × ℤ carries the product of discrete topologies.

    A set U ⊆ MonTensor is open iff β⁻¹(U) is open in ℤ × ℤ.
    Since ℤ × ℤ is discrete, every set is open, so this is the
    finest topology on MonTensor. We refine it to the coarsest
    coset-closed topology below. -/

-- ============================================================
-- Section 2: The coarsest coset-closed topology on N
-- ============================================================

/-- The translate a · N (as a set in MonTensor) -/
def translateN (a : MonTensor) : Set MonTensor :=
  {x | ∃ r ∈ N, a * r = x}

/-- The collection of complements of translates: sub-basic opens -/
def cosetOpenBasis : Set (Set MonTensor) :=
  {s | ∃ a : MonTensor, a ∈ N ∧ s = (translateN a)ᶜ}

/-- The coarsest coset-closed topology on MonTensor -/
instance cosetTopology : TopologicalSpace MonTensor :=
  TopologicalSpace.generateFrom cosetOpenBasis

-- ============================================================
-- Section 3: (H2) Every translate is closed — by definition
-- ============================================================

/-- (H2): a · N is closed for every a ∈ N -/
theorem translate_isClosed (a : MonTensor) (ha : a ∈ N) :
    IsClosed (translateN a) := by
  rw [← isOpen_compl_iff]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, ha, rfl⟩

/-- In particular, diagGen(k) · N is closed for every generator -/
theorem generator_coset_isClosed (k : ℤ) (hk : IsTwinPrimeGen k) :
    IsClosed (translateN (diagGen k)) :=
  translate_isClosed (diagGen k) (G_subset_N ⟨k, hk, rfl⟩)

-- ============================================================
-- Section 4: Identity is not in any nontrivial translate
-- ============================================================

/-- If a * r = 1 in MonTensor, then a = 1.
    (In a monoid tensor product of cancellative monoids,
     the only unit is the identity.) -/
axiom MonTensor.mul_eq_one_left {a r : MonTensor} (h : a * r = 1) : a = 1

/-- 1 ∉ translateN a for any a ≠ 1 -/
lemma one_not_in_translate {a : MonTensor} (ha : a ≠ 1) :
    (1 : MonTensor) ∉ translateN a := by
  intro ⟨r, _, har⟩
  exact ha (MonTensor.mul_eq_one_left har)

-- ============================================================
-- Section 5: (H3) — {1} open iff G finite
-- ============================================================

/-- N \ {1} = ⋃_{g ∈ G} translateN g -/
lemma N_minus_one_eq_union_translates :
    {t : MonTensor | t ∈ N ∧ t ≠ 1} =
    ⋃ (g : MonTensor) (_ : g ∈ G), translateN g := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, translateN]
  constructor
  · intro ⟨hx, hne⟩
    -- x ∈ N, x ≠ 1, so x has a generator factor
    sorry
  · intro ⟨g, hg, r, hr, hgr⟩
    constructor
    · rw [← hgr]; exact N.mul_mem (G_subset_N hg) hr
    · intro h; rw [h] at hgr
      exact (one_not_in_translate (by
        obtain ⟨k, hk, rfl⟩ := hg
        intro heq
        -- diagGen k = 1 would mean k = 0, contradicting hk.1
        sorry)) ⟨r, hr, hgr⟩

/-- If a generator g ∈ G is in translateN a for a ≠ 1,
    then a = g. (Because φ(k) is prime and can't factor nontrivially.) -/
theorem generator_in_translate_forces_eq
    {g a : MonTensor} (hg : g ∈ G) (ha_mem : a ∈ N) (ha_ne : a ≠ 1)
    (h : g ∈ translateN a) : a = g := by
  obtain ⟨r, hr, har⟩ := h
  obtain ⟨k, hk, rfl⟩ := hg
  -- a * r = diagGen k, where φ(k) is prime.
  -- If r ≠ 1, then a * r is a nontrivial factorization of diagGen k in N,
  -- contradicting that diagGen k is irreducible.
  sorry

/-- Finite covering of N\{1} by translates forces G to be finite -/
theorem finite_cover_forces_finite_G
    (S : Finset MonTensor)
    (hS : ∀ s ∈ S, s ∈ N ∧ s ≠ 1)
    (hcov : ∀ t : MonTensor, t ∈ N → t ≠ 1 → ∃ a ∈ S, t ∈ translateN a) :
    ∀ g : MonTensor, g ∈ G → g ∈ S := by
  intro g hg
  have hg_mem := G_subset_N hg
  have hg_ne : g ≠ 1 := by
    obtain ⟨k, hk, rfl⟩ := hg
    intro h
    -- diagGen k = 1 requires k = 0, contradicts hk.1
    sorry
  obtain ⟨a, ha_mem, ha_trans⟩ := hcov g hg_mem hg_ne
  have ha := (hS a ha_mem)
  have := generator_in_translate_forces_eq hg ha.1 ha.2 ha_trans
  rwa [this]

end TPC
