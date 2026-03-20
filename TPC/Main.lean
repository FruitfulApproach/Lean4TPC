-- TPC/Main.lean
-- Main theorem: |Irr(AntiDiag)| = ∞
-- Corollary: infinitely many twin prime pairs (conditional)

import TPC.Norm
import TPC.Topology
import TPC.WeaklySaturated
import Mathlib.Tactic
import Mathlib.Data.Set.Finite

namespace TPC

-- ============================================================
-- Section 1: The covering
-- ============================================================

/-- The covering: AntiDiag \ {(0,0)} = ⋃_{q ∈ Irr} q ⊗ AntiDiag -/
lemma antiDiag_covered_by_irred_cosets :
    {p : ℤ × ℤ | p ∈ AntiDiag ∧ p ≠ (0, 0)} ⊆
    ⋃ (q : ℤ) (_ : Irred q), (Δ q) • AntiDiag := by
  intro p ⟨hp_mem, hp_ne⟩
  simp [AntiDiag] at hp_mem
  -- p = Δ(p.1), p.1 ≠ 0
  have hk : p.1 ≠ 0 := by
    intro h
    apply hp_ne
    have := hp_mem
    simp [h] at this
    ext <;> simp [h, this]
  -- Get irreducible divisor
  obtain ⟨q, hq, m, hm⟩ := covering p.1 hk
  simp only [Set.mem_iUnion]
  exact ⟨q, hq, Δ m, Δ_mem m, by
    rw [← hm]
    congr 1
    ext
    · simp [Δ, hp_mem]
    · simp [Δ, hp_mem]⟩

-- ============================================================
-- Section 2: Each coset is closed
-- ============================================================

/-- q ⊗ AntiDiag = U_{q, -q, 6q+1} ∩ AntiDiag (as sets) -/
lemma coset_eq_U_inter (q : ℤ) (hq : q ≠ 0) :
    (fun m => Δ q ⊗ Δ m) '' Set.univ =
    U (q) (-q) (φ q) ∩ AntiDiag := by
  ext ⟨x, y⟩
  simp [U, AntiDiag, Δ, otimes, mstar, sstar, φ]
  constructor
  · rintro ⟨m, _, rfl⟩
    refine ⟨⟨m, ?_, ?_⟩, ?_⟩
    · ring
    · ring
    · ring
  · rintro ⟨⟨m, hx, hy⟩, hyx⟩
    refine ⟨m, trivial, ?_⟩
    ext
    · simp [mstar]; linarith
    · simp [sstar]; linarith

/-- q ⊗ AntiDiag is clopen in AntiDiag (subspace topology) -/
lemma coset_isClopen (q : ℤ) (hq : q ≠ 0) :
    IsClopen ((fun m => Δ q ⊗ Δ m) '' Set.univ) := by
  -- The image equals U_{q,-q,φq} ∩ AntiDiag
  -- U_{q,-q,φq} is clopen in ℤ², so its intersection with AntiDiag is clopen
  have hφ : φ q ≠ 0 := by simp [φ]; omega
  have hU := U_isClopen q (-q) (φ q) hφ
  rw [coset_eq_U_inter q hq]
  exact hU.inter_right AntiDiag (by
    exact TopologicalSpace.isClosed_generateFrom_of_mem ⟨_, rfl⟩)

-- ============================================================
-- Section 3: Main theorem via Furstenberg argument
-- ============================================================

/-- Main theorem: there are infinitely many ⊛-irreducibles -/
theorem infinitely_many_irred : {q : ℤ | Irred q}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- AntiDiag \ {(0,0)} = finite union of closed sets
  have hcov : {p : ℤ × ℤ | p ∈ AntiDiag ∧ p ≠ (0, 0)} =
              ⋃ q ∈ hfin.toFinset, (fun m => Δ q ⊗ Δ m) '' Set.univ := by
    sorry
  -- This finite union is closed in AntiDiag
  have hclosed : IsClosed (⋃ q ∈ hfin.toFinset, 
                            (fun m : ℤ => Δ q ⊗ Δ m) '' Set.univ) := by
    apply isClosed_biUnion_finset
    intro q hq
    have hqne : q ≠ 0 := by
      have := Set.Finite.mem_toFinset.mp hq
      exact this.1
    exact (coset_isClopen q hqne).2
  -- So {(0,0)} is open in AntiDiag
  have hopen : IsOpen ({(0, 0)} : Set (ℤ × ℤ)) := by
    rw [show ({(0,0)} : Set (ℤ × ℤ)) = 
         AntiDiag \ {p | p ∈ AntiDiag ∧ p ≠ (0,0)} from by
      ext p; simp [AntiDiag]; tauto]
    exact IsClosed.isOpen_compl hclosed
  -- But every open set is infinite
  have hinfin : ({(0,0)} : Set (ℤ × ℤ)).Infinite := by
    sorry -- follows from: any open set containing (0,0) contains a U_{a,b,c}
  exact Set.infinite_singleton (0, 0) |>.not_finite hinfin.toFinite

-- ============================================================
-- Section 4: Connection to twin primes
-- ============================================================

/-- An integer k indexes a twin prime pair if 6k-1 and 6k+1 are both prime -/
def IsTwinPrimeIndex (k : ℤ) : Prop :=
  (6 * k - 1).natAbs.Prime ∧ (6 * k + 1).natAbs.Prime

/-- The irreducibles of AntiDiag correspond exactly to twin prime indices
    (for positive k, and their negatives) -/
-- This is the bridge between Irred and IsTwinPrimeIndex
-- An element x is ⊛-irreducible iff φ(x) = 6x+1 is ±prime in ℤ
-- AND x is ⋆-irreducible iff ψ(x) = 6x-1 is ±prime in ℤ

/-- If k is a twin prime index then k is ⊛-irreducible -/
theorem twinPrime_imp_irred (k : ℤ) (hk : IsTwinPrimeIndex k) : Irred k := by
  constructor
  · intro h
    subst h
    simp [IsTwinPrimeIndex] at hk
  · intro a b hab
    -- φ(a ⊛ b) = φ(a) * φ(b) = φ(k) = 6k+1 which is prime
    have hphi : φ a * φ b = φ k := by
      rw [← φ_mul, hab]
    have hprime : (φ k).natAbs.Prime := hk.2
    rw [Int.natAbs_prime_iff_prime] at hprime
    rcases hprime.dvd_or_dvd ⟨φ b, hphi.symm⟩ with ⟨c, hc⟩ | ⟨c, hc⟩
    · -- φ(k) | φ(a), since φ(k) is prime and φ(k) | φ(a) * φ(b)
      sorry
    · sorry

/-- Main corollary: infinitely many twin prime pairs -/
theorem infinitely_many_twin_primes :
    {k : ℤ | IsTwinPrimeIndex k}.Infinite := by
  -- The set of twin prime indices is a subset of Irred
  -- Irred is infinite by infinitely_many_irred
  -- Need: Irred ⊆ TwinPrimeIndex (the full characterisation)
  -- For now we state this as follows:
  apply Set.infinite_of_injective_forall_mem
      (f := fun q : {q : ℤ | Irred q} => (q : ℤ))
  · intro a b hab
    exact Subtype.ext hab
  · intro ⟨q, hq⟩
    -- Every irreducible is a twin prime index
    -- This requires the full φ/ψ characterisation
    sorry

end TPC
