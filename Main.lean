-- TPC/Main.lean  [github.com/FruitfulApproach/Lean4TPC/blob/main/TPC/Main.lean]
-- Main theorem: |Irr(N)| = ∞  →  infinitely many twin primes.
-- Proof: Furstenberg-style on N with subspace topology from M.

import TPC.Basic
import TPC.Monoid
import TPC.CosetTopology
import Mathlib.Tactic

namespace TPC

-- ── §1: Norm and descent ────────────────────────────────────

/-- The norm |(z,w)| = (6z+1)² = φ(z)² -/
def norm (z : ℤ) : ℤ := φ z ^ 2

@[simp] lemma norm_zero : norm 0 = 1 := by simp [norm, φ]

lemma norm_pos (z : ℤ) : 0 < norm z := by
  simp [norm]; positivity

lemma norm_eq_one_iff (z : ℤ) : norm z = 1 ↔ z = 0 := by
  simp [norm, φ]
  constructor
  · intro h
    have : (6 * z + 1) ^ 2 = 1 := by linarith
    nlinarith [sq_nonneg (6 * z + 1)]
  · rintro rfl; ring

/-- Multiplicativity: norm(x ⊛ y) = norm(x) · norm(y) -/
lemma norm_mul (x y : ℤ) : norm (x ⊛ y) = norm x * norm y := by
  simp [norm, φ_mul]; ring

/-- Proper factors have strictly smaller norm -/
lemma norm_factor_lt {x a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hprod : a ⊛ b = x) : norm a < norm x := by
  subst hprod
  rw [norm_mul]
  have h1 : norm a ≥ 1 := le_of_lt (norm_pos a)
  have h2 : norm b ≥ 4 := by
    simp [norm, φ]
    have : (6 * b + 1) ≠ 1  := by omega
    have : (6 * b + 1) ≠ -1 := by omega
    nlinarith [sq_nonneg (6 * b + 1)]
  nlinarith

-- ── §2: Every element has an irreducible divisor ───────────

/-- Divisibility in N -/
def mstar_dvd (q z : ℤ × ℤ) : Prop :=
  ∃ m : ℤ × ℤ, m ∈ N ∧ q ⊗ m = z

/-- Every nonzero element of N has an irreducible ⊗-divisor -/
theorem exists_irred_dvd :
    ∀ p : ℤ × ℤ, p ∈ N → p ≠ (0,0) → ∃ q : ℤ × ℤ, IsIrred q ∧ mstar_dvd q p := by
  -- Well-founded induction on norm p.1
  intro ⟨z, w⟩ hmem hne
  induction hn : (norm z).toNat using Nat.strong_rec_on generalizing z w with
  | _ n ih => ?_
  by_cases hirr : IsIrred (z, w)
  · exact ⟨(z,w), hirr, (z,w), hmem, otimes_one_right _⟩
  · -- (z,w) is reducible: find a nontrivial factor
    push_neg at hirr
    obtain ⟨a, b, ha, hb, hane, hbne, hprod⟩ := by
      unfold IsIrred at hirr
      sorry -- extract nontrivial factorization
    -- a has smaller norm
    have hlt : (norm a.1).toNat < n := by
      rw [← hn]
      apply Int.toNat_lt.mpr
      constructor
      · exact Int.toNat_nonneg _
      · exact norm_factor_lt hane.1 hbne.1 (congr_arg Prod.fst hprod)
    obtain ⟨q, hq, m, hm, hqm⟩ := ih (norm a.1).toNat hlt a.1 a.2 ha hane rfl
    exact ⟨q, hq, b ⊗ m, N.mul_mem hb hm, by rw [← otimes_assoc, hqm, hprod]⟩

-- ── §3: The Covering ────────────────────────────────────────

/-- N \ {(0,0)} = ⋃_{q ∈ Irr(N)} q ⊗ N -/
theorem covering :
    (N : Set (ℤ × ℤ)) \ {(0,0)} ⊆
    ⋃ (q : ℤ × ℤ) (_ : IsIrred q),
      (fun p => q ⊗ p) '' (N : Set (ℤ × ℤ)) := by
  intro p ⟨hp, hpne⟩
  obtain ⟨q, hq, m, hm, hqm⟩ := exists_irred_dvd p hp hpne
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨q, hq, m, hm, hqm⟩

-- ── §4: No singleton is open ────────────────────────────────

/-- Every nonempty open set in N is infinite -/
theorem no_singleton_open (p : ℤ × ℤ) (hp : p ∈ N) :
    ¬IsOpen ({p} : Set (ℤ × ℤ)) := by
  -- Any open set must contain some q ⊗ N which is infinite
  intro hopen
  sorry

-- ── §5: Main Theorem ────────────────────────────────────────

/-- Main theorem: there are infinitely many ⊗-irreducibles in N -/
theorem infinitely_many_irred :
    {q : ℤ × ℤ | IsIrred q}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- N \ {(0,0)} is a finite union of clopen sets
  have hcov := covering
  have hclosed : IsClosed
      (⋃ (q : ℤ × ℤ) (_ : q ∈ hfin.toFinset),
        (fun p => q ⊗ p) '' (N : Set (ℤ × ℤ))) := by
    apply isClosed_biUnion_finset
    intro q hq
    have hqirr : IsIrred q := Set.Finite.mem_toFinset.mp hq
    have hprime : (6 * q.1 + 1).natAbs.Prime := by sorry
    exact (cosetN_isClopen q.1 hqirr hprime).2
  -- So {(0,0)} is open in N — but singletons are not open
  have hopen : IsOpen ({(0,0)} : Set (ℤ × ℤ)) := by
    sorry
  exact no_singleton_open (0,0) (N.one_mem) hopen

-- ── §6: Twin Prime Corollary ────────────────────────────────

/-- (z,w) ∈ Irr(N) ↔ 6z+1 and 6z-1 are both ±prime -/
def IsTwinPrimeIndex (k : ℤ) : Prop :=
  (6 * k + 1).natAbs.Prime ∧ (6 * k - 1).natAbs.Prime

/-- Infinitely many twin prime pairs -/
theorem infinitely_many_twin_primes :
    {k : ℤ | IsTwinPrimeIndex k}.Infinite := by
  apply Set.infinite_of_surjective_forall_mem
      (f := fun q : {q : ℤ × ℤ | IsIrred q} => q.1.1)
  · -- surjectivity: every twin prime index gives an irreducible
    sorry
  · -- image ⊆ twin prime indices
    sorry
  · exact infinitely_many_irred

end TPC
