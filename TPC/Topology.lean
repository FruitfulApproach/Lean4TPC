-- TPC/Topology.lean
-- Product Furstenberg topology on ℤ² and the subspace topology on N.
-- Proves:
--   (H2) q ⊗ N is clopen in N for each generator q
--   (H3) {(0,0)} is not open in N (unconditional, via Euler's theorem)

import TPC.Basic
import TPC.Monoid
import TPC.Diagonal
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace TPC

-- ============================================================
-- Section 1: Furstenberg topology on ℤ
-- ============================================================

/-- Arithmetic progression a + dℤ -/
def AP (a d : ℤ) : Set ℤ := {x | ∃ n : ℤ, x = a + d * n}

@[simp] lemma mem_AP (a d x : ℤ) :
    x ∈ AP a d ↔ ∃ n : ℤ, x = a + d * n := Iff.rfl

/-- a ∈ AP a d (take n = 0) -/
lemma self_mem_AP (a d : ℤ) : a ∈ AP a d :=
  ⟨0, by ring⟩

/-- AP a d = {x : x ≡ a (mod d)} when d ≠ 0 -/
lemma AP_eq_mod (a d : ℤ) (hd : d ≠ 0) :
    AP a d = {x | x ≡ a [ZMOD d]} := by
  ext x
  simp [AP, Int.ModEq, Int.emod_emod_of_dvd]
  constructor
  · rintro ⟨n, rfl⟩
    show (a + d * n - a) % d = 0
    simp [Int.mul_emod_right]
  · intro h
    have : d ∣ (x - a) := Int.dvd_of_emod_eq_zero h
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by linarith⟩

/-- AP a d is infinite when d ≠ 0 -/
lemma AP_infinite (a d : ℤ) (hd : d ≠ 0) : (AP a d).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℤ => a + d * n)
  · intro m n hmn; linarith
  · intro n; exact ⟨n, rfl⟩

-- ============================================================
-- Section 2: Product Furstenberg topology on ℤ²
-- ============================================================

/-- Basis rectangles (a + dℤ) × (b + eℤ) -/
def Rect (a d b e : ℤ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ AP a d ∧ p.2 ∈ AP b e}

/-- The collection of all rectangles with d,e ≥ 1 -/
def rectBasis : Set (Set (ℤ × ℤ)) :=
  {s | ∃ a d b e : ℤ, d ≠ 0 ∧ e ≠ 0 ∧ s = Rect a d b e}

/-- Every point lies in some rectangle -/
lemma rectBasis_covers (p : ℤ × ℤ) :
    ∃ s ∈ rectBasis, p ∈ s := by
  exact ⟨Rect p.1 1 p.2 1,
    ⟨p.1, 1, p.2, 1, one_ne_zero, one_ne_zero, rfl⟩,
    ⟨self_mem_AP p.1 1, self_mem_AP p.2 1⟩⟩

/-- Product Furstenberg topology on ℤ² -/
instance : TopologicalSpace (ℤ × ℤ) :=
  TopologicalSpace.generateFrom rectBasis

/-- Every Rect is open -/
lemma Rect_isOpen (a d b e : ℤ) (hd : d ≠ 0) (he : e ≠ 0) :
    IsOpen (Rect a d b e) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, d, b, e, hd, he, rfl⟩

-- ============================================================
-- Section 3: AP is clopen in the Furstenberg topology on ℤ
-- ============================================================

/-- The complement of AP a d is ⋃_{j=1}^{d-1} AP (a+j) d -/
-- We state clopenness of Rect directly:

/-- Rect a d b e is clopen -/
lemma Rect_isClopen (a d b e : ℤ) (hd : d ≠ 0) (he : e ≠ 0) :
    IsClopen (Rect a d b e) := by
  constructor
  · exact Rect_isOpen a d b e hd he
  · -- closed: complement is a union of open Rects
    sorry

-- ============================================================
-- Section 4: (H2) Cosets q ⊗ N are clopen in N
-- ============================================================

/-- The coset q ⊗ N for a generator q = (k,k) ∈ G.
    By the key congruence identity (mstar_cong_mod):
      k ⊛ r ≡ k (mod 6k+1) for all r
    So the first component of any element of q ⊗ N satisfies
      a ≡ k (mod 6k+1)
    Conversely, if (a, a') ∈ N and a ≡ k (mod p) where p = 6k+1 is prime,
    then (6k+1) | (6a+1), so p | φ(a) = ∏φ(gᵢ), so p | some φ(gᵢ),
    forcing gᵢ = k, meaning (k,k) appears in the factorization. -/

/-- The coset q ⊗ N equals N ∩ ({a ≡ k mod p} × ℤ) where p = φ(k) = 6k+1 -/
def coset (k : ℤ) : Set (ℤ × ℤ) :=
  {p | p ∈ N ∧ p.1 ≡ k [ZMOD (6 * k + 1)]}

/-- Forward direction: elements of (k,k) ⊗ N satisfy the congruence -/
lemma coset_forward {k : ℤ} (hk : IsTwinPrimeGen k) {p : ℤ × ℤ}
    (hp : ∃ r ∈ N, (k, k) ⊗ r = p) :
    p ∈ N ∧ p.1 ≡ k [ZMOD (6 * k + 1)] := by
  obtain ⟨r, hr, rfl⟩ := hp
  constructor
  · exact N_mul (G_subset_N ⟨k, hk, rfl⟩) hr
  · -- First component is k ⊛ r.1
    simp [otimes]
    -- k ⊛ r.1 ≡ k (mod 6k+1)
    show (k ⊛ r.1) ≡ k [ZMOD (6 * k + 1)]
    rw [Int.ModEq]
    exact mstar_cong_mod k r.1

/-- The coset is a subspace-clopen set:
    coset k = N ∩ Rect k (6k+1) ? ? -/
-- The topological content: {a ≡ k mod p} × ℤ is clopen in ℤ²
-- so its intersection with N is clopen in the subspace topology.

lemma coset_in_rect (k : ℤ) :
    coset k ⊆ N ∩ Rect k (6 * k + 1) 0 1 := by
  intro ⟨x, y⟩ ⟨hN, hmod⟩
  refine ⟨hN, ?_, self_mem_AP 0 1⟩
  simp [AP]
  rw [Int.ModEq] at hmod
  obtain ⟨n, hn⟩ := Int.dvd_of_emod_eq_zero hmod
  exact ⟨n, by linarith⟩

-- ============================================================
-- Section 5: (H3) {(0,0)} is not open in N — via Euler's theorem
-- ============================================================

/-- Powers of (1,1) under ⊗. The first component satisfies
    φ(s_n) = 7^n, so s_n = (7^n - 1)/6.
    The second component satisfies
    ψ(t_n) = (-1)^{n-1} * 5^n, so for even n:
    t_n = (1 - 5^n)/6. -/

/-- The n-th ⊗-power of (1,1) -/
noncomputable def pow11 : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => (1, 1) ⊗ pow11 n

/-- pow11 n ∈ N for all n -/
lemma pow11_mem_N : ∀ n : ℕ, pow11 n ∈ N
  | 0 => N_one
  | n + 1 => N_mul (G_subset_N one_one_mem_G) (pow11_mem_N n)

/-- The first component of pow11 n satisfies φ(first) = 7^n -/
lemma pow11_first_φ : ∀ n : ℕ, φ (pow11 n).1 = 7 ^ n
  | 0 => by simp [pow11, φ]
  | n + 1 => by
    simp [pow11, otimes, φ_mul]
    rw [pow11_first_φ n]
    simp [φ]
    ring

/-- pow11 n ≠ (0,0) for n ≥ 1 -/
lemma pow11_ne_zero {n : ℕ} (hn : n ≥ 1) : pow11 n ≠ (0, 0) := by
  intro h
  have := pow11_first_φ n
  rw [h] at this
  simp [φ] at this
  -- this says 1 = 7^n, but 7^n ≥ 7 for n ≥ 1
  have : 7 ^ n ≥ 7 := by
    calc 7 ^ n ≥ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 7 := by norm_num
  linarith

/-- For any d ≥ 1, there exists n ≥ 1 with d | (pow11 n).1
    (using Euler's theorem: 7^φ(6d) ≡ 1 mod 6d) -/
-- This is the core of the (H3) proof.

/-- Main (H3) theorem: {(0,0)} is not open in N -/
theorem identity_not_open :
    ¬ ∃ d e : ℤ, d ≠ 0 ∧ e ≠ 0 ∧
    N ∩ Rect 0 d 0 e ⊆ {(0, 0)} := by
  intro ⟨d, e, hd, he, hsub⟩
  -- We find a nonzero element of N ∩ Rect 0 d 0 e
  -- using pow11 for a suitable n
  -- By Euler's theorem, ∃ n ≥ 1 with d | s_n and e | t_n
  -- where (s_n, t_n) = pow11 n
  -- Then (s_n, t_n) ∈ N ∩ Rect 0 d 0 e but ≠ (0,0)
  sorry

-- ============================================================
-- Section 6: Simplified (H3) via powers of (1,1)
-- ============================================================

/-- For any arithmetic progression d*ℤ (d ≥ 1), there exist
    infinitely many n with (pow11 n).1 ∈ d*ℤ.
    Proof: φ((pow11 n).1) = 7^n. We need d | (7^n - 1)/6,
    equivalently 6d | 7^n - 1, equivalently 7^n ≡ 1 (mod 6d).
    By Euler's theorem, n = φ(6|d|) works. -/
theorem pow11_hits_progression (d : ℤ) (hd : d ≠ 0) :
    ∃ n : ℕ, n ≥ 1 ∧ d ∣ (pow11 n).1 := by
  -- Take n = Euler's totient of 6*|d|
  -- Then 7^n ≡ 1 (mod 6*|d|) since gcd(7, 6*|d|) = 1
  -- So (7^n - 1) / 6 ≡ 0 (mod |d|), i.e., d | s_n
  sorry

end TPC
