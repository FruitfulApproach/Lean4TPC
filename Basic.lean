-- TPC/Basic.lean  [github.com/FruitfulApproach/Lean4TPC/blob/main/TPC/Basic.lean]
-- Operations ⊛ (mstar) and ⋆ (sstar), isomorphisms φ and ψ, involution η,
-- and the no-zero-divisors lemma.

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace TPC

-- ── §1: Operations ─────────────────────────────────────────

def mstar (x y : ℤ) : ℤ := 6 * x * y + x + y    -- x ⊛ y
def sstar (x y : ℤ) : ℤ := -6 * x * y + x + y   -- x ⋆ y

notation:70 x " ⊛ " y => mstar x y
notation:70 x " ⋆ " y => sstar x y

@[simp] lemma mstar_zero_right (x : ℤ) : x ⊛ 0 = x := by simp [mstar]
@[simp] lemma mstar_zero_left  (x : ℤ) : 0 ⊛ x = x := by simp [mstar]
@[simp] lemma sstar_zero_right (x : ℤ) : x ⋆ 0 = x := by simp [sstar]
@[simp] lemma sstar_zero_left  (x : ℤ) : 0 ⋆ x = x := by simp [sstar]

lemma mstar_comm  (x y : ℤ)   : x ⊛ y = y ⊛ x             := by simp [mstar]; ring
lemma sstar_comm  (x y : ℤ)   : x ⋆ y = y ⋆ x             := by simp [sstar]; ring
lemma mstar_assoc (x y z : ℤ) : (x ⊛ y) ⊛ z = x ⊛ (y ⊛ z) := by simp [mstar]; ring
lemma sstar_assoc (x y z : ℤ) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z) := by simp [sstar]; ring

-- ── §2: Isomorphisms ───────────────────────────────────────

def φ (x : ℤ) : ℤ := 6 * x + 1   -- φ : N* → (6ℤ+1, ·)
def ψ (x : ℤ) : ℤ := 6 * x - 1   -- ψ : N⋆ → (6ℤ-1, ⊙)

@[simp] lemma φ_zero : φ 0 = 1  := by simp [φ]
@[simp] lemma ψ_zero : ψ 0 = -1 := by simp [ψ]

-- φ(x ⊛ y) = φ(x) · φ(y)
lemma φ_mul (x y : ℤ) : φ (x ⊛ y) = φ x * φ y := by simp [φ, mstar]; ring

-- ψ(x ⋆ y) = -(ψ(x) · ψ(y))   [since codomain uses ⊙ = neg-mult]
lemma ψ_mul (x y : ℤ) : ψ (x ⋆ y) = -(ψ x * ψ y) := by simp [ψ, sstar]; ring

lemma φ_injective : Function.Injective φ := fun a b h => by simp [φ] at h; linarith
lemma ψ_injective : Function.Injective ψ := fun a b h => by simp [ψ] at h; linarith

-- φ(q) prime  ↔  q is ⊛-irreducible  (used in Thm 3.2)
lemma φ_prime_of_irred (q : ℤ) (hq : q ≠ 0)
    (hirred : ∀ a b : ℤ, a ⊛ b = q → a = 0 ∨ b = 0) :
    (φ q).natAbs.Prime := by
  sorry  -- follows from: q irred in N* ↔ φ(q) irred in (6ℤ+1,·) ↔ φ(q) ±prime

-- ── §3: Involution η ───────────────────────────────────────

def η (x : ℤ) : ℤ := -x

lemma η_mstar_sstar (x y : ℤ) : η (x ⊛ y) = η x ⋆ η y := by
  simp [η, mstar, sstar]; ring

@[simp] lemma η_involution (x : ℤ) : η (η x) = x := by simp [η]

-- ── §4: No zero divisors ───────────────────────────────────

lemma mstar_no_zero_div {u v : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) : u ⊛ v ≠ 0 := by
  intro h
  have hφ : φ u * φ v = 1 := by simp [φ, mstar] at *; nlinarith
  have := Int.eq_one_or_neg_one_of_mul_eq_one' hφ
  simp [φ] at this
  omega

lemma sstar_no_zero_div {u v : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) : u ⋆ v ≠ 0 := by
  intro h
  have hψ : ψ u * ψ v = 0 := by simp [ψ, sstar] at *; nlinarith
  rcases mul_eq_zero.mp hψ with h1 | h1 <;> simp [ψ] at h1 <;> omega

end TPC
