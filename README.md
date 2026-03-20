# TPC — Twin Prime Conjecture via Weakly Saturated Submonoids

**[Homepage](https://fruitfulapproach.github.io/Lean4TPC/)**

A Lean 4 / Mathlib4 project formalising the algebraic approach to
the Twin Prime Conjecture developed in the companion paper.

## Structure

```
TPC/
├── lakefile.lean          -- Lake build configuration
├── lean-toolchain         -- Lean 4 version pin
├── TPC.lean               -- Root import file
└── TPC/
    ├── Basic.lean         -- Operations ⊛, ⋆, maps φ, ψ, η
    ├── Monoid.lean        -- CommMonoid instances; product monoid M
    ├── AntiDiagonal.lean  -- Δ(ℤ) = {(x,-x)}, closure, irred equivalence
    ├── WeaklySaturated.lean -- Abstract defn; proof N is WS, not saturated
    ├── Norm.lean          -- Norm |(x,-x)| = (6x+1)², axioms N1–N8
    ├── Topology.lean      -- U_{a,b,c} basis, clopen, topological monoid
    └── Main.lean          -- Main theorem + twin prime corollary
```

## Proof Status

| File | Status |
|------|--------|
| Basic.lean | Mostly complete; `mstar_no_zero_div` has `sorry` |
| Monoid.lean | Complete |
| AntiDiagonal.lean | Core lemmas complete; `weakSaturation` has `sorry` stubs |
| WeaklySaturated.lean | Abstract defn complete; counterexample complete |
| Norm.lean | N1–N7 complete; `exists_irred_dvd` needs well-founded induction |
| Topology.lean | Definitions complete; continuity proofs have `sorry` |
| Main.lean | Structure complete; Furstenberg argument has `sorry` stubs |

## Setup

```bash
# Install elan if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# In the TPC directory:
lake update
lake build
```

## Opening in VSCode

1. Install the **lean4** extension from the VSCode marketplace.
2. Open the `TPC` folder in VSCode.
3. Lake will automatically fetch Mathlib (this takes a while the first time).
4. Open any `.lean` file — the infoview shows goal states at each `sorry`.

## Key Mathematical Content

The main result is `TPC.Main.infinitely_many_irred`:

```
theorem infinitely_many_irred : {q : ℤ | Irred q}.Infinite
```

which via `TPC.Main.infinitely_many_twin_primes` gives infinitely many
twin prime pairs, conditional on the full characterisation
`Irred k ↔ IsTwinPrimeIndex k` (marked `sorry`, stated as `twinPrime_imp_irred`).

## The Core Argument

1. **`Basic.lean`**: φ(x⊛y) = φ(x)φ(y) — one `ring` tactic.
2. **`AntiDiagonal.lean`**: Δ(x)⊗Δ(y) = Δ(x⊛y) — one `ring` tactic.
3. **`WeaklySaturated.lean`**: counterexample (1,0)⊗(1,-8)=(8,-8) — `norm_num`.
4. **`Norm.lean`**: |(x,-x)⊗(y,-y)| = |(x,-x)|·|(y,-y)| — one `ring`.
5. **`Topology.lean`**: U_{a,b,c} clopen — complement is finite union of translates.
6. **`Main.lean`**: Furstenberg — finite Irr ⟹ {(0,0)} open ⟹ contradiction.

---

