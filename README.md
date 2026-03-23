# TPC — Twin Prime Conjecture via Coset Topologies on Monoid Tensor Products

**[Homepage](https://fruitfulapproach.github.io/Lean4TPC/)**

A Lean 4 / Mathlib4 project formalising the algebraic approach to
the Twin Prime Conjecture developed in the companion paper.

## Website

The formal proof is hosted on GitHub Pages:

- **Homepage**: <https://fruitfulapproach.github.io/Lean4TPC/>
- **Proof viewer** (TPC.html): <https://fruitfulapproach.github.io/Lean4TPC/TPC.html>

## Structure

```
TPC/
├── lakefile.lean          -- Lake build configuration
├── lean-toolchain         -- Lean 4 version pin
├── TPC.lean               -- Root import file
└── TPC/
    ├── Basic.lean         -- Operations ⊛, ⋆, maps φ, ψ, η
    ├── Monoid.lean        -- MonTensor = (ℤ,⊛) ⊗_Mon (ℤ,⋆), diagGen, N
    ├── Diagonal.lean      -- Twin-prime-indexed generators
    ├── Norm.lean          -- Norm function, well-founded descent
    ├── Topology.lean      -- UMP topology, coset-closed topology
    └── Main.lean          -- Main theorem + twin prime corollary
```

## Proof Status

| File | Status |
|------|--------|
| Basic.lean | Mostly complete; `mstar_no_zero_div` has `sorry` |
| Monoid.lean | Axiomatized MonTensor with bilinearity relations |
| Diagonal.lean | Twin-prime-indexed generators |
| Norm.lean | Norm axioms; `exists_irred_dvd` needs well-founded induction |
| Topology.lean | UMP topology definitions; continuity proofs have `sorry` |
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
2. **`Monoid.lean`**: MonTensor with bilinearity: mk(a⊛b, w) = mk(a,w)·mk(b,w).
3. **`Norm.lean`**: ‖k⊗k‖ = (6k+1)² multiplicative — one `ring`.
4. **`Topology.lean`**: UMP final topology from β: ℤ×ℤ → M, cosets clopen.
5. **`Main.lean`**: Furstenberg — finite Irr(N) ⟹ {e} open ⟹ contradiction.

---
