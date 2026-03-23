-- TPC/AntiDiagonal.lean
-- Legacy file: the anti-diagonal embedding Δ(x) = (x, -x)
-- is now subsumed by the diagonal submonoid N = ⟨{k ⊗ k}⟩ ⊆ MonTensor.
--
-- In the tensor product formulation:
--   - The "anti-diagonal" Δ(x) = (x, -x) in ℤ² corresponds to
--     diagGen(x) = MonTensor.mk x x in MonTensor.
--   - The key identity Δ(x) ⊗ Δ(y) = Δ(x ⊛ y) becomes:
--     diagGen(x) * diagGen(y) is a product in N (by closure).
--   - Irreducibility in N decomposes via bilinearity (see Monoid.lean).
--
-- This file is kept for reference but is no longer imported.

import TPC.Basic
import TPC.Monoid

namespace TPC

-- The anti-diagonal in ℤ² is no longer the primary object.
-- See TPC.Monoid for diagGen and N.

end TPC
