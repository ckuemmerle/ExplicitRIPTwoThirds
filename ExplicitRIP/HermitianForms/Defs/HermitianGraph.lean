/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.HermitianForms.Defs.HermitianMatrix

/-!
# The Hermitian forms graph

The Hermitian-forms model of `VO₄⁻(p)` has vertex set `Herm₂(𝔽_p[i])`; distinct matrices are
adjacent when their difference has rank one. The sphere map identifies this adjacency with the
contact relation in the coordinates `(x, y, z, r)` of [KM, Section 4.1].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the Hermitian-forms model of `VO₄⁻(p)` on `Herm₂(E)`, in the
coordinates of `ExplicitRIP.hermitianMatrix`: distinct `H, K` are adjacent when `rank(H - K) = 1`
(the rank over `E = 𝔽_p[i]`). -/
def ExplicitRIP.hermitianGraph (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    SimpleGraph (ZMod p × ZMod p × ZMod p × ZMod p) :=
  SimpleGraph.fromRel fun x y =>
    (ExplicitRIP.hermitianMatrix p x - ExplicitRIP.hermitianMatrix p y).rank = 1
