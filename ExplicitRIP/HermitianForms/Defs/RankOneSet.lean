/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.HermitianForms.Defs.HermitianMatrix

/-!
# The set `ℛ` of rank-one Hermitian matrices

These matrices are the neighbors of zero in the Hermitian-forms model of `VO₄⁻(p)`. Under the
sphere map they correspond to the nonzero isotropic vectors for the quadratic form of
[KM, Section 4.1].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the set `ℛ` of rank-one matrices in `Herm₂(E)`, in the
coordinates of `ExplicitRIP.hermitianMatrix`. -/
noncomputable def ExplicitRIP.rankOneSet (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  open Classical in
  Finset.univ.filter fun K => (ExplicitRIP.hermitianMatrix p K).rank = 1
