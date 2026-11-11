/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FieldNorm

/-!
# The selected vertex set `Γ_T` in Hermitian coordinates

This applies the norm-graph formula of [KM, (15)] to the coordinates `(a, b₁, b₂, c)` of the
Hermitian-forms model: `c = N(a, b₁, b₂) + t`. The sphere map sends this set to the light-cone
selection `r - z = N(r + z, x, y) + t`, `t ∈ T`. The selection of [KM, (15)] uses the norm graph
directly in contact coordinates.
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)` and `T ⊆ 𝔽_p`, the set `Γ_T = {(a, b₁, b₂, N(a, b₁, b₂) + t) : (a,
b₁, b₂) ∈ 𝔽_p³, t ∈ T}`, in the coordinates `(a, b₁, b₂, c)` of
`ExplicitRIP.hermitianMatrix`, where `N = ExplicitRIP.fieldNorm p`. -/
noncomputable def ExplicitRIP.hermitianSelectedVertices (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) :
    Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (Finset.univ ×ˢ T).image fun wt : (ZMod p × ZMod p × ZMod p) × ZMod p =>
    (wt.1.1, wt.1.2.1, wt.1.2.2,
      ExplicitRIP.fieldNorm p wt.1 + wt.2)
