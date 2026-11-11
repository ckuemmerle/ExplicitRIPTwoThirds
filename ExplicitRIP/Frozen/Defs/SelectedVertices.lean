/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FieldNorm

/-!
# The selected vertex set

Source: [KM, Section 4.2, (15), and footnote 3].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)` and `T ⊆ 𝔽_p`, the set
`V'_T = {(c, N(c) + t) : c ∈ 𝔽_p³, t ∈ T}` of [KM, (15)], written in the vertex coordinates
`(x, y, z, r)` with `c = (x, y, z)`. These are the `L = |T|` translates `r = N(c) + t` of
the graph of the field norm `N = ExplicitRIP.fieldNorm p` of `𝔽_{p³}/𝔽_p`, in the power
basis of the lexicographically first monic irreducible cubic, as in [KM, footnote 3]. -/
noncomputable def ExplicitRIP.selectedVertices (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) : Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (Finset.univ ×ˢ T).image fun ct : (ZMod p × ZMod p × ZMod p) × ZMod p =>
    (ct.1.1, ct.1.2.1, ct.1.2.2, ExplicitRIP.fieldNorm p ct.1 + ct.2)
