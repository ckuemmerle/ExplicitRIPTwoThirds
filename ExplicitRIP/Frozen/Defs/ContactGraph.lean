/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The elliptic affine polar graph

Source: [KM, Sections 3 and 4.1, footnote 1].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the elliptic affine polar graph `VO₄⁻(p)` of
[KM, Sections 3 and 4.1]. Its vertices are the points `(x, y, z, r)` of `V = 𝔽_p³ × 𝔽_p`,
with `c = (x, y, z)`, and distinct `u, v` are adjacent when `Q(u - v) = 0`, where
`Q(c, r) = c · c - r²`. -/
def ExplicitRIP.contactGraph (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    SimpleGraph (ZMod p × ZMod p × ZMod p × ZMod p) :=
  SimpleGraph.fromRel fun u v =>
    (u - v).1 ^ 2 + (u - v).2.1 ^ 2 + (u - v).2.2.1 ^ 2 - (u - v).2.2.2 ^ 2 = 0
