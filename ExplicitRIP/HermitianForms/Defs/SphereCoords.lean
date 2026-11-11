/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Sphere coordinates on `Herm₂(E)`

The sphere map identifies the Hermitian-forms model of `VO₄⁻(p)` with the contact-coordinate
model of [KM, Section 4.1]. The determinant becomes `r² - x² - y² - z²`, so a nonzero rank-one
difference corresponds exactly to a contact edge.
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the sphere coordinates in [KM, Section 4.1] of a Hermitian
vertex: the vertex with coordinates `(a, b₁, b₂, c)` has
`(X, Y, Z, R) = (b₁, b₂, (a - c)/2, (a + c)/2)`. -/
def ExplicitRIP.sphereCoords (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (x : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (x.2.1, x.2.2.1, (x.1 - x.2.2.2) / 2, (x.1 + x.2.2.2) / 2)
