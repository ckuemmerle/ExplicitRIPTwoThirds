/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Contact of oriented spheres

Source: [KM, Section 4.1, footnote 1]; [Z, (1.1)].
-/

@[expose] public section

open scoped Matrix

/-- Contact of the oriented spheres `(x₁, y₁, z₁, r₁)` and `(x₂, y₂, z₂, r₂)` over a field `F`,
as in [Z, (1.1)]: `(x₁ - x₂)² + (y₁ - y₂)² + (z₁ - z₂)² = (r₁ - r₂)²`. For distinct vertices
over `𝔽_p`, with `p ≡ 3 (mod 4)`, this is adjacency in `VO₄⁻(p)`, as in
[KM, Section 4.1, footnote 1]. -/
def ExplicitRIP.SphereContact {F : Type*} [Field F] (S₁ S₂ : F × F × F × F) : Prop :=
  (S₁.1 - S₂.1) ^ 2 + (S₁.2.1 - S₂.2.1) ^ 2 + (S₁.2.2.1 - S₂.2.2.1) ^ 2 = (S₁.2.2.2 - S₂.2.2.2) ^ 2
