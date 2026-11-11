/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Coordinates on `Herm₂(E)`, `E = 𝔽_p[i]`

The four base-field coordinates of a two-by-two Hermitian matrix provide an intermediate model
of the vertex space of `VO₄⁻(p)`. The sphere map sends `(a, b₁, b₂, c)` to
`(b₁, b₂, (a - c)/2, (a + c)/2)` in the contact coordinates of [KM, Section 4.1].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the Hermitian matrix `[[a, b₁ + i b₂], [b₁ - i b₂, c]] ∈
Herm₂(E)` with coordinates `x = (a, b₁, b₂, c) ∈ 𝔽_p⁴`, over the field `E = 𝔽_p[i]`,
`i² = -1`, realized as `QuadraticAlgebra (ZMod p) (-1) 0` (elements `⟨u, v⟩ = u + v i`; its `star`
is the conjugation `u + v i ↦ u - v i`). -/
def ExplicitRIP.hermitianMatrix (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    Matrix (Fin 2) (Fin 2) (QuadraticAlgebra (ZMod p) (-1) 0) :=
  !![⟨x.1, 0⟩, ⟨x.2.1, x.2.2.1⟩; ⟨x.2.1, -x.2.2.1⟩, ⟨x.2.2.2, 0⟩]
