/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The trace pairing on `Herm₂(E)`

The matrix trace of a product gives a symmetric nondegenerate bilinear pairing on the four
base-field coordinates of the Hermitian-forms model of `VO₄⁻(p)`.
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the trace pairing on Hermitian matrices: for
`H = (a, b₁, b₂, c)` and `K = (α, β₁, β₂, γ)` in the coordinates of `ExplicitRIP.hermitianMatrix`,
`tr(HK) = aα + 2(b₁β₁ + b₂β₂) + cγ ∈ 𝔽_p`. It is the trace of the product
(`ExplicitRIP.Trace.matrix_trace_mul`); as a bilinear form it is symmetric and nondegenerate
(`ExplicitRIP.Trace.form_isSymm`, `ExplicitRIP.Trace.form_nondegenerate`). -/
def ExplicitRIP.tracePairing (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (H K : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p :=
  H.1 * K.1 + 2 * (H.2.1 * K.2.1 + H.2.2.1 * K.2.2.1) + H.2.2.2 * K.2.2.2
