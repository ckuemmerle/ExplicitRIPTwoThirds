/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The induced 1-norm

Source: [KM, Section 2.1, the definition of the induced 1-norm].
-/

@[expose] public section

open scoped Matrix

/-- The induced `1`-norm `‖M‖_{1→1} = max_j ∑_i |M_{ij}|`, the maximal absolute column sum, as
defined at the start of [KM, Section 2.1]. -/
noncomputable def ExplicitRIP.oneToOneNorm {𝕜 : Type*} [RCLike 𝕜] {q : Type*} [Fintype q]
    (M : Matrix q q 𝕜) : ℝ :=
  ⨆ j : q, ∑ i : q, ‖M i j‖
