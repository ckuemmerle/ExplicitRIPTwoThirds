/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The spectral norm

Source: [KM, Sections 1 and 2.1, the norm ‖·‖_{2→2}].
-/

@[expose] public section

open scoped Matrix

/-- The spectral norm `‖M‖_op = ‖M‖_{2→2}` of a matrix `M ∈ 𝕜^{m × n}` with `𝕜 = ℝ` or `ℂ`: the
operator norm of `x ↦ M x` from `EuclideanSpace 𝕜 n` to `EuclideanSpace 𝕜 m`. This is
definitionally Mathlib's `L²` operator norm of matrices, `Matrix.l2_opNorm_def`, and
represents the norm used in [KM, Sections 1 and 2.1]. -/
noncomputable def ExplicitRIP.opNorm {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (M : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖
