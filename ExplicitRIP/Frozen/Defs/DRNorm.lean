/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The discrete Rayleigh norm

Source: [KM, Section 2.1, the definition before (5)].
-/

@[expose] public section

open scoped Matrix

/-- The discrete Rayleigh norm `‖M‖_DR = max_{∅ ≠ I, J ⊆ [q]} |1_I^* M 1_J| / √(|I| |J|)`
defined before [KM, (5)]; the two sets are chosen independently. Here
`1_I^* M 1_J = ∑_{i ∈ I} ∑_{j ∈ J} M_{ij}`, and the index set `[q]` is any finite type. -/
noncomputable def ExplicitRIP.drNorm {𝕜 : Type*} [RCLike 𝕜] {q : Type*} [Fintype q]
    (M : Matrix q q 𝕜) : ℝ :=
  ⨆ IJ : {IJ : Finset q × Finset q // IJ.1.Nonempty ∧ IJ.2.Nonempty},
    ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, M i j‖ / Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)
