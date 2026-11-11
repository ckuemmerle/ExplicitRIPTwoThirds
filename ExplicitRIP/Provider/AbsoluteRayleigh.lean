/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.DRNorm

/-!
# Proof of [KM, (7)]: absolute values and the discrete Rayleigh norm

Source: [KM, Section 2.2, (7)].

The triangle inequality on each rectangle proves `‖M‖_DR ≤ ‖|M|‖_DR`, with absolute values taken
entrywise.
-/

public section

open scoped BigOperators Matrix

/-- Taking entrywise absolute values can only increase the discrete Rayleigh norm. -/
theorem ExplicitRIP.Provider.drNorm_le_drNorm_abs :
    ∀ {𝕜 : Type} [RCLike 𝕜] (ι : Type) [Fintype ι] (M : Matrix ι ι 𝕜),
      ExplicitRIP.drNorm M ≤ ExplicitRIP.drNorm (M.map fun z => ‖z‖) := by
  intro 𝕜 _ ι _ M
  classical
  unfold ExplicitRIP.drNorm
  refine ciSup_mono (Finite.bddAbove_range _) fun IJ => ?_
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  change ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, M i j‖ ≤
    ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, ‖M i j‖‖
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => norm_nonneg (M i j))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
