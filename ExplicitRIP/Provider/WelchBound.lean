/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.Welch.Basic
import ExplicitRIP.Frozen.FramePotential

/-!
# Proof of [KM, (3)]: the Welch bound

Source: [KM, Section 1, (3)].

The frame-potential lower bound and coherence upper bound control the squared Welch ratio. For
`n ≥ 2` unit vectors in `ℂ^m`, `μ ≥ √((n - m)/(m(n - 1)))`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.welch_bound :
    ∀ (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → 2 ≤ n →
      Real.sqrt (((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) - 1))) ≤ ExplicitRIP.coherence Φ :=
by
  intro m n Φ hunit hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnsub : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hnR]
  have henergy := (ExplicitRIP.frame_potential_bound m n Φ hunit).2.trans
    (ExplicitRIP.Welch.sum_norm_sq_gram_error_le m n Φ hunit (by omega))
  have hcancel : ((n : ℝ) - m) / m ≤ ((n : ℝ) - 1) * ExplicitRIP.coherence Φ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hnpos).mp
    simpa only [mul_div_assoc, mul_assoc] using henergy
  apply (Real.sqrt_le_left (ExplicitRIP.RIPOneTwo.coherence_nonneg Φ)).mpr
  rw [← div_div]
  apply (div_le_iff₀ hnsub).mpr
  simpa only [mul_comm] using hcancel
