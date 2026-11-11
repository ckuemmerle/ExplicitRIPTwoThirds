/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.DRNorm

/-! The discrete Rayleigh norm bounds every rectangle, including empty rectangles. -/

public section

open scoped BigOperators Matrix

namespace ExplicitRIP.Lev

theorem dr_norm_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    0 ≤ ExplicitRIP.drNorm M := by
  apply Real.iSup_nonneg
  intro IJ
  exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem rectangle_sum_le_dr_norm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (s t : Finset ι) :
    ‖∑ i ∈ s, ∑ j ∈ t, M i j‖ ≤
      (ExplicitRIP.drNorm M * Real.sqrt (s.card : ℝ)) * Real.sqrt (t.card : ℝ) := by
  classical
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · let r : {IJ : Finset ι × Finset ι // IJ.1.Nonempty ∧ IJ.2.Nonempty} → ℝ :=
        fun IJ => ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, M i j‖ /
          Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)
      have h : ‖∑ i ∈ s, ∑ j ∈ t, M i j‖ /
          Real.sqrt ((s.card : ℝ) * t.card) ≤ ExplicitRIP.drNorm M :=
        le_ciSup (Finite.bddAbove_range r) ⟨(s, t), hs, ht⟩
      have hden : 0 < Real.sqrt ((s.card : ℝ) * t.card) :=
        Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hs.card_pos)
          (Nat.cast_pos.mpr ht.card_pos))
      have hb := (div_le_iff₀ hden).mp h
      rw [Real.sqrt_mul (Nat.cast_nonneg s.card)] at hb
      simpa only [mul_assoc] using hb
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
      simp only [Finset.sum_empty, Finset.sum_const_zero, norm_zero, Finset.card_empty,
        Nat.cast_zero, Real.sqrt_zero, mul_zero, le_refl]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.sum_empty, norm_zero, Finset.card_empty, Nat.cast_zero,
      Real.sqrt_zero, mul_zero, zero_mul, le_refl]

end ExplicitRIP.Lev
