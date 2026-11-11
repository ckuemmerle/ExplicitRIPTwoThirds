/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Threshold arithmetic for degree reduction

The scale `1536 * (M + 1)` turns the degree bound `768 * n / A` into
all three hypotheses needed by popular-component selection and trapping.
-/

public section

namespace ExplicitRIP.GuthZahl.Structure

theorem degree_reduction_thresholds (M n d p : ℕ) (hM : 1 ≤ M) (hn : 0 < n)
    (hnp : n ≤ p ^ 2) (A : ℝ) (hA : 0 < A)
    (hscale : 1536 * ((M : ℝ) + 1) * Real.sqrt n ≤ A)
    (hdegree : (d : ℝ) ≤ 768 * n / A) :
    d < p ∧ 2 * M * d ^ 2 ≤ n ∧ ((2 * M * d : ℕ) : ℝ) ≤ A := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hsq := Real.sq_sqrt hnR.le
  have hproduct : (1536 * ((M : ℝ) + 1) * Real.sqrt n) * d ≤ 768 * n := by
    calc
      _ ≤ A * d := mul_le_mul_of_nonneg_right hscale hdR
      _ = (d : ℝ) * A := mul_comm _ _
      _ ≤ _ := (le_div_iff₀ hA).mp hdegree
  have hscaled : 2 * ((M : ℝ) + 1) * d ≤ Real.sqrt n := by
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith only [hproduct, hsq]
  have htwo : 2 * (d : ℝ) ≤ Real.sqrt n := by
    have hcoeff : 2 * (d : ℝ) ≤ 2 * ((M : ℝ) + 1) * d :=
      mul_le_mul_of_nonneg_right (by linarith only [hMR]) hdR
    exact hcoeff.trans hscaled
  have hsmall : (d : ℝ) < Real.sqrt n := by
    linarith only [htwo, hs]
  have hsp : Real.sqrt (n : ℝ) ≤ p :=
    Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg p, by exact_mod_cast hnp⟩
  have hmd : 2 * (M : ℝ) * d ≤ Real.sqrt n := by
    apply le_trans _ hscaled
    exact mul_le_mul_of_nonneg_right (by linarith) hdR
  have hsA : Real.sqrt (n : ℝ) ≤ A := by
    apply le_trans _ hscale
    have hcoeff : (1 : ℝ) ≤ 1536 * ((M : ℝ) + 1) := by linarith only [hMR]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff hs.le
  refine ⟨by exact_mod_cast hsmall.trans_le hsp, ?_, ?_⟩
  · have hbound := mul_le_mul hmd hsmall.le hdR hs.le
    have hreal : 2 * (M : ℝ) * (d : ℝ) ^ 2 ≤ n := by
      nlinarith only [hbound, hsq]
    exact_mod_cast hreal
  · exact_mod_cast hmd.trans hsA

end ExplicitRIP.GuthZahl.Structure

end
