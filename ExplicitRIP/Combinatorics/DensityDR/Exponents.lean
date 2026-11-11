/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Normalization and exponent comparison for the density bound

Real-variable estimates compare the density exponents.

Source: [KM, proof of Lemma 3].
-/

public section

namespace ExplicitRIP.Dens

/-- Rewriting the averaged rectangle bound in its normalized power form. -/
theorem rectangle_bound_normalization (a b c β : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b / a * (2 * c * (2 * a) ^ β)) / Real.sqrt (a * b) =
      2 ^ (β + 1) * c * b ^ (1 / 2 : ℝ) * a ^ (β - 3 / 2) := by
  have hbhalf : b ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) = b := by
    rw [← Real.rpow_add hb]
    norm_num
  have haThree : a ^ (3 / 2 : ℝ) = a * a ^ (1 / 2 : ℝ) := by
    calc
      _ = a ^ (1 + (1 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add ha, Real.rpow_one]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_sub ha, haThree, Real.sqrt_mul ha.le,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have haHalf : a ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  have hbHalf : b ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  field_simp
  rw [← pow_two] at hbhalf
  ring_nf
  rw [hbhalf, mul_comm b c]

/-- The split at three halves yields the exponent appearing in the frozen statement. -/
theorem rectangle_exponent_bound (a b n β : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ n) :
    b ^ (1 / 2 : ℝ) * a ^ (β - 3 / 2) ≤ n ^ max (1 / 2 : ℝ) (β - 1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hn0 : 0 < n := hb0.trans_le hbn
  by_cases hβ : β ≤ 3 / 2
  · have haPow : a ^ (β - 3 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha (sub_nonpos.mpr hβ)
    have hmax : max (1 / 2 : ℝ) (β - 1) = 1 / 2 := max_eq_left (by linarith)
    rw [hmax]
    calc
      _ ≤ b ^ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left haPow (Real.rpow_nonneg hb0.le _)
      _ ≤ n ^ (1 / 2 : ℝ) := by
        rw [mul_one]
        exact Real.rpow_le_rpow hb0.le hbn (by norm_num)
  · have hβ' : 0 ≤ β - 3 / 2 := by linarith
    have hmax : max (1 / 2 : ℝ) (β - 1) = β - 1 := max_eq_right (by linarith)
    rw [hmax]
    calc
      _ ≤ n ^ (1 / 2 : ℝ) * n ^ (β - 3 / 2) :=
        mul_le_mul (Real.rpow_le_rpow hb0.le hbn (by norm_num))
          (Real.rpow_le_rpow ha0.le (hab.trans hbn) hβ')
          (Real.rpow_nonneg ha0.le _) (Real.rpow_nonneg hn0.le _)
      _ = n ^ (β - 1) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring

/-- The averaged inequality implies the final normalized rectangle estimate. -/
theorem normalized_rectangle_le (a b n c β S : ℝ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ n) (hc : 0 ≤ c) (hS : a * S ≤ b * (2 * c * (2 * a) ^ β)) :
    S / Real.sqrt (a * b) ≤ 2 ^ (β + 1) * c * n ^ max (1 / 2 : ℝ) (β - 1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hS' : S ≤ b / a * (2 * c * (2 * a) ^ β) := by
    calc
      S ≤ b * (2 * c * (2 * a) ^ β) / a :=
        (le_div_iff₀ ha0).mpr (by simpa only [mul_comm S a] using hS)
      _ = _ := by ring
  calc
    _ ≤ (b / a * (2 * c * (2 * a) ^ β)) / Real.sqrt (a * b) :=
      div_le_div_of_nonneg_right hS' (Real.sqrt_nonneg _)
    _ = 2 ^ (β + 1) * c * (b ^ (1 / 2 : ℝ) * a ^ (β - 3 / 2)) := by
      rw [rectangle_bound_normalization a b c β ha0 hb0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rectangle_exponent_bound a b n β ha hab hbn)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hc)

end ExplicitRIP.Dens
