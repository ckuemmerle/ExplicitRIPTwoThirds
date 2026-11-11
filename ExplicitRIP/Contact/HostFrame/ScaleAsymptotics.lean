/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame

/-!
# Frame parameters at the host-dimension scale

The host dimension lies between `(p - 1)³` and `p³`. Taking cube roots bounds the two
frame parameters at the dimension scale by the same reciprocal error as at the prime scale.
-/

public section

namespace ExplicitRIP.Contact.HostFrame

theorem scale_error_bounds (x : ℝ) (hx : 2 ≤ x) :
    let m := (x - 1) * (x ^ 2 + 1)
    let μ := (x ^ 2 - x + 1) / m
    let ν := 1 / (x ^ 2 + 1)
    |μ * m ^ (1 / 3 : ℝ) - 1| ≤ 2 / x ∧
      |ν * m ^ (2 / 3 : ℝ) - 1| ≤ 2 / x := by
  intro m μ ν
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 0 ≤ x - 1 := by linarith only [hx]
  have hm0 : 0 ≤ m := mul_nonneg hx1 (by positivity)
  have hmlo : (x - 1) ^ 3 ≤ m := by
    dsimp [m]
    nlinarith only [mul_nonneg hx1 hx0.le]
  have hmhi : m ≤ x ^ 3 := by
    dsimp [m]
    nlinarith only [sq_nonneg (x - 1)]
  have hroot (a : ℝ) (ha : 0 ≤ a) :
      (a ^ 3) ^ (1 / 3 : ℝ) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hroot2 (a : ℝ) (ha : 0 ≤ a) :
      (a ^ 3) ^ (2 / 3 : ℝ) = a ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h₁lo : x - 1 ≤ m ^ (1 / 3 : ℝ) := by
    simpa only [hroot _ hx1] using
      Real.rpow_le_rpow (pow_nonneg hx1 3) hmlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h₁hi : m ^ (1 / 3 : ℝ) ≤ x := by
    simpa only [hroot _ hx0.le] using
      Real.rpow_le_rpow hm0 hmhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h₂lo : (x - 1) ^ 2 ≤ m ^ (2 / 3 : ℝ) := by
    simpa only [hroot2 _ hx1] using
      Real.rpow_le_rpow (pow_nonneg hx1 3) hmlo (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have h₂hi : m ^ (2 / 3 : ℝ) ≤ x ^ 2 := by
    simpa only [hroot2 _ hx0.le] using
      Real.rpow_le_rpow hm0 hmhi (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hμ : 0 ≤ μ := div_nonneg (by nlinarith only [sq_nonneg (x - 1)]) hm0
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hq : 0 < x ^ 2 + 1 := by positivity
  have hx1pos : 0 < x - 1 := by linarith only [hx]
  have hloμ : 1 - 2 / x ≤ μ * (x - 1) := by
    have he : μ * (x - 1) = 1 - x / (x ^ 2 + 1) := by
      dsimp [μ, m]
      field_simp
      ring
    have hdiv : x / (x ^ 2 + 1) ≤ 2 / x := by
      apply (div_le_div_iff₀ hq hx0).mpr
      nlinarith only [sq_nonneg x]
    rw [he]
    linarith only [hdiv]
  have hloν : 1 - 2 / x ≤ ν * (x - 1) ^ 2 := by
    have he : ν * (x - 1) ^ 2 = 1 - (2 * x) / (x ^ 2 + 1) := by
      dsimp [ν]
      field_simp
      ring
    have hdiv : (2 * x) / (x ^ 2 + 1) ≤ 2 / x := by
      apply (div_le_div_iff₀ hq hx0).mpr
      nlinarith only []
    rw [he]
    linarith only [hdiv]
  obtain ⟨hμerr, hνerr, _⟩ := ExplicitRIP.HostFrame.parameter_error_bounds x hx
  have hdiv : 1 / x ≤ 2 / x :=
    div_le_div_of_nonneg_right (by norm_num) hx0.le
  have hμup : μ * x ≤ 1 + 2 / x := by
    have h := (abs_le.mp hμerr).2
    change x * μ - 1 ≤ 1 / x at h
    nlinarith only [h, hdiv]
  have hνup : ν * x ^ 2 ≤ 1 + 2 / x := by
    have h := (abs_le.mp hνerr).2
    change x ^ 2 * ν - 1 ≤ 1 / x at h
    nlinarith only [h, hdiv]
  constructor
  · apply abs_le.mpr
    constructor
    · linarith only [hloμ.trans (mul_le_mul_of_nonneg_left h₁lo hμ)]
    · linarith only [(mul_le_mul_of_nonneg_left h₁hi hμ).trans hμup]
  · apply abs_le.mpr
    constructor
    · linarith only [hloν.trans (mul_le_mul_of_nonneg_left h₂lo hν)]
    · linarith only [(mul_le_mul_of_nonneg_left h₂hi hν).trans hνup]

/-- The dimension `m = (x - 1)(x² + 1)` satisfies `|m / x³ - 1| ≤ 1 / x` for `x ≥ 2`; with `x = p`
this is `m ∼ p³`. -/
theorem dimension_ratio_error (x : ℝ) (hx : 2 ≤ x) :
    |(x - 1) * (x ^ 2 + 1) / x ^ 3 - 1| ≤ 1 / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx3 : 0 < x ^ 3 := by positivity
  have he : (x - 1) * (x ^ 2 + 1) / x ^ 3 - 1 = -((x ^ 2 - x + 1) / x ^ 3) := by
    field_simp
    ring
  rw [he, abs_neg, abs_of_nonneg (div_nonneg (by nlinarith only [hx]) hx3.le)]
  apply (div_le_div_iff₀ hx3 hx0).mpr
  nlinarith only [hx]

end ExplicitRIP.Contact.HostFrame
