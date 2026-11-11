/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.MainAsymptotics.Parameters

/-!
# Scalar estimates for the main RIP families

The decay and exponent estimates for the logarithmic parameter choices include the floor errors.

Source: [KM, proof of Theorem 1].
-/

public section

namespace ExplicitRIP.MainAsymptotics

theorem rip_expression_bound {x ℓ L k : ℝ} (hx : 0 < x)
    (hℓ : 2 ≤ ℓ) (hlog : Real.log x = ℓ)
    (hL : L ≤ ℓ) (hk1 : 1 ≤ k) (hk : k ≤ x ^ 2 / ℓ ^ 6) :
    2 * (L * Real.sqrt k * Real.log (2 * k) / x) + k / x ^ 2 ≤ 7 / ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hd1 : 1 ≤ ℓ ^ 6 := one_le_pow₀ hℓ1
  have hdℓ : ℓ ≤ ℓ ^ 6 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hℓ1 (by norm_num : 1 ≤ 6))
  have hkp : k ≤ x ^ 2 := hk.trans (div_le_self (sq_nonneg _) hd1)
  have hsqrtk : Real.sqrt k ≤ x / ℓ ^ 3 := by
    apply (Real.sqrt_le_left (by positivity)).2
    calc
      k ≤ x ^ 2 / ℓ ^ 6 := hk
      _ = (x / ℓ ^ 3) ^ 2 := by field_simp
  have hsqrt : L * Real.sqrt k ≤ x / ℓ ^ 2 := by
    calc
      L * Real.sqrt k ≤ ℓ * (x / ℓ ^ 3) :=
        mul_le_mul hL hsqrtk (Real.sqrt_nonneg _) hℓ0.le
      _ = x / ℓ ^ 2 := by field_simp
  have hlog0 : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith)
  have hlogk : Real.log (2 * k) ≤ 3 * ℓ := by
    calc
      Real.log (2 * k) ≤ Real.log (2 * x ^ 2) :=
        Real.log_le_log (by linarith) (by linarith only [hkp])
      _ = Real.log 2 + 2 * ℓ := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx.ne'), Real.log_pow, hlog]
        norm_num only [Nat.cast_ofNat]
      _ ≤ 3 * ℓ := by
        have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
  have hfirst : L * Real.sqrt k * Real.log (2 * k) / x ≤ 3 / ℓ := by
    calc
      L * Real.sqrt k * Real.log (2 * k) / x ≤
          (x / ℓ ^ 2) * (3 * ℓ) / x :=
        div_le_div_of_nonneg_right (mul_le_mul hsqrt hlogk hlog0 (by positivity)) hx.le
      _ = 3 / ℓ := by field_simp
  have hsecond : k / x ^ 2 ≤ 1 / ℓ := by
    calc
      k / x ^ 2 ≤ (x ^ 2 / ℓ ^ 6) / x ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith only [hk]
      _ = 1 / ℓ ^ 6 := by field_simp
      _ ≤ 1 / ℓ := one_div_le_one_div_of_le hℓ0 hdℓ
  calc
    _ ≤ 2 * (3 / ℓ) + 1 / ℓ :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond
    _ = 7 / ℓ := by ring

theorem sparsity_le_rpow {x ℓ k m : ℝ} (hx : 0 ≤ x) (hℓ : 2 ≤ ℓ)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ 2 / ℓ ^ 6) (hm : x ^ 3 / 2 ≤ m) :
    k ≤ m ^ (2 / 3 : ℝ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hd : (2 : ℝ) ≤ ℓ ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hℓ 6
    norm_num at h
    linarith
  have hhalf : k ≤ x ^ 2 / 2 :=
    hk.trans (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hd)
  have hm0 : 0 ≤ m := (by positivity : 0 ≤ x ^ 3 / 2).trans hm
  apply le_rpow_two_thirds_of_cube_le_sq hk0 hm0
  calc
    k ^ 3 ≤ (x ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hk0 hhalf 3
    _ ≤ (x ^ 3 / 2) ^ 2 := by nlinarith only [pow_nonneg hx 6]
    _ ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm 2

theorem log_ratio_bound {ε x ℓ k m : ℝ} (hε : 0 < ε) (hx : 1 < x)
    (hℓ : 2 ≤ ℓ) (hlarge : 64 / ε ^ 2 ≤ ℓ) (hlog : Real.log x = ℓ)
    (hk1 : 1 ≤ k) (hkhalf : (x ^ 2 / ℓ ^ 6) / 2 ≤ k)
    (hxm : x ≤ m) (hmp : m ≤ x ^ 3) (hkm : k ≤ m ^ (2 / 3 : ℝ)) :
    |Real.log k / Real.log m - 2 / 3| ≤ ε := by
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hk0 : 0 < k := by linarith
  have hm1 : 1 < m := hx.trans_le hxm
  have hm0 : 0 < m := by linarith
  have hB : 0 < Real.log m := Real.log_pos hm1
  have hA0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hBup : Real.log m ≤ 3 * ℓ := by
    have h := Real.log_le_log hm0 hmp
    simpa only [Real.log_pow, hlog, Nat.cast_ofNat] using h
  have hAup : Real.log k ≤ (2 / 3) * Real.log m := by
    have h := Real.log_le_log hk0 hkm
    rwa [Real.log_rpow hm0] at h
  have hAlow : 2 * ℓ - 6 * Real.log ℓ - Real.log 2 ≤ Real.log k := by
    have h := Real.log_le_log (by positivity : 0 < (x ^ 2 / ℓ ^ 6) / 2) hkhalf
    rw [Real.log_div (by positivity) (by norm_num),
      Real.log_div (pow_ne_zero _ hx0.ne') (pow_ne_zero _ hℓ0.ne'),
      Real.log_pow, Real.log_pow, hlog] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hs0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt ℓ := (Real.le_sqrt (by norm_num) hℓ0.le).2 (by nlinarith)
  have hss : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hsε : 8 / ε ≤ Real.sqrt ℓ := by
    apply (Real.le_sqrt (by positivity) hℓ0.le).2
    simpa only [div_pow, show (8 : ℝ) ^ 2 = 64 by norm_num] using hlarge
  have hsε' : 8 ≤ ε * Real.sqrt ℓ := by
    have h := (div_le_iff₀ hε).1 hsε
    linarith only [h]
  have hlogℓ : Real.log ℓ ≤ 2 * Real.sqrt ℓ := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.sqrt ℓ)
    rw [Real.log_sqrt hℓ0.le] at h
    linarith only [h]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have herr : 6 * Real.log ℓ + Real.log 2 ≤ 3 * ε * ℓ := by
    have hmul : 8 * Real.sqrt ℓ ≤ ε * ℓ := by
      calc
        8 * Real.sqrt ℓ ≤ (ε * Real.sqrt ℓ) * Real.sqrt ℓ :=
          mul_le_mul_of_nonneg_right hsε' hs0
        _ = ε * ℓ := by rw [mul_assoc, ← pow_two, hss]
    nlinarith only [hmul, hs1, hlogℓ, hlog2]
  have hlower : (2 / 3 - ε) * Real.log m ≤ Real.log k := by
    by_cases hsign : 0 ≤ (2 / 3 : ℝ) - ε
    · have h := mul_le_mul_of_nonneg_left hBup hsign
      nlinarith only [h, hAlow, herr]
    · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hB.le
      linarith only [h, hA0]
  apply abs_le.2
  constructor
  · have h := (le_div_iff₀ hB).2 hlower
    linarith only [h]
  · have h := (div_le_iff₀ hB).2 hAup
    linarith only [h, hε]

end ExplicitRIP.MainAsymptotics
