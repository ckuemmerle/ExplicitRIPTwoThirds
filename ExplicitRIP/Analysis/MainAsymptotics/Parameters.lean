/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Parameters for the main RIP families

The logarithmic translate count and sparsity choices have the required scalar growth rates
independently of a matrix estimate.

Source: [KM, proof of Theorem 1].
-/

public section

open Filter

namespace ExplicitRIP.MainAsymptotics

theorem primes_three_mod_four_infinite :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h := Nat.infinite_setOfPred_prime_and_modEq
    (q := 4) (a := 3) (by norm_num) (by norm_num)
  exact h.mono fun p hp => ⟨hp.1, hp.2⟩

theorem card_initial_segment (p L : ℕ) [Fact p.Prime] (hL : L ≤ p) :
    ((Finset.range L).image fun t : ℕ => (t : ZMod p)).card = L := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le ha hL),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le hb hL)] using h

theorem le_rpow_two_thirds_of_cube_le_sq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 3 ≤ b ^ 2) :
    a ≤ b ^ (2 / 3 : ℝ) := by
  have h' := Real.rpow_le_rpow (pow_nonneg ha 3) h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have ha' : (a ^ 3) ^ (1 / 3 : ℝ) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hb' : (b ^ 2) ^ (1 / 3 : ℝ) = b ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
    norm_num
  rwa [ha', hb'] at h'

theorem eventually_scalar_hyps (ε C : ℝ) :
    ∀ᶠ p : ℕ in atTop,
      2 ≤ p ∧ 1 / ε ≤ (p : ℝ) ∧
        2 * Real.log p ^ 6 ≤ (p : ℝ) ∧
        max (max 2 (1 / ε + 1)) (max (7 * C / ε) (64 / ε ^ 2)) ≤ Real.log p := by
  have hpoly : ∀ᶠ p : ℕ in atTop, 2 * Real.log p ^ 6 ≤ (p : ℝ) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero
    have h2 := h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
    have h4 := tendsto_natCast_atTop_atTop.eventually
      (h2.and (eventually_gt_atTop (0 : ℝ)))
    filter_upwards [h4] with p hp
    rcases hp with ⟨hp, hpos⟩
    simp only [one_mul, add_zero] at hp
    rw [div_lt_iff₀ hpos] at hp
    linarith
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / ε), hpoly,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max (max 2 (1 / ε + 1)) (max (7 * C / ε) (64 / ε ^ 2)))] with p hp hpε hpoly hlog
  exact ⟨hp, hpε, hpoly, hlog⟩

theorem parameter_bounds (p : ℕ) (hp : 2 ≤ p)
    (hpoly : 2 * Real.log p ^ 6 ≤ (p : ℝ)) (hlog : 2 ≤ Real.log p) :
    let L := ⌊Real.log p⌋₊
    let k := ⌊(p : ℝ) ^ 2 / Real.log p ^ 6⌋₊
    1 ≤ L ∧ L ≤ p ∧ 1 ≤ k ∧ k ≤ p ^ 2 ∧
      ((p : ℝ) ^ 2 / Real.log p ^ 6) / 2 ≤ (k : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hl0 : 0 < Real.log p := by linarith
  have hl1 : 1 ≤ Real.log p := by linarith
  have hd : 1 ≤ Real.log p ^ 6 := one_le_pow₀ hl1
  have hK : 2 * (p : ℝ) ≤ (p : ℝ) ^ 2 / Real.log p ^ 6 := by
    apply (le_div_iff₀ (pow_pos hl0 6)).2
    nlinarith only [mul_le_mul_of_nonneg_left hpoly hp0.le]
  have hK0 : 0 ≤ (p : ℝ) ^ 2 / Real.log p ^ 6 := by positivity
  have hKp : (p : ℝ) ^ 2 / Real.log p ^ 6 ≤ (p : ℝ) ^ 2 :=
    div_le_self (sq_nonneg _) hd
  refine ⟨Nat.le_floor (by norm_num; linarith),
    Nat.floor_le_of_le (Real.log_le_self hp0.le),
    Nat.le_floor (by norm_num; linarith), ?_, ?_⟩
  · apply Nat.floor_le_of_le
    exact_mod_cast hKp
  · have hf := Nat.sub_one_lt_floor ((p : ℝ) ^ 2 / Real.log p ^ 6)
    linarith

theorem row_bounds (p : ℕ) (hp : 2 ≤ p) :
    (p : ℝ) ≤ (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) ∧
      (p : ℝ) ^ 3 / 2 ≤ (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) ∧
      (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ 3 := by
  have hp1 : 1 ≤ p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  push_cast [Nat.cast_sub hp1]
  have hsq : 1 ≤ (p : ℝ) ^ 2 := by nlinarith only [hpR]
  constructor
  · nlinarith only [hpR, mul_nonneg (by linarith : (0 : ℝ) ≤ p - 2)
      (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)]
  constructor
  · nlinarith only [hpR, mul_nonneg (by linarith : (0 : ℝ) ≤ p - 2)
      (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)]
  · nlinarith only [hsq, hpR]

end ExplicitRIP.MainAsymptotics
