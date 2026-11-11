/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.MainAsymptotics.Estimates
public import ExplicitRIP.Contact.Cholesky.Bounds

/-!
# Shared scalar conclusion for the main RIP families

The logarithmic parameters satisfy dimension growth, ratio decay, quantitative error decay, and
the sparsity exponent.

Source: [KM, proof of Theorem 1].
-/

public section

namespace ExplicitRIP.MainAsymptotics

theorem scalar_bounds (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (p : ℕ) [Fact p.Prime] (hp2 : 2 ≤ p) (hpε : 1 / ε ≤ (p : ℝ))
    (hpoly : 2 * Real.log p ^ 6 ≤ (p : ℝ))
    (hℓ : max (max 2 (1 / ε + 1)) (max (7 * C / ε) (64 / ε ^ 2)) ≤ Real.log p) :
    let L : ℕ := ⌊Real.log p⌋₊
    let k : ℕ := ⌊(p : ℝ) ^ 2 / Real.log p ^ 6⌋₊
    let m : ℕ := (p - 1) * (p ^ 2 + 1)
    1 ≤ L ∧ L ≤ p ∧ 1 ≤ k ∧ k ≤ p ^ 2 ∧
      1 / ε ≤ ((L * p ^ 3 : ℕ) : ℝ) ∧ 1 / ε ≤ (m : ℝ) ∧
      (m : ℝ) / (L * p ^ 3 : ℕ) ≤ ε ∧
      C * (ExplicitRIP.Actbar.largeEntry p * L * Real.sqrt k * Real.log (2 * k) +
        k * ExplicitRIP.Actbar.smallEntry p) ≤ ε ∧
      (k : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) ∧
      |Real.log k / Real.log m - 2 / 3| ≤ ε := by
  intro L k m
  rcases max_le_iff.1 hℓ with ⟨hℓa, hℓb⟩
  rcases max_le_iff.1 hℓa with ⟨hℓ2, hℓε⟩
  rcases max_le_iff.1 hℓb with ⟨hℓC, hℓlarge⟩
  obtain ⟨hL1, hLp, hk1, hkp, hkhalf⟩ := parameter_bounds p hp2 hpoly hℓ2
  obtain ⟨hpm, hmlo, hmhi⟩ := row_bounds p hp2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith only [hpR]
  have hℓ0 : 0 < Real.log p := by linarith only [hℓ2]
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) < L := by linarith only [hL1R]
  have hk1R : (1 : ℝ) ≤ k := by
    simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).2 (show 1 ≤ k from hk1)
  have hLlog : (L : ℝ) ≤ Real.log p := Nat.floor_le hℓ0.le
  have hkK : (k : ℝ) ≤ (p : ℝ) ^ 2 / Real.log p ^ 6 := Nat.floor_le (by positivity)
  have hLε : 1 / ε ≤ (L : ℝ) := by
    have h := Nat.sub_one_lt_floor (Real.log p)
    linarith only [h, hℓε]
  have hp3 : (p : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact le_self_pow₀ (by linarith only [hpR]) (by decide : 3 ≠ 0)
  have hn : 1 / ε ≤ ((L * p ^ 3 : ℕ) : ℝ) := by
    push_cast
    exact hpε.trans (hp3.trans (le_mul_of_one_le_left (by positivity) hL1R))
  have hm : 1 / ε ≤ (m : ℝ) := hpε.trans hpm
  have hmn : (m : ℝ) / (L * p ^ 3 : ℕ) ≤ ε := by
    push_cast
    calc
      (m : ℝ) / ((L : ℝ) * (p : ℝ) ^ 3) ≤
          (p : ℝ) ^ 3 / ((L : ℝ) * (p : ℝ) ^ 3) :=
        div_le_div_of_nonneg_right hmhi (by positivity)
      _ = 1 / (L : ℝ) := by field_simp
      _ ≤ ε := by
        apply (div_le_iff₀ hL0).2
        have h := (div_le_iff₀ hε).1 hLε
        linarith only [h]
  have hrip : C * (ExplicitRIP.Actbar.largeEntry p * L * Real.sqrt k * Real.log (2 * k) +
      k * ExplicitRIP.Actbar.smallEntry p) ≤ ε := by
    have hlogk : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith only [hk1R])
    have hX : 0 ≤ (L : ℝ) * Real.sqrt k * Real.log (2 * k) := by positivity
    have hcoeff := ExplicitRIP.Contact.Cholesky.gram_coeff_bounds p
    have happrox : ExplicitRIP.Actbar.largeEntry p * L * Real.sqrt k * Real.log (2 * k) +
        k * ExplicitRIP.Actbar.smallEntry p ≤
        2 * ((L : ℝ) * Real.sqrt k * Real.log (2 * k) / p) + k / (p : ℝ) ^ 2 := by
      have ha := mul_le_mul_of_nonneg_right hcoeff.1 hX
      have hb := mul_le_mul_of_nonneg_left hcoeff.2 (zero_le_one.trans hk1R)
      calc
        _ ≤ (2 / p) * ((L : ℝ) * Real.sqrt k * Real.log (2 * k)) +
            k * (1 / (p : ℝ) ^ 2) := by nlinarith only [ha, hb]
        _ = _ := by ring
    calc
      _ ≤ C * (2 * ((L : ℝ) * Real.sqrt k * Real.log (2 * k) / p) +
          k / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left happrox hC.le
      _ ≤ C * (7 / Real.log p) :=
        mul_le_mul_of_nonneg_left
          (rip_expression_bound hp0 hℓ2 rfl hLlog hk1R hkK) hC.le
      _ = (7 * C) / Real.log p := by ring
      _ ≤ ε := by
        have h := (div_le_iff₀ hε).1 hℓC
        apply (div_le_iff₀ hℓ0).2
        nlinarith only [h]
  have hk23 : (k : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) :=
    sparsity_le_rpow hp0.le hℓ2 (by positivity) hkK hmlo
  have hlog : |Real.log k / Real.log m - 2 / 3| ≤ ε :=
    log_ratio_bound hε (by linarith only [hpR]) hℓ2 hℓlarge rfl
      hk1R hkhalf hpm hmhi hk23
  exact ⟨hL1, hLp, hk1, hkp, hn, hm, hmn, hrip, hk23, hlog⟩

end ExplicitRIP.MainAsymptotics
