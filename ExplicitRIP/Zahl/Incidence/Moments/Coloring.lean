/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Counting.Coloring
public import ExplicitRIP.Zahl.Incidence.Sampling.Colors

/-! # Second and fractional moments of uniform color samples -/

public section

namespace ExplicitRIP.Zahl

open Classical in
/-- The second moment includes both diagonal and distinct coordinate pairs. -/
theorem mean_colorSample_card_sq {α : Type*} (L : Finset α) (k : ℕ)
    (hk : 0 < k) :
    finiteMean (Finset.univ : Finset (↥L → Fin k))
      (fun χ => ((colorSample L χ).card : ℝ) ^ 2) =
        (L.card : ℝ) / (k : ℝ) +
          (L.card : ℝ) * ((L.card : ℝ) - 1) / (k : ℝ) ^ 2 := by
  classical
  have h₂ : Finset.expect (Finset.univ : Finset (↥L → Fin k))
      (fun χ => ((colorSample L χ).card : ℝ) * (((colorSample L χ).card : ℝ) - 1)) =
        (L.card : ℝ) * ((L.card : ℝ) - 1) * (1 / (k : ℝ) ^ 2) := by
    simpa only [colorSample, Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_attach] using
      Sampling.expect_card_filter_factorial L.attach Finset.univ
        (fun (χ : ↥L → Fin k) a => (χ a).val = 0) (1 / (k : ℝ) ^ 2)
        (fun a _ b _ hab => Sampling.expect_two_zero_colors k hk a b hab)
  calc
    _ = finiteMean Finset.univ (fun χ : ↥L → Fin k =>
        ((colorSample L χ).card : ℝ) +
          ((colorSample L χ).card : ℝ) * (((colorSample L χ).card : ℝ) - 1)) := by
      apply Finset.expect_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [finiteMean, Finset.expect_add_distrib, h₂,
        ← finiteMean, mean_colorSample_card L k hk]
      ring

open Classical in
/-- Cauchy--Schwarz bounds the fractional sample-size moment. -/
theorem mean_colorSample_card_three_halves {α : Type*} (L : Finset α) (k : ℕ)
    (hk : 0 < k) (hkn : k ≤ L.card) :
    finiteMean (Finset.univ : Finset (↥L → Fin k))
      (fun χ => ((colorSample L χ).card : ℝ) ^ (3 / 2 : ℝ)) ≤
        2 * ((L.card : ℝ) / (k : ℝ)) ^ (3 / 2 : ℝ) := by
  classical
  let μ : ℝ := (L.card : ℝ) / (k : ℝ)
  let X (χ : ↥L → Fin k) : ℝ := (colorSample L χ).card
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
  have hμ : 1 ≤ μ := (one_le_div hkR).mpr (by exact_mod_cast hkn)
  have hμ0 : 0 ≤ μ := le_trans zero_le_one hμ
  have hrpow (x : ℝ) (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = Real.sqrt x * x := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (↥L → Fin k)) (fun χ => Real.sqrt (X χ)) X
  have hsqrt (χ : ↥L → Fin k) : Real.sqrt (X χ) ^ 2 = X χ :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  simp_rw [hsqrt] at hcs
  change (finiteMean Finset.univ (fun χ => Real.sqrt (X χ) * X χ)) ^ 2 ≤
    finiteMean Finset.univ X * finiteMean Finset.univ (fun χ => X χ ^ 2) at hcs
  have hfirst : finiteMean Finset.univ X = μ := mean_colorSample_card L k hk
  rw [hfirst] at hcs
  have hdiag : (L.card : ℝ) * ((L.card : ℝ) - 1) / (k : ℝ) ^ 2 ≤ μ ^ 2 := by
    dsimp [μ]
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [hnR]
  have hsecond : finiteMean Finset.univ (fun χ => X χ ^ 2) ≤ 2 * μ ^ 2 := by
    have heq := mean_colorSample_card_sq L k hk
    change finiteMean Finset.univ (fun χ => X χ ^ 2) =
      μ + (L.card : ℝ) * ((L.card : ℝ) - 1) / (k : ℝ) ^ 2 at heq
    nlinarith only [heq, hdiag, mul_nonneg hμ0 (sub_nonneg.mpr hμ)]
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hsecond hμ0)
  have hsq : (Real.sqrt μ * μ) ^ 2 = μ ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hμ0]
    ring
  have hroot : finiteMean Finset.univ (fun χ => Real.sqrt (X χ) * X χ) ≤
      2 * (Real.sqrt μ * μ) := by
    have hnonneg : 0 ≤ Real.sqrt μ * μ := mul_nonneg (Real.sqrt_nonneg _) hμ0
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg)
    nlinarith only [hbound, hsq, sq_nonneg (Real.sqrt μ * μ)]
  calc
    _ = finiteMean Finset.univ (fun χ => Real.sqrt (X χ) * X χ) := by
      apply Finset.expect_congr rfl
      intro χ _
      exact hrpow _ (Nat.cast_nonneg _)
    _ ≤ 2 * (Real.sqrt μ * μ) := hroot
    _ = 2 * μ ^ (3 / 2 : ℝ) := by rw [hrpow μ hμ0]

end ExplicitRIP.Zahl
