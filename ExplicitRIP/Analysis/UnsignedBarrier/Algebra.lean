/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Sums

/-!
# Algebra and real powers in the unsigned barrier

Rearranging the energy bound gives the finite barrier and its sparsity consequences.

Source: [KM, proof of Theorem 4].
-/

public section

namespace ExplicitRIP.Absbar

theorem barrier_of_energy_bound (m n r D : ℝ) (hm : 0 < m) (hn : 1 < n)
    (hr : 0 < r)
    (h : n * (n - m) / m ≤ n * D ^ 2 + D / Real.sqrt r * (n * (n - 1) / r * D)) :
    (n - m) * r ^ (3 / 2 : ℝ) / (m * (n - 1 + r ^ (3 / 2 : ℝ))) ≤ D ^ 2 := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hR : 0 < r * Real.sqrt r := mul_pos hr hs
  have hden : 0 < m * (n - 1 + r * Real.sqrt r) :=
    mul_pos hm (add_pos (sub_pos.mpr hn) hR)
  have heq : n * D ^ 2 + D / Real.sqrt r * (n * (n - 1) / r * D) =
      n * D ^ 2 * (n - 1 + r * Real.sqrt r) / (r * Real.sqrt r) := by
    field_simp
    ring
  rw [heq] at h
  have hc := (div_le_div_iff₀ hm hR).mp h
  rw [Edges.rpow_three_halves r hr.le]
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_left₀ (show 0 < n by linarith)).mp
  convert hc using 1 <;> ring

theorem power_le_of_barrier (m n r D : ℝ) (hm : 0 < m) (hn : 1 < n)
    (hr : 0 < r) (hreg : 2 * (1 + D ^ 2) * m ≤ n)
    (h : (n - m) * r ^ (3 / 2 : ℝ) /
      (m * (n - 1 + r ^ (3 / 2 : ℝ))) ≤ D ^ 2) :
    r ^ (3 / 2 : ℝ) ≤ 2 * D ^ 2 * m := by
  have hR : 0 ≤ r ^ (3 / 2 : ℝ) := Real.rpow_nonneg hr.le _
  have hden : 0 < m * (n - 1 + r ^ (3 / 2 : ℝ)) :=
    mul_pos hm (add_pos_of_pos_of_nonneg (sub_pos.mpr hn) hR)
  have hc := (div_le_iff₀ hden).mp h
  have hp := mul_nonneg (sub_nonneg.mpr hreg) hR
  have hd := mul_nonneg (sq_nonneg D) hm.le
  apply (mul_le_mul_iff_left₀ (show 0 < n by linarith)).mp
  nlinarith only [hc, hp, hd]

/-- A useful uniform estimate in the small-aspect-ratio regime. -/
theorem sparsity_le_of_barrier (m n k D : ℝ) (hm : 0 < m) (hn : 1 < n)
    (hk : 2 ≤ k) (hreg : 2 * (1 + D ^ 2) * m ≤ n)
    (h : (n - m) * (k - 1) ^ (3 / 2 : ℝ) /
      (m * (n - 1 + (k - 1) ^ (3 / 2 : ℝ))) ≤ D ^ 2) :
    k ≤ (2 * (2 * D ^ 2) ^ (2 / 3 : ℝ)) * m ^ (2 / 3 : ℝ) := by
  have hr : 0 < k - 1 := by linarith
  have hp := power_le_of_barrier m n (k - 1) D hm hn hr hreg h
  have hp' := Real.rpow_le_rpow (Real.rpow_nonneg hr.le _) hp (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul hr.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num,
    Real.rpow_one, Real.mul_rpow (by positivity : 0 ≤ 2 * D ^ 2) hm.le] at hp'
  calc
    k ≤ 2 * (k - 1) := by linarith
    _ ≤ 2 * ((2 * D ^ 2) ^ (2 / 3 : ℝ) * m ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hp' (by norm_num)
    _ = _ := by ring

end ExplicitRIP.Absbar
