/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LevDR.SubsetLog
public import Mathlib.Tactic.Ring

/-! Two applications of the all-subset estimate for an arbitrary complex kernel. -/

public section

open scoped BigOperators

/-- Rectangle estimates control arbitrary nonnegative coefficients on both sides. -/
theorem ExplicitRIP.Lev.nonneg_weighted_rectangle_log
    {I J : Type*} (G : I → J → ℂ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset I) (t : Finset J)
    (hrectangle : ∀ u : Finset I, u ⊆ s → ∀ v : Finset J, v ⊆ t →
      ‖∑ i ∈ u, ∑ j ∈ v, G i j‖ ≤
        (theta * Real.sqrt (u.card : ℝ)) * Real.sqrt (v.card : ℝ))
    (a : I → ℝ) (b : J → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ t, 0 ≤ b j) :
    ‖∑ i ∈ s, ∑ j ∈ t, (a i : ℂ) * (b j : ℂ) *
      G i j‖ ≤
      theta * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (1 + Real.log (t.card : ℝ)) *
        Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ j ∈ t, (b j) ^ 2) :=
by
  classical
  let Lt : ℝ := Real.sqrt (1 + Real.log (t.card : ℝ))
  let B2 : ℝ := Real.sqrt (∑ j ∈ t, (b j) ^ 2)
  let R : ℝ := theta * Lt * B2
  have hR : 0 ≤ R :=
    mul_nonneg (mul_nonneg htheta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hleft (u : Finset I) (hu : u ⊆ s) :
      ‖∑ i ∈ u, ∑ j ∈ t, (b j : ℂ) * G i j‖ ≤
        R * Real.sqrt (u.card : ℝ) := by
    have h := norm_nonneg_weighted_sum_le_log_of_subset_bounds
      t (fun j => ∑ i ∈ u, G i j) b
      (theta * Real.sqrt (u.card : ℝ))
      (mul_nonneg htheta (Real.sqrt_nonneg _)) hb (by
        intro v hv
        rw [Finset.sum_comm]
        exact hrectangle u hu v hv)
    simp only [Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    calc
      _ ≤ (theta * Real.sqrt (u.card : ℝ)) * Lt * B2 := h
      _ = R * Real.sqrt (u.card : ℝ) := by
        dsimp only [R]
        ring
  have h := norm_nonneg_weighted_sum_le_log_of_subset_bounds
    s (fun i => ∑ j ∈ t, (b j : ℂ) * G i j) a R hR ha hleft
  calc
    _ ≤ R * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (∑ i ∈ s, (a i) ^ 2) := by
      simpa only [Finset.mul_sum, ← mul_assoc] using h
    _ = theta * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (1 + Real.log (t.card : ℝ)) *
        Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ j ∈ t, (b j) ^ 2) := by
      dsimp only [R, Lt, B2]
      ring
