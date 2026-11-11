/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Layer counting and square-root summation

Layer counting and reciprocal-square-root summation control the rich-pencil contribution to
the edge count without logarithmic loss.
-/

public section
namespace ExplicitRIP.Edges
open Finset

/-- A square is bounded by the sum of the even layers up to its side length. -/
theorem sq_le_sum_layers (k : ℕ) : k ^ 2 ≤ ∑ i ∈ range k, 2 * (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    nlinarith

theorem sq_le_sum_layers_of_le {k M : ℕ} (hk : k ≤ M) :
    k ^ 2 ≤ ∑ i ∈ range M, if i < k then 2 * (i + 1) else 0 := by
  apply (sq_le_sum_layers k).trans
  have he : ∑ i ∈ range k, 2 * (i + 1) =
      ∑ i ∈ range k, if i < k then 2 * (i + 1) else 0 := by
    apply sum_congr rfl
    intro i hi
    rw [ite_eq_left (mem_range.mp hi)]
  rw [he]
  exact sum_le_sum_of_subset (range_mono hk)

/-- The layer-cake bound for a finite family of richness values. -/
theorem sum_sq_le_layers {β : Type*} (P : Finset β) (k : β → ℕ) (M : ℕ)
    (hk : ∀ b ∈ P, k b ≤ M) :
    ∑ b ∈ P, (k b) ^ 2 ≤
      ∑ i ∈ range M, 2 * (i + 1) * (P.filter (fun b => i + 1 ≤ k b)).card := by
  classical
  apply (sum_le_sum fun b hb => sq_le_sum_layers_of_le (hk b hb)).trans
  rw [sum_comm]
  apply le_of_eq
  apply sum_congr rfl
  intro i _
  simp only [card_eq_sum_ones, mul_sum, sum_filter]
  apply sum_congr rfl
  intro b _
  simp only [Nat.lt_iff_add_one_le, mul_ite, mul_one, mul_zero]

/-- The discrete reciprocal-square-root sum has no logarithmic loss. -/
theorem sum_one_div_sqrt_le (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / Real.sqrt (i + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hs := Real.sqrt_nonneg (n : ℝ)
    have ht := Real.sqrt_pos.mpr hn1
    have hst : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
    have hs2 := Real.sq_sqrt hn
    have ht2 := Real.sq_sqrt hn1.le
    have hstep : (1 : ℝ) / Real.sqrt (n + 1) ≤
        2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
      apply (div_le_iff₀ ht).mpr
      have hsq := sq_nonneg (Real.sqrt (n + 1) - Real.sqrt n)
      nlinarith
    push_cast
    linarith

/-- Conversion between the fixed exponent and the square-root form. -/
theorem rpow_three_halves (s : ℝ) (hs : 0 ≤ s) :
    s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
  calc
    s ^ (3 / 2 : ℝ) = s ^ (1 + (1 / 2 : ℝ)) := by congr 1; norm_num
    _ = s * Real.sqrt s := by
      rw [Real.rpow_add_of_nonneg hs (by norm_num) (by norm_num), Real.rpow_one,
        Real.sqrt_eq_rpow]

theorem mul_rpow_neg_three_halves (s : ℝ) (hs : 0 < s) :
    s * s ^ (-(3 / 2 : ℝ)) = 1 / Real.sqrt s := by
  calc
    s * s ^ (-(3 / 2 : ℝ)) = s ^ (-(1 / 2 : ℝ)) := by
      rw [show -(1 / 2 : ℝ) = 1 + -(3 / 2 : ℝ) by norm_num,
        Real.rpow_add hs, Real.rpow_one]
    _ = 1 / Real.sqrt s := by
      simp only [Real.rpow_neg hs.le, Real.sqrt_eq_rpow, one_div]

end ExplicitRIP.Edges
