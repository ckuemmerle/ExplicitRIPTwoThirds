/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Finite Abel and Cauchy estimates for descending nonnegative coefficients. -/

public section

noncomputable section
open scoped BigOperators

namespace ExplicitRIP.Lev

/-- Finite Abel summation, retaining both boundary terms. -/
theorem finite_abel_identity {R : Type*} [CommRing R]
    (N : ℕ) (a F : ℕ → R) :
    (∑ i ∈ Finset.range N, (a i - a (i + 1)) * F (i + 1)) =
      (∑ i ∈ Finset.range N, a i * (F (i + 1) - F i)) +
        a 0 * F 0 - a N * F N := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; ring
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

/-- Square-root increments have squared size bounded by a harmonic summand. -/
theorem sqrt_increment_sq_le_inv (i : ℕ) :
    (Real.sqrt ((i + 1 : ℕ) : ℝ) - Real.sqrt (i : ℝ)) ^ 2 ≤
      (((i + 1 : ℕ) : ℝ))⁻¹ := by
  let x := Real.sqrt ((i + 1 : ℕ) : ℝ)
  let y := Real.sqrt (i : ℝ)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hxy : y ≤ x := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ i)
  have hd : 0 ≤ x - y := sub_nonneg.mpr hxy
  have hx2 : x ^ 2 = ((i + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hy2 : y ^ 2 = (i : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hi : 0 < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_cast
  have hdx : (x - y) * x ≤ 1 := by
    nlinarith only [hx2, hy2, hcast, mul_nonneg hy hd]
  have hsq := mul_self_le_mul_self (mul_nonneg hd hx) hdx
  change (x - y) ^ 2 ≤ (((i + 1 : ℕ) : ℝ))⁻¹
  rw [← one_div]
  apply (le_div_iff₀ hi).mpr
  calc
    (x - y) ^ 2 * ((i + 1 : ℕ) : ℝ) =
        ((x - y) * x) * ((x - y) * x) := by rw [← hx2]; ring
    _ ≤ 1 := by simpa only [mul_one] using hsq

end ExplicitRIP.Lev

theorem ExplicitRIP.Lev.norm_weighted_sum_le_log_of_prefix_bounds
    (N : ℕ) (v : ℕ → ℂ) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (_ha : ∀ i, i ≤ N → 0 ≤ a i)
    (hmono : ∀ i, i < N → a (i + 1) ≤ a i) (hzero : a N = 0)
    (hprefix : ∀ k, k ≤ N →
      ‖∑ i ∈ Finset.range k, v i‖ ≤ C * Real.sqrt (k : ℝ)) :
    ‖∑ i ∈ Finset.range N, (a i : ℂ) * v i‖ ≤
      C * Real.sqrt (1 + Real.log (N : ℝ)) *
        Real.sqrt (∑ i ∈ Finset.range N, (a i) ^ 2) :=
by
  let P : ℕ → ℂ := fun k => ∑ i ∈ Finset.range k, v i
  let d : ℕ → ℝ := fun i => Real.sqrt ((i + 1 : ℕ) : ℝ) - Real.sqrt (i : ℝ)
  have hdiff (i : ℕ) (hi : i ∈ Finset.range N) : 0 ≤ a i - a (i + 1) :=
    sub_nonneg.mpr (hmono i (Finset.mem_range.mp hi))
  have hvector : (∑ i ∈ Finset.range N, ((a i - a (i + 1) : ℝ) : ℂ) * P (i + 1)) =
      ∑ i ∈ Finset.range N, (a i : ℂ) * v i := by
    have h := ExplicitRIP.Lev.finite_abel_identity
      N (fun i => (a i : ℂ)) P
    simpa only [P, Finset.sum_range_succ, Finset.sum_range_zero,
      add_sub_cancel_left, mul_zero, add_zero, hzero, Complex.ofReal_zero,
      zero_mul, sub_zero, ← Complex.ofReal_sub] using h
  have hscalar : (∑ i ∈ Finset.range N, (a i - a (i + 1)) *
      Real.sqrt ((i + 1 : ℕ) : ℝ)) = ∑ i ∈ Finset.range N, a i * d i := by
    have h := ExplicitRIP.Lev.finite_abel_identity
      N a (fun i => Real.sqrt (i : ℝ))
    simpa only [d, Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero,
      hzero, zero_mul, sub_zero] using h
  have hsqsum : (∑ i ∈ Finset.range N, (d i) ^ 2) ≤ 1 + Real.log (N : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ))⁻¹ :=
        Finset.sum_le_sum (fun i _ =>
          ExplicitRIP.Lev.sqrt_increment_sq_le_inv i)
      _ = (harmonic N : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have hnorm : ‖∑ i ∈ Finset.range N, (a i : ℂ) * v i‖ ≤
      C * (∑ i ∈ Finset.range N, a i * d i) := by
    rw [← hvector]
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖((a i - a (i + 1) : ℝ) : ℂ) * P (i + 1)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, (a i - a (i + 1)) *
          (C * Real.sqrt ((i + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiff i hi)]
        exact mul_le_mul_of_nonneg_left
          (hprefix (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) (hdiff i hi)
      _ = C * (∑ i ∈ Finset.range N, (a i - a (i + 1)) *
          Real.sqrt ((i + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C * (∑ i ∈ Finset.range N, a i * d i) := by rw [hscalar]
  calc
    _ ≤ C * (∑ i ∈ Finset.range N, a i * d i) := hnorm
    _ ≤ C * (Real.sqrt (∑ i ∈ Finset.range N, (a i) ^ 2) *
        Real.sqrt (∑ i ∈ Finset.range N, (d i) ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ a d) hC
    _ ≤ C * (Real.sqrt (∑ i ∈ Finset.range N, (a i) ^ 2) *
        Real.sqrt (1 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsqsum) (Real.sqrt_nonneg _)) hC
    _ = C * Real.sqrt (1 + Real.log (N : ℝ)) *
        Real.sqrt (∑ i ∈ Finset.range N, (a i) ^ 2) := by ring
