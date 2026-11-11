/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LevDR.NonnegRectangle
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-! Complex coefficients split into four nonnegative coordinate parts. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ExplicitRIP.Lev

/-- The four nonnegative coordinate parts of a complex number. -/
def quadrantPart (r : Fin 4) (z : ℂ) : ℝ :=
  ![max z.re 0, max (-z.re) 0, max z.im 0, max (-z.im) 0] r

/-- The unit phases multiplying the four coordinate parts. -/
def quadrantPhase (r : Fin 4) : ℂ := ![1, -1, Complex.I, -Complex.I] r

theorem quadrant_part_nonneg (r : Fin 4) (z : ℂ) : 0 ≤ quadrantPart r z := by
  fin_cases r <;> simp only [quadrantPart] <;> exact le_max_right _ _

theorem max_zero_sq_le (x : ℝ) : (max x 0) ^ 2 ≤ x ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · rw [max_eq_right (le_of_not_ge hx)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg x

theorem quadrant_part_sq_le (r : Fin 4) (z : ℂ) :
    (quadrantPart r z) ^ 2 ≤ Complex.normSq z := by
  have hre : z.re ^ 2 ≤ Complex.normSq z := by
    simpa only [pow_two] using Complex.re_sq_le_normSq z
  have him : z.im ^ 2 ≤ Complex.normSq z := by
    simpa only [pow_two] using Complex.im_sq_le_normSq z
  fin_cases r
  · exact (max_zero_sq_le z.re).trans hre
  · change (max (-z.re) 0) ^ 2 ≤ Complex.normSq z
    exact (max_zero_sq_le (-z.re)).trans (by simpa only [neg_sq] using hre)
  · exact (max_zero_sq_le z.im).trans him
  · change (max (-z.im) 0) ^ 2 ≤ Complex.normSq z
    exact (max_zero_sq_le (-z.im)).trans (by simpa only [neg_sq] using him)

theorem quadrant_phase_norm (r : Fin 4) : ‖quadrantPhase r‖ = 1 := by
  fin_cases r <;> simp [quadrantPhase]

theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    exact sub_zero x
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    exact zero_sub (-x) |>.trans (neg_neg x)

theorem sum_quadrant_parts (z : ℂ) :
    (∑ r : Fin 4, quadrantPhase r * (quadrantPart r z : ℂ)) = z := by
  have hre := max_sub_max_neg z.re
  have him := max_sub_max_neg z.im
  apply Complex.ext
  · simp [Fin.sum_univ_four, quadrantPhase, quadrantPart]
    linarith only [hre]
  · simp [Fin.sum_univ_four, quadrantPhase, quadrantPart]
    linarith only [him]

theorem quadrant_mass_le {J : Type*} (s : Finset J) (a : J → ℂ) (r : Fin 4) :
    Real.sqrt (∑ i ∈ s, (quadrantPart r (a i)) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, Complex.normSq (a i)) :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => quadrant_part_sq_le r (a i)))

end ExplicitRIP.Lev

/-- Complex coefficients are controlled by sixteen nonnegative rectangles. -/
theorem ExplicitRIP.Lev.complex_weighted_rectangle_log
    {I J : Type*} (G : I → J → ℂ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset I) (t : Finset J)
    (hrectangle : ∀ u : Finset I, u ⊆ s → ∀ v : Finset J, v ⊆ t →
      ‖∑ i ∈ u, ∑ j ∈ v, G i j‖ ≤
        (theta * Real.sqrt (u.card : ℝ)) * Real.sqrt (v.card : ℝ))
    (a : I → ℂ) (b : J → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j *
      G i j‖ ≤
      16 * theta * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (1 + Real.log (t.card : ℝ)) *
        Real.sqrt (∑ i ∈ s, Complex.normSq (a i)) *
        Real.sqrt (∑ j ∈ t, Complex.normSq (b j)) :=
by
  classical
  let Q : ℝ := theta * Real.sqrt (1 + Real.log (s.card : ℝ)) *
    Real.sqrt (1 + Real.log (t.card : ℝ))
  let Ea : ℝ := Real.sqrt (∑ i ∈ s, Complex.normSq (a i))
  let Eb : ℝ := Real.sqrt (∑ j ∈ t, Complex.normSq (b j))
  let R : ℝ := Q * Ea * Eb
  let P : Fin 4 → Fin 4 → ℂ := fun r q =>
    ∑ i ∈ s, ∑ j ∈ t,
      (quadrantPart r (a i) : ℂ) * (quadrantPart q (b j) : ℂ) * G i j
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg htheta (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hP (r q : Fin 4) : ‖P r q‖ ≤ R := by
    have h := nonneg_weighted_rectangle_log G theta htheta s t hrectangle
      (fun i => quadrantPart r (a i)) (fun j => quadrantPart q (b j))
      (fun i _ => quadrant_part_nonneg r (a i)) (fun j _ => quadrant_part_nonneg q (b j))
    exact h.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (quadrant_mass_le s a r) hQ)
      (quadrant_mass_le t b q) (Real.sqrt_nonneg _)
      (mul_nonneg hQ (Real.sqrt_nonneg _)))
  have hunit (r q : Fin 4) : ‖(quadrantPhase r * quadrantPhase q) * P r q‖ ≤ R := by
    simpa only [norm_mul, quadrant_phase_norm, one_mul] using hP r q
  have hterm (i : I) (j : J) : a i * b j * G i j =
      ∑ r : Fin 4, ∑ q : Fin 4, (quadrantPhase r * quadrantPhase q) *
        ((quadrantPart r (a i) : ℂ) * (quadrantPart q (b j) : ℂ) * G i j) := by
    calc
      _ = (∑ r : Fin 4, quadrantPhase r * (quadrantPart r (a i) : ℂ)) *
          (∑ q : Fin 4, quadrantPhase q * (quadrantPart q (b j) : ℂ)) * G i j := by
        rw [sum_quadrant_parts, sum_quadrant_parts]
      _ = ∑ r : Fin 4, (quadrantPhase r * (quadrantPart r (a i) : ℂ)) *
          (∑ q : Fin 4, quadrantPhase q * (quadrantPart q (b j) : ℂ)) * G i j := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro q _
        ring
  have hexpand : (∑ i ∈ s, ∑ j ∈ t, a i * b j * G i j) =
      ∑ r : Fin 4, ∑ q : Fin 4, (quadrantPhase r * quadrantPhase q) * P r q := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ t, ∑ r : Fin 4, ∑ q : Fin 4,
          (quadrantPhase r * quadrantPhase q) *
            ((quadrantPart r (a i) : ℂ) * (quadrantPart q (b j) : ℂ) * G i j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hterm i j)
      _ = ∑ i ∈ s, ∑ r : Fin 4, ∑ q : Fin 4, ∑ j ∈ t,
          (quadrantPhase r * quadrantPhase q) *
            ((quadrantPart r (a i) : ℂ) * (quadrantPart q (b j) : ℂ) * G i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = ∑ r : Fin 4, ∑ q : Fin 4, ∑ i ∈ s, ∑ j ∈ t,
          (quadrantPhase r * quadrantPhase q) *
            ((quadrantPart r (a i) : ℂ) * (quadrantPart q (b j) : ℂ) * G i j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = _ := by simp only [P, Finset.mul_sum]
  calc
    _ = ‖∑ r : Fin 4, ∑ q : Fin 4, (quadrantPhase r * quadrantPhase q) * P r q‖ :=
      congrArg norm hexpand
    _ ≤ ∑ r : Fin 4, ‖∑ q : Fin 4, (quadrantPhase r * quadrantPhase q) * P r q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Fin 4, ∑ q : Fin 4, ‖(quadrantPhase r * quadrantPhase q) * P r q‖ :=
      Finset.sum_le_sum (fun r _ => norm_sum_le _ _)
    _ ≤ ∑ _r : Fin 4, ∑ _q : Fin 4, R :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun q _ => hunit r q))
    _ = 16 * R := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = 16 * theta * Real.sqrt (1 + Real.log (s.card : ℝ)) *
        Real.sqrt (1 + Real.log (t.card : ℝ)) *
        Real.sqrt (∑ i ∈ s, Complex.normSq (a i)) *
        Real.sqrt (∑ j ∈ t, Complex.normSq (b j)) := by
      dsimp only [R, Q, Ea, Eb]
      ring
