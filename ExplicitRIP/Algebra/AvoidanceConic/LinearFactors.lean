/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.Dimensions
public import Mathlib

/-!
# Linear factors of plane cubics

A polynomial of degree one has an affine line of zeros. A cubic with no such
factor is irreducible, so it is relatively prime to every nonzero quadratic.
-/

public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial
open scoped Matrix

variable {K : Type*} [Field K]

theorem exponent_eq_of_sum_le_one (m : Fin 2 →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ 1) :
    m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 := by
  rw [exponent_sum_two] at hm
  have hm' : (m 0 = 0 ∧ m 1 = 0) ∨ (m 0 = 1 ∧ m 1 = 0) ∨
      (m 0 = 0 ∧ m 1 = 1) := by omega
  rcases hm' with h | h | h
  · left; ext i; fin_cases i <;> simp_all
  · right; left; ext i; fin_cases i <;> simp_all
  · right; right; ext i; fin_cases i <;> simp_all

/-- The three coefficient terms of a polynomial of degree at most one. -/
theorem eq_affine_of_totalDegree_le_one (P : Bivariate K) (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + C (P.coeff (Finsupp.single 0 1)) * X 0 +
      C (P.coeff (Finsupp.single 1 1)) * X 1 := by
  classical
  ext m
  by_cases h0 : m = 0
  · subst m; simp
  by_cases h1 : m = Finsupp.single 0 1
  · subst m; simp [Ne.symm h0]
  by_cases h2 : m = Finsupp.single 1 1
  · subst m; simp [Ne.symm h0]
  have hm : P.coeff m = 0 := by
    by_contra hn
    have hd := (le_totalDegree (mem_support_iff.mpr hn)).trans hP
    rcases exponent_eq_of_sum_le_one m hd with h | h | h
    · exact h0 h
    · exact h1 h
    · exact h2 h
  simp [coeff_X, Ne.symm h0, Ne.symm h1, Ne.symm h2, hm]

/-- An affine linear equation over a field has a parametrized line of zeros. -/
theorem exists_line_of_totalDegree_eq_one (P : Bivariate K) (hP : P.totalDegree = 1) :
    ∃ a v : Fin 2 → K, v ≠ 0 ∧
      ∀ t : K, eval (fun i => a i + t * v i) P = 0 := by
  classical
  let c := P.coeff 0
  let b := P.coeff (Finsupp.single 0 1)
  let d := P.coeff (Finsupp.single 1 1)
  have he : P = C c + C b * X 0 + C d * X 1 := eq_affine_of_totalDegree_le_one P hP.le
  have hbd : b ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    have hc : P = C c := by simpa only [h.1, h.2, C_0, zero_mul, add_zero] using he
    rw [hc, totalDegree_C] at hP
    exact Nat.zero_ne_one hP
  by_cases hd : d ≠ 0
  · refine ⟨![0, -c / d], ![1, -b / d], ?_, ?_⟩
    · intro h; have hh := congrFun h 0; simp at hh
    · intro t
      rw [he]
      simp only [map_add, map_mul, eval_C, eval_X, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_add, mul_one]
      field_simp
      ring
  · have hb : b ≠ 0 := hbd.resolve_right hd
    have hd0 : d = 0 := not_ne_iff.mp hd
    refine ⟨![-c / b, 0], ![0, 1], ?_, ?_⟩
    · intro h; have hh := congrFun h 1; simp at hh
    · intro t
      rw [he, hd0]
      simp only [map_add, map_mul, eval_C, eval_X, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_add, mul_one, mul_zero, add_zero, zero_mul]
      field_simp
      ring

/-- A cubic over a field is irreducible if it has no linear divisor. -/
theorem irreducible_of_degree_three_of_no_linear_dvd (P : Bivariate K)
    (hP : P.totalDegree = 3)
    (hlinear : ∀ L : Bivariate K, L.totalDegree = 1 → ¬L ∣ P) : Irreducible P := by
  have hP0 : P ≠ 0 := by intro h; simp only [h, totalDegree_zero] at hP; omega
  refine ⟨?_, ?_⟩
  · intro hu
    have := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B hAB
    have hA : A ≠ 0 := left_ne_zero_of_mul (hAB ▸ hP0)
    have hB : B ≠ 0 := right_ne_zero_of_mul (hAB ▸ hP0)
    have hd : A.totalDegree + B.totalDegree = 3 := by
      rw [← totalDegree_mul_of_isDomain hA hB, ← hAB, hP]
    by_cases huA : IsUnit A
    · exact Or.inl huA
    by_cases huB : IsUnit B
    · exact Or.inr huB
    have hpA : 0 < A.totalDegree := by
      by_contra h
      have he := totalDegree_eq_zero_iff_eq_C.mp (by omega : A.totalDegree = 0)
      apply huA
      rw [he]
      exact (isUnit_iff_ne_zero.mpr (by intro h; apply hA; simpa only [h, C_0] using he)).map C
    have hpB : 0 < B.totalDegree := by
      by_contra h
      have he := totalDegree_eq_zero_iff_eq_C.mp (by omega : B.totalDegree = 0)
      apply huB
      rw [he]
      exact (isUnit_iff_ne_zero.mpr (by intro h; apply hB; simpa only [h, C_0] using he)).map C
    have hone : A.totalDegree = 1 ∨ B.totalDegree = 1 := by omega
    rcases hone with ha | hb
    · exact False.elim (hlinear A ha ⟨B, hAB⟩)
    · exact False.elim (hlinear B hb ⟨A, hAB.trans (mul_comm A B)⟩)

end ExplicitRIP.Avconic

end
