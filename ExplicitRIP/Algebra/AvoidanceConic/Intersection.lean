/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.Dimensions
public import Mathlib

/-!
# A degree-product bound for distinct affine intersection points

Polynomial interpolation on arbitrary distinct points, combined with the dimension
of a bounded polynomial quotient, proves the affine intersection bound over any field.
-/

@[expose] public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial Finset

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- A linear polynomial separating two distinct points. -/
theorem exists_linear_separator (a b : Fin 2 → K) (hab : a ≠ b) :
    ∃ P : Bivariate K, P.totalDegree ≤ 1 ∧ eval a P = 1 ∧ eval b P = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := Function.ne_iff.mp hab
  refine ⟨C ((a i - b i)⁻¹) * (X i - C (b i)), ?_, ?_, ?_⟩
  · apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add, totalDegree_X] using
      (totalDegree_sub (X i : Bivariate K) (C (b i))).trans (by simp)
  · simp only [map_mul, eval_C, map_sub, eval_X]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hi)
  · simp only [map_mul, eval_C, map_sub, eval_X, sub_self, mul_zero]

/-- Every function on a finite collection of distinct plane points is a polynomial
function of total degree at most the number of points. -/
theorem exists_interpolating_polynomial (q : ι → Fin 2 → K)
    (hq : Function.Injective q) (v : ι → K) :
    ∃ P : Bivariate K, P.totalDegree ≤ Fintype.card ι ∧ ∀ i, eval (q i) P = v i := by
  classical
  have hsep : ∀ i j : ι, i ≠ j →
      ∃ P : Bivariate K, P.totalDegree ≤ 1 ∧ eval (q i) P = 1 ∧ eval (q j) P = 0 :=
    fun i j hij => exists_linear_separator (q i) (q j) (fun h => hij (hq h))
  choose sep hdeg hone hzero using hsep
  let L (i j : ι) : Bivariate K := if h : i = j then 1 else sep i j h
  have hLdeg (i j : ι) : (L i j).totalDegree ≤ 1 := by
    dsimp only [L]
    split_ifs with h
    · simp only [totalDegree_one, zero_le]
    · exact hdeg i j h
  have hLone (i j : ι) : eval (q i) (L i j) = 1 := by
    dsimp only [L]
    split_ifs with h
    · exact map_one _
    · exact hone i j h
  have hLzero (i j : ι) (h : i ≠ j) : eval (q j) (L i j) = 0 := by
    simpa only [L, dite_eq_right h] using hzero i j h
  let B (i : ι) : Bivariate K := ∏ j, L i j
  have hBdeg (i : ι) : (B i).totalDegree ≤ Fintype.card ι := by
    apply (totalDegree_finsetProd _ _).trans
    simpa only [sum_const, card_univ, smul_eq_mul, mul_one] using
      Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hLdeg i j)
  have hBeval (i j : ι) : eval (q j) (B i) = if i = j then 1 else 0 := by
    by_cases h : i = j
    · subst j
      simp only [B, map_prod, hLone, prod_const_one, ite_true]
    · rw [ite_eq_right h]
      dsimp only [B]
      rw [map_prod]
      exact prod_eq_zero (mem_univ j) (hLzero i j h)
  refine ⟨∑ i, C (v i) * B i, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hBdeg i)
  · intro j
    simp only [map_sum, map_mul, eval_C, hBeval, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]

/-- Evaluation on a finite family of plane points as a linear map. -/
def pointEvaluation (q : ι → Fin 2 → K) : Bivariate K →ₗ[K] (ι → K) :=
  LinearMap.pi fun i => (aeval (q i)).toLinearMap

omit [Fintype ι] in
@[simp] theorem pointEvaluation_apply (q : ι → Fin 2 → K) (P : Bivariate K) (i : ι) :
    pointEvaluation q P i = eval (q i) P := rfl

/-- Distinct common zeros of relatively prime plane polynomials are bounded by
the product of their total degrees. -/
theorem card_le_degree_product (q : ι → Fin 2 → K) (hq : Function.Injective q)
    (G H : Bivariate K) (hG : G ≠ 0) (hH : H ≠ 0) (hrel : IsRelPrime G H)
    (hGq : ∀ i, eval (q i) G = 0) (hHq : ∀ i, eval (q i) H = 0) :
    Fintype.card ι ≤ G.totalDegree * H.totalDegree := by
  classical
  let M := G.totalDegree + H.totalDegree + Fintype.card ι
  have hM : G.totalDegree + H.totalDegree ≤ M := by dsimp only [M]; omega
  let f := (pointEvaluation q).comp (DegreeSpace K M).subtype
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨P, hP, hv⟩ := exists_interpolating_polynomial q hq v
    refine ⟨⟨P, (mem_restrictTotalDegree _ _ _).mpr (hP.trans ?_)⟩, ?_⟩
    · dsimp only [M]; omega
    · exact funext hv
  have hker := boundedIdealSpace_le_ker_comp G H M (pointEvaluation q)
    (fun A => by ext i; simp only [pointEvaluation_apply, map_mul, hGq, zero_mul, Pi.zero_apply])
    (fun A => by ext i; simp only [pointEvaluation_apply, map_mul, hHq, zero_mul, Pi.zero_apply])
  have hd := finrank_target_le_degree_product G H hG hH hrel M hM f hf hker
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using hd

end ExplicitRIP.Avconic

end
