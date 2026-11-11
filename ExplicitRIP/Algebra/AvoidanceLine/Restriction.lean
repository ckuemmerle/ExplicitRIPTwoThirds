/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Restricting homogeneous polynomials to affine lines

The coefficient of the top possible power in an affine restriction is the
homogeneous polynomial evaluated at the direction of the line.
-/

@[expose] public section

noncomputable section

namespace ExplicitRIP.Avline

open Polynomial
open scoped BigOperators

variable {K ι σ : Type*} [CommSemiring K]

/-- The polynomial parametrizing one coordinate of an affine line. -/
def affinePolynomial (a b : K) : K[X] := C a + C b * X

theorem affinePolynomial_natDegree_le (a b : K) :
    (affinePolynomial a b).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp only [natDegree_C, Nat.zero_le]
  · exact (natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_le,
      zero_add]))

theorem affinePolynomial_coeff_one (a b : K) :
    (affinePolynomial a b).coeff 1 = b := by
  simp only [affinePolynomial, coeff_add, coeff_C, one_ne_zero, ite_false,
    coeff_C_mul, coeff_X_one, mul_one, zero_add]

theorem eval_affinePolynomial (a b t : K) :
    (affinePolynomial a b).eval t = a + b * t := by
  simp only [affinePolynomial, eval_add, eval_C, eval_mul, eval_X]

/-- Multiplication preserves the coefficient at the sum of specified degree bounds. -/
theorem coeff_prod_sum_bounds (s : Finset ι) (f : ι → K[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, coeff_one_zero]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (f j).natDegree ≤ d j :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hdeg : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, d j :=
      (natDegree_prod_le s f).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self i s)) hdeg,
      ih hs, Finset.prod_insert hi]

/-- Substitution of affine coordinate polynomials into a multivariate polynomial. -/
def restrictLine (F : MvPolynomial σ K) (a b : σ → K) : K[X] :=
  F.eval₂ C (fun i => affinePolynomial (a i) (b i))

theorem restrictLine_natDegree_le {F : MvPolynomial σ K} {n : ℕ}
    (hF : F.IsHomogeneous n) (a b : σ → K) :
    (restrictLine F a b).natDegree ≤ n := by
  classical
  rw [restrictLine, MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro d hd
  apply (natDegree_C_mul_le _ _).trans
  rw [hF.degree_eq_sum_deg_support hd]
  apply (natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact natDegree_pow_le.trans (by
    simpa only [mul_one] using Nat.mul_le_mul_left (d i)
      (affinePolynomial_natDegree_le (a i) (b i)))

theorem restrictLine_coeff {F : MvPolynomial σ K} {n : ℕ}
    (hF : F.IsHomogeneous n) (a b : σ → K) :
    (restrictLine F a b).coeff n = MvPolynomial.eval b F := by
  classical
  rw [restrictLine, MvPolynomial.eval₂_eq, finsetSum_coeff]
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_C_mul, hF.degree_eq_sum_deg_support hd]
  congr 1
  rw [coeff_prod_sum_bounds _ _ (fun i => d i)]
  · apply Finset.prod_congr rfl
    intro i _
    simpa only [mul_one, affinePolynomial_coeff_one] using
      (coeff_pow_of_natDegree_le (m := d i) (affinePolynomial_natDegree_le (a i) (b i)))
  · intro i _
    exact natDegree_pow_le.trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left (d i)
        (affinePolynomial_natDegree_le (a i) (b i)))

theorem eval_restrictLine (F : MvPolynomial σ K) (a b : σ → K) (t : K) :
    (restrictLine F a b).eval t = MvPolynomial.eval (fun i => a i + b i * t) F := by
  change (Polynomial.evalRingHom t) (F.eval₂ C (fun i => affinePolynomial (a i) (b i))) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (Polynomial.evalRingHom t).comp C = RingHom.id K := by
    ext x
    exact eval_C
  rw [hC, MvPolynomial.eval₂_id]
  change MvPolynomial.eval (fun i => (affinePolynomial (a i) (b i)).eval t) F = _
  simp only [eval_affinePolynomial]

end ExplicitRIP.Avline

end

end
