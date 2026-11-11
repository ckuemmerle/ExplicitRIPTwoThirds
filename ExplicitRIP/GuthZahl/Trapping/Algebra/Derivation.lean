/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Defs

/-!
# Differentiation of the coefficients of a direction polynomial

The outer variables record directions and are held fixed. The coefficient
formula reduces additivity and the product rule to those for partial derivatives.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl
namespace TrappingAlgebra

/-- Partial differentiation of the coefficients, holding the outer variables fixed. -/
noncomputable def coefficientDeriv {K : Type*} [Field K]
    (i : Fin 3) (H : DirectionPoly K) : DirectionPoly K :=
  ∑ a ∈ H.support, MvPolynomial.monomial a (MvPolynomial.pderiv i (H.coeff a))

theorem coeff_coefficientDeriv {K : Type*} [Field K]
    (i : Fin 3) (H : DirectionPoly K) (m : Fin 3 →₀ ℕ) :
    (coefficientDeriv i H).coeff m = MvPolynomial.pderiv i (H.coeff m) := by
  classical
  by_cases hm : m ∈ H.support
  · simp only [coefficientDeriv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      Finset.sum_ite_eq', hm, ite_true]
  · simp only [coefficientDeriv, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      Finset.sum_ite_eq', hm, ite_false, MvPolynomial.notMem_support_iff.mp hm, map_zero]

theorem coefficientDeriv_add {K : Type*} [Field K]
    (i : Fin 3) (H J : DirectionPoly K) :
    coefficientDeriv i (H + J) = coefficientDeriv i H + coefficientDeriv i J := by
  apply MvPolynomial.ext
  intro m
  simp only [coeff_coefficientDeriv, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

theorem coefficientDeriv_zero {K : Type*} [Field K] (i : Fin 3) :
    coefficientDeriv i (0 : DirectionPoly K) = 0 := by
  apply MvPolynomial.ext
  intro m
  simp only [coeff_coefficientDeriv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]

theorem coefficientDeriv_mul {K : Type*} [Field K]
    (i : Fin 3) (H J : DirectionPoly K) :
    coefficientDeriv i (H * J) = coefficientDeriv i H * J + H * coefficientDeriv i J := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [coeff_coefficientDeriv, MvPolynomial.coeff_mul, map_sum,
    MvPolynomial.pderiv_mul, Finset.sum_add_distrib, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]

theorem directionDeriv_add {K : Type*} [Field K] (H J : DirectionPoly K) :
    directionDeriv (H + J) = directionDeriv H + directionDeriv J := by
  change (∑ i : Fin 3, MvPolynomial.X i * coefficientDeriv i (H + J)) = _
  simp only [coefficientDeriv_add, mul_add, Finset.sum_add_distrib]
  rfl

theorem directionDeriv_zero {K : Type*} [Field K] :
    directionDeriv (0 : DirectionPoly K) = 0 := by
  change (∑ i : Fin 3, MvPolynomial.X i * coefficientDeriv i (0 : DirectionPoly K)) = 0
  simp only [coefficientDeriv_zero, mul_zero, Finset.sum_const_zero]

/-- The directional derivative satisfies the product rule while treating the direction variables as
fixed. -/
theorem _root_.ExplicitRIP.GuthZahl.directionDeriv_mul {K : Type*} [Field K]
    (H J : DirectionPoly K) :
    directionDeriv (H * J) = directionDeriv H * J + H * directionDeriv J := by
  change (∑ i : Fin 3, MvPolynomial.X i * coefficientDeriv i (H * J)) =
    (∑ i : Fin 3, MvPolynomial.X i * coefficientDeriv i H) * J +
      H * ∑ i : Fin 3, MvPolynomial.X i * coefficientDeriv i J
  simp only [coefficientDeriv_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

end TrappingAlgebra
end ExplicitRIP.GuthZahl

end
