/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Tangent equations for algebraically contained lines

The first coefficient of a line restriction is the gradient paired with its
direction. Thus every contained line through a point lies in the affine
kernel of that gradient. No differentiation of pointwise functions is used.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The constant coefficient of a restriction is the value at its base point. -/
theorem coeff_zero_restrictLine (f : Poly K) (a v : Point K) :
    (restrictLine f a v).coeff 0 = MvPolynomial.eval a f := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_restrictLine, zero_smul, add_zero]

/-- The linear coefficient of a restriction is the directional derivative. -/
theorem coeff_one_restrictLine (f : Poly K) (a v : Point K) :
    (restrictLine f a v).coeff 1 =
      ∑ i : Fin 3, MvPolynomial.eval a (MvPolynomial.pderiv i f) * v i := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [restrictLine_C, Polynomial.coeff_C, one_ne_zero, ↓reduceIte,
      MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
  | add f g hf hg =>
    simp only [restrictLine_add, Polynomial.coeff_add, hf, hg,
      map_add, add_mul, Finset.sum_add_distrib]
  | mul_X f j hf =>
    rw [restrictLine_mul, restrictLine_X, mul_add, ← mul_assoc,
      Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X,
      Polynomial.coeff_mul_C, hf, coeff_zero_restrictLine]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X,
      Fin.sum_univ_succ]
    fin_cases j <;> simp [MvPolynomial.pderiv_X, Pi.single_apply] <;> ring

/-- The gradient evaluated at a point, as a linear functional on directions. -/
noncomputable def tangentFunctional (f : Poly K) (x : Point K) : Point K →ₗ[K] K where
  toFun v := ∑ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i f) * v i
  map_add' v w := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- All directions of a contained line annihilate the gradient at each of its points. -/
theorem tangentFunctional_eq_zero_of_lineOn {f : Poly K} {L : Line K}
    (hL : LineOn f L) {x v : Point K} (hx : x ∈ L.1) (hv : v ∈ L.1.direction) :
    tangentFunctional f x v = 0 := by
  change (∑ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i f) * v i) = 0
  rw [← coeff_one_restrictLine, hL x hx v hv, Polynomial.coeff_zero]

/-- The affine kernel of the gradient at a point. -/
noncomputable def tangentPlane (f : Poly K) (x : Point K) : AffineSubspace K (Point K) :=
  AffineSubspace.mk' x (LinearMap.ker (tangentFunctional f x))

/-- Every contained line through a point lies in its affine tangent kernel. -/
theorem line_le_tangentPlane {f : Poly K} {L : Line K}
    (hL : LineOn f L) {x : Point K} (hx : x ∈ L.1) : L.1 ≤ tangentPlane f x := by
  intro y hy
  apply AffineSubspace.mem_mk'.2
  exact tangentFunctional_eq_zero_of_lineOn hL hx
    (AffineSubspace.vsub_mem_direction hy hx)

/-- The gradient functional on a coordinate vector. -/
theorem tangentFunctional_single (f : Poly K) (x : Point K) (i : Fin 3) (c : K) :
    tangentFunctional f x (Pi.single i c) =
      MvPolynomial.eval x (MvPolynomial.pderiv i f) * c := by
  change (∑ j : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv j f) *
    Pi.single (M := fun _ : Fin 3 => K) i c j) = _
  simp only [Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- At a smooth point the affine tangent kernel has dimension two. -/
theorem finrank_direction_tangentPlane (f : Poly K) (x : Point K)
    (hsmooth : ∃ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0) :
    Module.finrank K (tangentPlane f x).direction = 2 := by
  obtain ⟨i, hi⟩ := hsmooth
  have hsurj : Function.Surjective (tangentFunctional f x) := by
    intro c
    refine ⟨Pi.single i (c / MvPolynomial.eval x (MvPolynomial.pderiv i f)), ?_⟩
    rw [tangentFunctional_single]
    field_simp
  have hdim := LinearMap.finrank_range_add_finrank_ker (tangentFunctional f x)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hdim
  have hpoint : Module.finrank K (Point K) = 3 := by
    simp only [Point, Module.finrank_pi, Fintype.card_fin]
  rw [hpoint] at hdim
  rw [tangentPlane, AffineSubspace.direction_mk']
  exact Nat.add_left_cancel hdim

end ExplicitRIP.GuthZahl.RuledSurfaces
end
