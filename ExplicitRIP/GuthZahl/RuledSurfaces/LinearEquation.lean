/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Restriction
public import ExplicitRIP.GuthZahl.RuledSurfaces.Tangent

/-!
# Affine planes defined by linear polynomials

The zero set of a polynomial of total degree one is its affine tangent plane
at any zero. In particular, any two lines on such a polynomial are coplanar.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A polynomial of total degree at most one is affine linear about every base point. -/
theorem eval_eq_tangentFunctional_add_of_totalDegree_le_one {f : Poly K}
    (hf : f.totalDegree ≤ 1) (a x : Point K) :
    MvPolynomial.eval x f = tangentFunctional f a (x - a) + MvPolynomial.eval a f := by
  have hdeg := (restrictLine_natDegree_le f a (x - a)).trans hf
  have heq := congrArg (Polynomial.eval (1 : K))
    (Polynomial.eq_X_add_C_of_natDegree_le_one hdeg)
  rw [eval_restrictLine, one_smul] at heq
  have hpoint : a + (x - a) = x := by abel
  rw [hpoint, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_C, mul_one, coeff_zero_restrictLine,
    coeff_one_restrictLine] at heq
  exact heq

/-- The gradient of a linear polynomial is nonzero at every point over an infinite field. -/
theorem exists_pderiv_eval_ne_zero_of_totalDegree_eq_one [Infinite K] {f : Poly K}
    (hf : f.totalDegree = 1) (a : Point K) :
    ∃ i : Fin 3, MvPolynomial.eval a (MvPolynomial.pderiv i f) ≠ 0 := by
  by_contra h
  push Not at h
  have hconstant : f = MvPolynomial.C (MvPolynomial.eval a f) := by
    apply MvPolynomial.funext
    intro x
    rw [MvPolynomial.eval_C, eval_eq_tangentFunctional_add_of_totalDegree_le_one hf.le a x]
    simp only [tangentFunctional, LinearMap.coe_mk, AddHom.coe_mk, h, zero_mul,
      Finset.sum_const_zero, zero_add]
  rw [hconstant, MvPolynomial.totalDegree_C] at hf
  exact Nat.zero_ne_one hf

/-- The zero set of a linear equation lies in the tangent plane at any of its zeroes. -/
theorem mem_tangentPlane_of_eval_eq_zero_of_totalDegree_le_one {f : Poly K}
    (hf : f.totalDegree ≤ 1) {a x : Point K}
    (ha : MvPolynomial.eval a f = 0) (hx : MvPolynomial.eval x f = 0) :
    x ∈ tangentPlane f a := by
  apply AffineSubspace.mem_mk'.2
  change tangentFunctional f a (x - a) = 0
  have heq := eval_eq_tangentFunctional_add_of_totalDegree_le_one hf a x
  rw [ha, hx, add_zero] at heq
  exact heq.symm

/-- Any two lines on a linear equation are coplanar, including parallel lines. -/
theorem coplanar_of_lineOn_linear [Infinite K] {f : Poly K} (hf : f.totalDegree = 1)
    {L M : Line K} (hL : LineOn f L) (hM : LineOn f M) : Coplanar L M := by
  obtain ⟨a, ha⟩ := line_nonempty L
  refine ⟨tangentPlane f a,
    finrank_direction_tangentPlane f a (exists_pderiv_eval_ne_zero_of_totalDegree_eq_one hf a),
    line_le_tangentPlane hL ha, ?_⟩
  intro x hx
  exact mem_tangentPlane_of_eval_eq_zero_of_totalDegree_le_one hf.le
    (eval_eq_zero_of_lineOn hL ha) (eval_eq_zero_of_lineOn hM hx)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
