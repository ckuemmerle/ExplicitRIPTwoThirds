/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Defs

/-!
# Direction degrees of iterated directional derivatives

Differentiating coefficients preserves the direction exponents, and multiplication by
a direction coordinate increases their total degree by at most one.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem directionDeriv_totalDegree_le {K : Type*} [Field K] (H : DirectionPoly K) :
    (directionDeriv H).totalDegree ≤ H.totalDegree + 1 := by
  classical
  unfold directionDeriv
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_X, add_comm H.totalDegree]
  apply Nat.add_le_add_left
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree ha)

end ExplicitRIP.GuthZahl

end
