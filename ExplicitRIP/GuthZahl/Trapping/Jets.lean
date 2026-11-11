/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Jets.Degree
public import ExplicitRIP.GuthZahl.Trapping.Jets.Evaluation

/-!
# Directional jets for the Guth–Zahl trapping argument

The direction degree is bounded by the jet order. Evaluation of a jet is the
corresponding line-restriction coefficient multiplied by its factorial, over
every field and at every order.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- The direction-variable degree is controlled without a surface-degree bound. -/
theorem directionJet_totalDegree_le {K : Type*} [Field K] (f : Poly K) (j : ℕ) :
    (directionJet f j).totalDegree ≤ j := by
  induction j with
  | zero => simp only [directionJet, MvPolynomial.totalDegree_C, le_refl]
  | succ j ih =>
    exact (directionDeriv_totalDegree_le (directionJet f j)).trans (Nat.add_le_add_right ih 1)

open Classical in
/-- The precise derivative/coefficient identity, including j >= p. -/
theorem eval_directionJet {K : Type*} [Field K] (f : Poly K)
    (x v : Point K) (j : ℕ) :
    evalDirection (directionJet f j) x v =
      (j.factorial : K) * (restrictLine f x v).coeff j := by
  rw [← eval_zero_restrictDirection, restrictDirection_directionJet,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]

end ExplicitRIP.GuthZahl

end
