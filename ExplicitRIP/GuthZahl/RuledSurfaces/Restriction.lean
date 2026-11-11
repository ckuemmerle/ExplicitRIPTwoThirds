/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Finite coefficient tests for containment

The degree of the restriction to an affine line is bounded by total degree.
Thus algebraic containment is a finite list of coefficient equations in any
nonzero parametrization.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A polynomial vanishes if all coefficients up to a degree bound vanish. -/
theorem polynomial_eq_zero_of_coeff_le (p : Polynomial K) (d : ℕ)
    (hp : p.natDegree ≤ d) (hcoeff : ∀ n ≤ d, p.coeff n = 0) : p = 0 := by
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n ≤ d
  · exact hcoeff n hn
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (Nat.lt_of_not_ge hn))

/-- A finite list of coefficient equations tests containment. -/
theorem lineOn_iff_coeff_restrictLine_eq_zero [Infinite K] {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0) (f : Poly K) :
    LineOn f L ↔ ∀ n ≤ f.totalDegree, (restrictLine f a v).coeff n = 0 := by
  rw [lineOn_iff_restrictLine_eq_zero _ _ _ ha _ hv hv0]
  constructor
  · intro h n hn
    rw [h, Polynomial.coeff_zero]
  · exact polynomial_eq_zero_of_coeff_le _ _ (restrictLine_natDegree_le f a v)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
