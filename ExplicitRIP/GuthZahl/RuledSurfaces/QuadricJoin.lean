/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadricSmooth
public import ExplicitRIP.GuthZahl.RuledSurfaces.LineThroughFacts

/-!
# Joining a point of a quadric to a contained line

The tangent functional gives a linear equation for an intersection point on
the fixed line. If its slope vanishes, the parallel direction gives a contained
line instead. Thus the construction includes intersections at infinity.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

/-- A zero and a direction with all three restriction coefficients zero give a contained line. -/
theorem lineOn_lineThrough_of_coefficients {q : Poly K} (hdegree : q.totalDegree ≤ 2)
    (x v : Point K) (hv : v ≠ 0) (h0 : MvPolynomial.eval x q = 0)
    (h1 : tangentFunctional q x v = 0) (h2 : (restrictLine q x v).coeff 2 = 0) :
    LineOn q (lineThrough x v hv) := by
  apply (lineOn_lineThrough_iff q x v hv).mpr
  apply polynomial_eq_zero_of_coeff_le _ 2 ((restrictLine_natDegree_le _ _ _).trans hdegree)
  intro n hn
  interval_cases n
  · exact (coeff_zero_restrictLine q x v).trans h0
  · exact (coeff_one_restrictLine q x v).trans h1
  · exact h2

/-- Every zero of a quadratic polynomial lies on a contained line coplanar with any fixed
contained line, provided the fixed line is nonempty. -/
theorem exists_line_through_point_coplanar {q : Poly K}
    (hdegree : q.totalDegree ≤ 2) (A : Line K) (hA : LineOn q A)
    (x : Point K) (hx : MvPolynomial.eval x q = 0) :
    ∃ L : Line K, x ∈ L.1 ∧ LineOn q L ∧ Coplanar L A := by
  by_cases hxA : x ∈ A.1
  · exact ⟨A, hxA, hA, coplanar_self A⟩
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization A
  let φ := tangentFunctional q x
  by_cases hβ : φ v = 0
  · refine ⟨lineThrough x v hv0, base_mem_lineThrough x v hv0, ?_,
      coplanar_lineThrough_of_direction x v hv hv0⟩
    apply lineOn_lineThrough_of_coefficients hdegree x v hv0 hx hβ
    rw [coeff_restrictLine_eq_of_totalDegree_le hdegree x a v,
      hA a ha v hv, Polynomial.coeff_zero]
  · let t : K := -(φ (a - x)) / φ v
    let y : Point K := a + t • v
    have hyA : y ∈ A.1 := (hparam y).mpr ⟨t, rfl⟩
    have hv' : y - x ≠ (0 : Point K) := sub_ne_zero.mpr
      (fun h => hxA (h ▸ hyA))
    let L := lineThrough x (y - x) hv'
    have hxL : x ∈ L.1 := base_mem_lineThrough _ _ _
    have hyL : y ∈ L.1 := (mem_lineThrough _ _ _ hv').mpr
      ⟨1, by simp only [one_smul]; abel⟩
    have hφ : φ (y - x) = 0 := by
      have heq : y - x = (a - x) + t • v := by dsimp only [y]; abel
      rw [heq, map_add, map_smul]
      change φ (a - x) + t * φ v = 0
      dsimp only [t]
      rw [div_mul_cancel₀ _ hβ, add_neg_cancel]
    have hL : LineOn q L := by
      apply (lineOn_lineThrough_iff q x (y - x) hv').mpr
      apply polynomial_eq_zero_of_degree_le_two
      · exact (restrictLine_natDegree_le _ _ _).trans hdegree
      · exact (coeff_zero_restrictLine q x (y - x)).trans hx
      · exact (coeff_one_restrictLine q x (y - x)).trans hφ
      · rw [eval_restrictLine, one_smul]
        have heq : x + (y - x) = y := by abel
        rw [heq]
        exact eval_eq_zero_of_lineOn hA hyA
    have hLA : L ≠ A := fun h => hxA (h ▸ hxL)
    exact ⟨L, hxL, hL, coplanar_of_mem_of_ne hyL hyA hLA⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
