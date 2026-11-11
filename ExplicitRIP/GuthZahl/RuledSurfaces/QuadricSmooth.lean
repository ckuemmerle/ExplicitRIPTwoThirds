/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadricPlane
public import ExplicitRIP.GuthZahl.RuledSurfaces.PointLines
public import ExplicitRIP.GuthZahl.RuledSurfaces.Smooth

/-!
# Smooth affine points and line fibers of a quadric containing skew lines

A singular zero of a quadratic polynomial joins to every other zero by a
contained line. For an irreducible quadric this forces every contained line to
pass through the singular point. Thus a quadric with two skew lines is smooth
at every affine zero, and its tangent plane contains at most two lines.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A quadratic restriction with zero constant and linear coefficients vanishes
if it also vanishes at one. -/
theorem polynomial_eq_zero_of_degree_le_two (p : Polynomial K)
    (hdegree : p.natDegree ≤ 2) (h0 : p.coeff 0 = 0) (h1 : p.coeff 1 = 0)
    (heval : p.eval 1 = 0) : p = 0 := by
  have hsum := Polynomial.eval_eq_sum_range' (p := p) (n := 3) (by omega) (1 : K)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1,
    one_pow, mul_one, zero_add, add_zero, heval] at hsum
  apply polynomial_eq_zero_of_coeff_le p 2 hdegree
  intro n hn
  interval_cases n
  · exact h0
  · exact h1
  · exact hsum.symm

/-- The line joining a singular zero of a quadric to any other zero is contained. -/
theorem restrictLine_eq_zero_from_singular_zero {q : Poly K} (hdegree : q.totalDegree ≤ 2)
    (x y : Point K) (hx : MvPolynomial.eval x q = 0) (hy : MvPolynomial.eval y q = 0)
    (hsing : ∀ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i q) = 0) :
    restrictLine q x (y - x) = 0 := by
  apply polynomial_eq_zero_of_degree_le_two
  · exact (restrictLine_natDegree_le _ _ _).trans hdegree
  · rw [coeff_zero_restrictLine, hx]
  · rw [coeff_one_restrictLine]
    simp only [hsing, zero_mul, Finset.sum_const_zero]
  · rw [eval_restrictLine, one_smul]
    have heq : x + (y - x) = y := by abel
    rw [heq, hy]

/-- Every contained line of an irreducible quadric passes through each singular zero. -/
theorem mem_line_of_singular_zero [Infinite K] {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (x : Point K) (hx : MvPolynomial.eval x q = 0)
    (hsing : ∀ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i q) = 0)
    (A : Line K) (hA : LineOn q A) : x ∈ A.1 := by
  by_contra hxA
  obtain ⟨P, hP, hxP, hAP⟩ := exists_plane_containing_point_line x A
  have hlines := infinite_lines_joining_point_line x A hxA
  apply hlines
  apply (finite_lines_in_plane hq (by omega) P hP).subset
  rintro L ⟨hxL, y, hyA, hyL⟩
  have hxy : x ≠ y := fun h => hxA (h.symm ▸ hyA)
  have hv0 : y - x ≠ (0 : Point K) := sub_ne_zero.mpr hxy.symm
  have hvL := AffineSubspace.vsub_mem_direction hyL hxL
  refine ⟨?_, line_le_of_two_points hxy hxL hyL hxP (hAP hyA)⟩
  apply (lineOn_iff_restrictLine_eq_zero q _ _ hxL _ hvL hv0).mpr
  exact restrictLine_eq_zero_from_singular_zero hdegree.le x y hx
    (eval_eq_zero_of_lineOn hA hyA) hsing

/-- A quadric containing two skew lines has no singular affine zero. -/
theorem smooth_of_quadric_with_skew_lines [Infinite K] {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (A B : Line K) (hAB : ¬ Coplanar A B)
    (hA : LineOn q A) (hB : LineOn q B) (x : Point K) (hx : MvPolynomial.eval x q = 0) :
    ∃ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i q) ≠ 0 := by
  by_contra h
  push Not at h
  have hxA := mem_line_of_singular_zero hq hdegree x hx h A hA
  have hxB := mem_line_of_singular_zero hq hdegree x hx h B hB
  exact hAB (coplanar_of_mem_of_ne hxA hxB (ne_of_not_coplanar hAB))

/-- At most two contained lines pass through any affine point of a quadric containing skew lines. -/
theorem card_lines_through_point_le_two [Infinite K] {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (A B : Line K) (hAB : ¬ Coplanar A B)
    (hA : LineOn q A) (hB : LineOn q B) (x : Point K) (Ls : Finset (Line K))
    (hLs : ∀ L ∈ Ls, x ∈ L.1 ∧ LineOn q L) : Ls.card ≤ 2 := by
  by_cases hnonempty : Ls.Nonempty
  · obtain ⟨L, hL⟩ := hnonempty
    have hx := eval_eq_zero_of_lineOn (hLs L hL).2 (hLs L hL).1
    have hsmooth := smooth_of_quadric_with_skew_lines hq hdegree A B hAB hA hB x hx
    apply card_lines_in_plane_le_two hq hdegree (tangentPlane q x)
      (finrank_direction_tangentPlane q x hsmooth) Ls
    intro M hM
    exact ⟨(hLs M hM).2, line_le_tangentPlane (hLs M hM).2 (hLs M hM).1⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty]
    exact Nat.zero_le 2

end ExplicitRIP.GuthZahl.RuledSurfaces
end
