/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadricParallel

/-!
# Incidence geometry of a quadric containing skew lines

There is no triangle of distinct pairwise coplanar contained lines. For a pair
of intersecting projective lines on the quadric, every contained line is
coplanar with one of the pair. These two facts give the two ruling classes.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

/-- Three distinct contained lines cannot pass through one affine point. -/
theorem not_three_lines_through_point {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (U V : Line K) (hUV : ¬ Coplanar U V)
    (hU : LineOn q U) (hV : LineOn q V) (A B C : Line K)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (x : Point K) (hxA : x ∈ A.1) (hxB : x ∈ B.1) (hxC : x ∈ C.1) : False := by
  classical
  have hcard := card_lines_through_point_le_two hq hdegree U V hUV hU hV x {A, B, C} (by
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨hxA, hA⟩
    · exact ⟨hxB, hB⟩
    · exact ⟨hxC, hC⟩)
  have hthree : ({A, B, C} : Finset (Line K)).card = 3 := by simp [hAB, hAC, hBC]
  omega

omit [Infinite K] in
/-- A pairwise coplanar triple with unequal first two directions is planar or concurrent. -/
theorem planar_or_concurrent_of_pairwise_coplanar (A B C : Line K) (hAB : A ≠ B)
    (hcAB : Coplanar A B) (hcAC : Coplanar A C) (hcBC : Coplanar B C)
    (hdAB : A.1.direction ≠ B.1.direction) :
    (∃ P : AffineSubspace K (Point K), Module.finrank K P.direction = 2 ∧
      A.1 ≤ P ∧ B.1 ≤ P ∧ C.1 ≤ P) ∨
      ∃ x : Point K, x ∈ A.1 ∧ x ∈ B.1 ∧ x ∈ C.1 := by
  obtain ⟨P, hP, hAP, hBP⟩ := hcAB
  obtain ⟨x, hxA, hxB⟩ :=
    (inter_nonempty_or_direction_eq_of_coplanar ⟨P, hP, hAP, hBP⟩).resolve_right hdAB
  by_cases hxC : x ∈ C.1
  · exact Or.inr ⟨x, hxA, hxB, hxC⟩
  left
  refine ⟨P, hP, hAP, hBP, ?_⟩
  have hcCA : Coplanar C A := (coplanar_comm C A).mpr hcAC
  have hcCB : Coplanar C B := (coplanar_comm C B).mpr hcBC
  by_cases hdCA : C.1.direction = A.1.direction
  · have hdCB : C.1.direction ≠ B.1.direction := fun h => hdAB (hdCA.symm.trans h)
    obtain ⟨y, hyC, hyB⟩ := (inter_nonempty_or_direction_eq_of_coplanar hcCB).resolve_right hdCB
    apply AffineSubspace.le_of_direction_le _ ⟨y, hyC, hBP hyB⟩
    rw [hdCA]
    exact AffineSubspace.direction_le hAP
  · obtain ⟨y, hyC, hyA⟩ := (inter_nonempty_or_direction_eq_of_coplanar hcCA).resolve_right hdCA
    by_cases hdCB : C.1.direction = B.1.direction
    · apply AffineSubspace.le_of_direction_le _ ⟨y, hyC, hAP hyA⟩
      rw [hdCB]
      exact AffineSubspace.direction_le hBP
    · obtain ⟨z, hzC, hzB⟩ := (inter_nonempty_or_direction_eq_of_coplanar hcCB).resolve_right hdCB
      have hyz : y ≠ z := by
        rintro rfl
        have hxy := line_inter_subsingleton _ _ hAB ⟨hxA, hxB⟩ ⟨hyA, hzB⟩
        exact hxC (hxy.symm ▸ hyC)
      exact line_le_of_two_points hyz hyC hzC (hAP hyA) (hBP hzB)

/-- Three distinct pairwise coplanar contained lines cannot lie on a quadric containing skew
lines. -/
theorem not_three_pairwise_coplanar_lines {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (U V : Line K) (hUV : ¬ Coplanar U V)
    (hU : LineOn q U) (hV : LineOn q V) (A B C : Line K)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (hcAB : Coplanar A B) (hcAC : Coplanar A C) (hcBC : Coplanar B C) : False := by
  have hcase (A B C : Line K) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
      (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
      (hcAB : Coplanar A B) (hcAC : Coplanar A C) (hcBC : Coplanar B C)
      (hdAB : A.1.direction ≠ B.1.direction) : False := by
    rcases planar_or_concurrent_of_pairwise_coplanar A B C hAB hcAB hcAC hcBC hdAB with
      ⟨P, hP, hAP, hBP, hCP⟩ | ⟨x, hxA, hxB, hxC⟩
    · exact not_three_lines_in_plane hq hdegree P hP A B C hAB hAC hBC hA hB hC hAP hBP hCP
    · exact not_three_lines_through_point hq hdegree U V hUV hU hV A B C hAB hAC hBC
        hA hB hC x hxA hxB hxC
  by_cases hdAB : A.1.direction = B.1.direction
  · by_cases hdAC : A.1.direction = C.1.direction
    · exact not_three_parallel_lines hq hdegree U V hUV hU hV A B C hAB hAC hBC
        hA hB hC hdAB hdAC
    · exact hcase A C B hAC hAB hBC.symm hA hC hB hcAC hcAB
        ((coplanar_comm C B).mpr hcBC) hdAC
  · exact hcase A B C hAB hAC hBC hA hB hC hcAB hcAC hcBC hdAB

/-- Every contained line is coplanar with one of two distinct coplanar contained lines. -/
theorem coplanar_or_coplanar_of_quadric {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (U V : Line K) (hUV : ¬ Coplanar U V)
    (hU : LineOn q U) (hV : LineOn q V) (A B : Line K)
    (hAB : A ≠ B) (hA : LineOn q A) (hB : LineOn q B) (hcAB : Coplanar A B)
    (N : Line K) (hN : LineOn q N) : Coplanar N A ∨ Coplanar N B := by
  by_contra h
  push Not at h
  obtain ⟨x, hxN⟩ := line_nonempty N
  have hxq := eval_eq_zero_of_lineOn hN hxN
  obtain ⟨L, hxL, hL, hcLA⟩ := exists_line_through_point_coplanar hdegree.le A hA x hxq
  obtain ⟨M, hxM, hM, hcMB⟩ := exists_line_through_point_coplanar hdegree.le B hB x hxq
  have hNL : N ≠ L := fun heq => h.1 (heq.symm ▸ hcLA)
  have hNM : N ≠ M := fun heq => h.2 (heq.symm ▸ hcMB)
  by_cases hLM : L = M
  · subst M
    have hLA : L ≠ A := by
      intro heq
      exact h.1 (coplanar_of_mem_of_ne hxN (heq ▸ hxL) (ne_of_not_coplanar h.1))
    have hLB : L ≠ B := by
      intro heq
      exact h.2 (coplanar_of_mem_of_ne hxN (heq ▸ hxL) (ne_of_not_coplanar h.2))
    exact not_three_pairwise_coplanar_lines hq hdegree U V hUV hU hV A B L hAB
      hLA.symm hLB.symm hA hB hL hcAB ((coplanar_comm A L).mpr hcLA)
      ((coplanar_comm B L).mpr hcMB)
  · exact not_three_lines_through_point hq hdegree U V hUV hU hV N L M hNL hNM hLM
      hN hL hM x hxN hxL hxM

end ExplicitRIP.GuthZahl.RuledSurfaces
end
