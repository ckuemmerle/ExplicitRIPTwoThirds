/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Surfaces.Budget
public import ExplicitRIP.Zahl.Lie.Classification.Geometry
public import ExplicitRIP.Zahl.Geometry.QuadricIncidence

/-! # Plane and quadric budgets for three-rich points -/

public section

namespace ExplicitRIP.Zahl


open Classical in
/-- The total three-rich degree of the planar lines is at most four times
 the size of the ambient Heisenberg family. -/
lemma plane_three_rich_degree_sum_le {F : Type*} [Field F]
    [Fact (¬ IsSquare (-1 : F))] (L : Finset (HLine F))
    (normal : Point (QuadraticExtension F)) (hnormal : normal ≠ 0)
    (offset : QuadraticExtension F) :
    (∑ l ∈ (chartImage L).filter (planeContains normal offset),
      (richPoints (chartImage L) 3 ∩ linePoints l).ncard) ≤ 4 * (chartImage L).card := by
  classical
  let R := (chartImage L).filter (planeContains normal offset)
  let S := L.filter (fun l => planeContains normal offset l.toChart)
  have hS : chartImage S = R := by
    simp only [S, R, chartImage, Finset.filter_image]
  have hplane : ∀ l ∈ S, planeContains normal offset l.toChart :=
    fun _ hl => (Finset.mem_filter.mp hl).2
  obtain ⟨E, hE, hthrough⟩ : ∃ E : Finset (Point (QuadraticExtension F)), E.card ≤ 1 ∧
      ∀ w, w ∉ E → (R.filter (fun l => w ∈ linePoints l)).card ≤ 1 := by
    rcases heisenberg_plane_pencil normal hnormal offset S hplane with hpar | ⟨w₀, _, hw₀⟩
    · refine ⟨∅, by simp only [Finset.card_empty, zero_le], ?_⟩
      intro w _
      simpa only [hS] using hpar.2 w
    · refine ⟨{w₀}, by simp only [Finset.card_singleton, le_refl], ?_⟩
      intro w hw
      have hw' : w ≠ w₀ := by simpa only [Finset.mem_singleton] using hw
      simpa only [hS] using hw₀ w hw'
  have hbudget := surface_incidence_budget (chartImage L) R
    {w | (∑ j : Fin 3, normal j * w j) = offset} E 1 1 (by omega)
    (fun l hl => (Finset.mem_filter.mp hl).2) hthrough
    (by
      intro m hm
      simp only [Finset.mem_sdiff, R, Finset.mem_filter] at hm
      exact plane_intersection_ncard_le_one normal hnormal offset m
        (fun hc => hm.2 ⟨hm.1, hc⟩))
  have hRcard : R.card ≤ (chartImage L).card := Finset.card_filter_le _ _
  calc
    _ ≤ R.card * E.card + 1 * 1 * (chartImage L).card := hbudget
    _ ≤ R.card * 1 + 1 * 1 * (chartImage L).card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left R.card hE) _
    _ ≤ 4 * (chartImage L).card := by omega

open Classical in
/-- The factor four counts both rulings and both intersections of an outside line. -/
lemma quadric_three_rich_degree_sum_le {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (T : Finset (ChartLine K)) (Q : SplitQuadric K) :
    (∑ l ∈ T.filter (quadricContains Q),
      (richPoints T 3 ∩ linePoints l).ncard) ≤ 4 * T.card := by
  classical
  let R := T.filter (quadricContains Q)
  have hthrough (w : Point K) (_ : w ∉ (∅ : Finset (Point K))) :
      (R.filter (fun l => w ∈ linePoints l)).card ≤ 2 := by
    simpa only [R, Finset.filter_filter] using quadric_point_line_count_le_two h2 Q T w
  have hbudget := surface_incidence_budget T R {w | quadricValue Q w = 0} ∅ 2 2 le_rfl
    (fun l hl => (Finset.mem_filter.mp hl).2) hthrough
    (by
      intro m hm
      simp only [Finset.mem_sdiff, R, Finset.mem_filter] at hm
      exact quadric_intersection_ncard_le_two Q m (fun hc => hm.2 ⟨hm.1, hc⟩))
  simpa only [Finset.card_empty, mul_zero, zero_add] using hbudget

end ExplicitRIP.Zahl
