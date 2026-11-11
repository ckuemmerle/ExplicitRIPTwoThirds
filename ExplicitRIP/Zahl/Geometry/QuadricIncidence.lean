/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.QuadricIncidence.Roots
public import ExplicitRIP.Zahl.Geometry.QuadricIncidence.Classification
public import ExplicitRIP.Zahl.Geometry.Rulings

/-!
# Incidences with a split quadric

Every contained line belongs to one of the two rulings. At most two such lines
pass through any point, and a noncontained line has at most four incidences
with a finite family of contained lines, counted with point multiplicity.
-/

public section

namespace ExplicitRIP.Zahl

open Polynomial

open Classical in
/-- At most two contained lines pass through a point. -/
theorem quadric_point_line_count_le_two {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K)
    (L : Finset (ChartLine K)) (w : Point K) :
    (L.filter (fun l => quadricContains Q l ∧ w ∈ linePoints l)).card ≤ 2 := by
  have hcard (side : Bool) :
      (L.filter (fun l => inRuling Q side l ∧ w ∈ linePoints l)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    obtain ⟨_, hl, hwl⟩ := Finset.mem_filter.mp hl
    obtain ⟨_, hm, hwm⟩ := Finset.mem_filter.mp hm
    by_contra hne
    exact not_coplanar_of_same_ruling Q side l m hl hm hne
      ((coplanar_iff_intersects_or_parallel l m).mpr (Or.inl ⟨w, hwl, hwm⟩))
  have hsub : (L.filter (fun l => quadricContains Q l ∧ w ∈ linePoints l)) ⊆
      (L.filter (fun l => inRuling Q false l ∧ w ∈ linePoints l)) ∪
        (L.filter (fun l => inRuling Q true l ∧ w ∈ linePoints l)) := by
    intro l hl
    obtain ⟨hmem, hq, hw⟩ := Finset.mem_filter.mp hl
    rcases (quadricContains_iff_inRuling h2 Q l).mp hq with hleft | hright
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hmem, hleft, hw⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hmem, hright, hw⟩))
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (hcard false) (hcard true)))

/-- A noncontained line has at most four incidences with contained lines. -/
theorem external_quadric_incidence_le_four {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K)
    (L : Finset (ChartLine K)) (hL : ∀ l ∈ L, quadricContains Q l)
    (m : ChartLine K) (hm : ¬ quadricContains Q m) :
    (∑ l ∈ L, (linePoints l ∩ linePoints m).ncard) ≤ 4 := by
  classical
  obtain ⟨hfinite, hcount⟩ := quadric_intersection_ncard_le_two Q m hm
  let P := hfinite.toFinset
  have hP : P.card ≤ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hfinite] at hcount
    exact hcount
  have hintersection (l : ChartLine K) (hl : l ∈ L) :
      (linePoints l ∩ linePoints m).ncard =
        (P.filter (fun w => w ∈ linePoints l)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    change (w ∈ linePoints l ∧ w ∈ linePoints m) ↔
      w ∈ (P.filter (fun w => w ∈ linePoints l))
    rw [Finset.mem_filter]
    change (w ∈ linePoints l ∧ w ∈ linePoints m) ↔
      (w ∈ hfinite.toFinset ∧ w ∈ linePoints l)
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hwl, hwm⟩
      exact ⟨⟨hwm, hL l hl w hwl⟩, hwl⟩
    · rintro ⟨⟨hwm, _⟩, hwl⟩
      exact ⟨hwl, hwm⟩
  have hthrough (w : Point K) :
      (L.filter (fun l => w ∈ linePoints l)).card ≤ 2 := by
    have heq : L.filter (fun l => w ∈ linePoints l) =
        L.filter (fun l => quadricContains Q l ∧ w ∈ linePoints l) := by
      apply Finset.filter_congr
      intro l hl
      exact ⟨fun hw => ⟨hL l hl, hw⟩, And.right⟩
    rw [heq]
    exact quadric_point_line_count_le_two h2 Q L w
  calc
    (∑ l ∈ L, (linePoints l ∩ linePoints m).ncard) =
        ∑ l ∈ L, (P.filter (fun w => w ∈ linePoints l)).card :=
      Finset.sum_congr rfl hintersection
    _ = ∑ w ∈ P, (L.filter (fun l => w ∈ linePoints l)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun l w => w ∈ linePoints l)
    _ ≤ ∑ _w ∈ P, 2 := Finset.sum_le_sum (fun w _ => hthrough w)
    _ = P.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 hP
    _ = 4 := rfl

end ExplicitRIP.Zahl
