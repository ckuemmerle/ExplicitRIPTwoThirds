/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Surfaces.Bookkeeping

/-! # Plane and ruling incidence budgets for bichromatic pruning -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
lemma plane_bichromatic_degree_sum_le {K : Type*} [Field K] [Finite K]
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (normal : Point K) (hnormal : normal ≠ 0) (offset : K)
    (w₀ : Point K)
    (hthrough : ∀ w, w ≠ w₀ →
      (((R ∪ B).filter (planeContains normal offset)).filter
        (fun l => w ∈ linePoints l)).card ≤ 1) :
    (∑ l ∈ (R ∪ B).filter (planeContains normal offset),
      (bichromaticPoints R B ∩ linePoints l).ncard) ≤
        ((R ∪ B).filter (planeContains normal offset)).card + (R ∪ B).card := by
  let S := (R ∪ B).filter (planeContains normal offset)
  let T := (R ∪ B).filter (fun l => ¬ planeContains normal offset l)
  let X : Set (Point K) := {w | w ∈ bichromaticPoints R B ∧ w ≠ w₀ ∧
    (∑ j : Fin 3, normal j * w j) = offset}
  have hcover : ∀ w ∈ X, ∃ m ∈ T, w ∈ linePoints m := by
    rintro w ⟨⟨⟨r, hr, hwr⟩, b, hb, hwb⟩, hne, _⟩
    by_cases hpr : planeContains normal offset r
    · by_cases hpb : planeContains normal offset b
      · have heq := Finset.card_le_one.mp (hthrough w hne)
          r (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_union_left B hr, hpr⟩, hwr⟩)
          b (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_union_right R hb, hpb⟩, hwb⟩)
        exact False.elim (Finset.disjoint_left.mp hRB hr (heq ▸ hb))
      · exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_union_right R hb, hpb⟩, hwb⟩
    · exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_union_left B hr, hpr⟩, hwr⟩
  have hX : X.ncard ≤ (R ∪ B).card := by
    calc
      X.ncard ≤ ∑ m ∈ T, (X ∩ linePoints m).ncard :=
        ncard_le_sum_inter T X linePoints hcover
      _ ≤ ∑ _m ∈ T, 1 := Finset.sum_le_sum fun m hm => by
        have hsub : X ∩ linePoints m ⊆
            linePoints m ∩ {w | (∑ j : Fin 3, normal j * w j) = offset} :=
          fun _ hw => ⟨hw.2, hw.1.2.2⟩
        exact (Set.ncard_le_ncard hsub).trans
          (plane_intersection_ncard_le_one normal hnormal offset m
            (Finset.mem_filter.mp hm).2).2
      _ = T.card := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ (R ∪ B).card := Finset.card_filter_le _ _
  have hsum : (∑ l ∈ S, (X ∩ linePoints l).ncard) ≤ X.ncard := by
    simpa only [mul_one] using sum_ncard_inter_le S X linePoints 1
      (fun w hw => hthrough w hw.2.1)
  have hline (l : ChartLine K) (hl : l ∈ S) :
      (bichromaticPoints R B ∩ linePoints l).ncard ≤ 1 + (X ∩ linePoints l).ncard := by
    have hsub : bichromaticPoints R B ∩ linePoints l ⊆ {w₀} ∪ (X ∩ linePoints l) := by
      intro w hw
      by_cases h : w = w₀
      · exact Or.inl h
      · exact Or.inr ⟨⟨hw.1, h, (Finset.mem_filter.mp hl).2 w hw.2⟩, hw.2⟩
    exact (Set.ncard_le_ncard hsub).trans (by simpa only [Set.ncard_singleton]
      using (Set.ncard_union_le ({w₀} : Set (Point K)) (X ∩ linePoints l)))
  calc
    _ ≤ ∑ l ∈ S, (1 + (X ∩ linePoints l).ncard) := Finset.sum_le_sum hline
    _ = S.card + ∑ l ∈ S, (X ∩ linePoints l).ncard := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ S.card + (R ∪ B).card := Nat.add_le_add_left (hsum.trans hX) _

open Classical in
lemma heisenberg_plane_through_le_one {F : Type*} [Field F]
    [Fact (¬ IsSquare (-1 : F))]
    (L : Finset (HLine F)) (normal : Point (QuadraticExtension F))
    (hnormal : normal ≠ 0) (offset : QuadraticExtension F) :
    ∃ w₀ : Point (QuadraticExtension F), ∀ w, w ≠ w₀ →
      (((chartImage L).filter (planeContains normal offset)).filter
        (fun l => w ∈ linePoints l)).card ≤ 1 := by
  obtain ⟨T, _, hT⟩ := exists_chartImage_subfamily L
    (Finset.filter_subset (planeContains normal offset) (chartImage L))
  have hplane (l : HLine F) (hl : l ∈ T) : planeContains normal offset l.toChart := by
    have hm : l.toChart ∈ chartImage T := Finset.mem_image.mpr ⟨l, hl, rfl⟩
    rw [hT] at hm
    exact (Finset.mem_filter.mp hm).2
  rcases heisenberg_plane_pencil normal hnormal offset T hplane with h | ⟨w₀, _, h⟩
  · exact ⟨0, fun w _ => hT ▸ h.2 w⟩
  · exact ⟨w₀, fun w hw => hT ▸ h w hw⟩

open Classical in
lemma ruling_bichromatic_degree_sum_le {K : Type*} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K) (side : Bool)
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B) :
    (∑ l ∈ R.filter (inRuling Q side),
      (bichromaticPoints R B ∩ linePoints l).ncard) ≤
        rulingCount Q side R * rulingCount Q (!side) B + 2 * B.card := by
  let S := R.filter (inRuling Q side)
  let T := B.filter (inRuling Q (!side))
  let U := B.filter (fun m => ¬ quadricContains Q m)
  let X : Set (Point K) := {w | quadricValue Q w = 0 ∧ ∃ m ∈ U, w ∈ linePoints m}
  have hX : X.ncard ≤ 2 * B.card := by
    calc
      X.ncard ≤ ∑ m ∈ U, (X ∩ linePoints m).ncard :=
        ncard_le_sum_inter U X linePoints (fun _ hw => hw.2)
      _ ≤ ∑ _m ∈ U, 2 := Finset.sum_le_sum fun m hm => by
        exact (Set.ncard_le_ncard (fun _ hw => ⟨hw.2, hw.1.1⟩ :
          X ∩ linePoints m ⊆ linePoints m ∩ {w | quadricValue Q w = 0})).trans
            (quadric_intersection_ncard_le_two Q m (Finset.mem_filter.mp hm).2).2
      _ = 2 * U.card := by simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ 2 * B.card := Nat.mul_le_mul_left _ (Finset.card_filter_le _ _)
  have hsumX : (∑ l ∈ S, (X ∩ linePoints l).ncard) ≤ X.ncard := by
    simpa only [mul_one] using sum_ncard_inter_le S X linePoints 1
      (fun w _ => same_ruling_through_le_one Q side S
        (fun _ hl => (Finset.mem_filter.mp hl).2) w)
  have hline (l : ChartLine K) (hl : l ∈ S) :
      (bichromaticPoints R B ∩ linePoints l).ncard ≤ T.card + (X ∩ linePoints l).ncard := by
    let Y := bichromaticPoints {l} T
    have hY : Y.ncard ≤ T.card := by
      calc
        Y.ncard ≤ ∑ m ∈ T, (Y ∩ linePoints m).ncard :=
          ncard_le_sum_inter T Y linePoints (fun _ hw => hw.2)
        _ ≤ ∑ _m ∈ T, 1 := Finset.sum_le_sum fun m hm => by
          have hne : l ≠ m := fun heq => Finset.disjoint_left.mp hRB
            (Finset.mem_filter.mp hl).1 (heq ▸ (Finset.mem_filter.mp hm).1)
          apply (Set.ncard_le_ncard (t := linePoints l ∩ linePoints m) ?_).trans
            (line_intersection_ncard_le_one l m hne).2
          rintro w ⟨⟨⟨r, hr, hwr⟩, _⟩, hwm⟩
          have : r = l := Finset.mem_singleton.mp hr
          exact ⟨this ▸ hwr, hwm⟩
        _ = T.card := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have hsub : bichromaticPoints R B ∩ linePoints l ⊆ Y ∪ (X ∩ linePoints l) := by
      rintro w ⟨⟨_, m, hm, hwm⟩, hwl⟩
      by_cases hqm : quadricContains Q m
      · have hrm : inRuling Q (!side) m := by
          have hnot : ¬ inRuling Q side m := by
            intro hsame
            have hne : l ≠ m := fun heq => Finset.disjoint_left.mp hRB
              (Finset.mem_filter.mp hl).1 (heq ▸ hm)
            exact not_coplanar_of_same_ruling Q side l m
              (Finset.mem_filter.mp hl).2 hsame hne
              ((coplanar_iff_intersects_or_parallel l m).mpr (Or.inl ⟨w, hwl, hwm⟩))
          have hcases := (quadricContains_iff_inRuling h2 Q m).mp hqm
          cases side with
          | false => exact hcases.resolve_left hnot
          | true => exact hcases.resolve_right hnot
        exact Or.inl ⟨⟨l, Finset.mem_singleton_self l, hwl⟩,
          m, Finset.mem_filter.mpr ⟨hm, hrm⟩, hwm⟩
      · have hql : quadricContains Q l :=
          (quadricContains_iff_inRuling h2 Q l).mpr (by
            have hrl := (Finset.mem_filter.mp hl).2
            cases side with
            | false => exact Or.inl hrl
            | true => exact Or.inr hrl)
        exact Or.inr ⟨⟨hql w hwl, m, Finset.mem_filter.mpr ⟨hm, hqm⟩, hwm⟩, hwl⟩
    exact (Set.ncard_le_ncard hsub).trans ((Set.ncard_union_le _ _).trans
      (Nat.add_le_add_right hY _))
  calc
    _ ≤ ∑ l ∈ S, (T.card + (X ∩ linePoints l).ncard) := Finset.sum_le_sum hline
    _ = S.card * T.card + ∑ l ∈ S, (X ∩ linePoints l).ncard := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_left (hsumX.trans hX) _

end ExplicitRIP.Zahl
