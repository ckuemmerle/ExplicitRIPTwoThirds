/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Pruning.Deletion
public import ExplicitRIP.Zahl.Incidence.Moments.FixedSize
public import ExplicitRIP.Zahl.Incidence.Pruning.Counting
public import ExplicitRIP.Zahl.Lie.Classification.Geometry
public import ExplicitRIP.Zahl.Geometry.QuadricIncidence

/-! # Finite incidence bookkeeping for the two-rich estimates -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
lemma chartImage_mono {F : Type*} [Field F] {S T : Finset (HLine F)}
    (h : S ⊆ T) : chartImage S ⊆ chartImage T := Finset.image_subset_image h

open Classical in
lemma chartImage_union {F : Type*} [Field F]
    [DecidableEq (HLine F)] [DecidableEq (ChartLine (QuadraticExtension F))]
    (S T : Finset (HLine F)) :
    chartImage (S ∪ T) = chartImage S ∪ chartImage T := by
  ext l
  simp only [chartImage, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨m, hm | hm, heq⟩
    · exact Or.inl ⟨m, hm, heq⟩
    · exact Or.inr ⟨m, hm, heq⟩
  · rintro (⟨m, hm, heq⟩ | ⟨m, hm, heq⟩)
    · exact ⟨m, Or.inl hm, heq⟩
    · exact ⟨m, Or.inr hm, heq⟩

open Classical in
lemma chartImage_disjoint {F : Type*} [Field F] {S T : Finset (HLine F)}
    (h : Disjoint S T) : Disjoint (chartImage S) (chartImage T) := by
  apply Finset.disjoint_left.mpr
  intro l hl hl'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hl'
  exact Finset.disjoint_left.mp h hr (HLine.toChart_injective heq ▸ hb)

open Classical in
lemma rulingCount_mono {K : Type*} [Field K] (Q : SplitQuadric K) (side : Bool)
    {S T : Finset (ChartLine K)} (h : S ⊆ T) :
    rulingCount Q side S ≤ rulingCount Q side T :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

open Classical in
lemma bichromaticPoints_comm {K : Type*} [CommRing K] (R B : Finset (ChartLine K)) :
    bichromaticPoints R B = bichromaticPoints B R := by
  ext w
  exact and_comm

open Classical in
lemma sum_ncard_inter {α β : Type*} [Finite α] (S : Finset β)
    (P : Set α) (I : β → Set α) :
    (∑ l ∈ S, (P ∩ I l).ncard) =
      ∑ w ∈ P.toFinite.toFinset, (S.filter (fun l => w ∈ I l)).card := by
  have heq (l : β) : (P ∩ I l).ncard =
      (P.toFinite.toFinset.filter (fun w => w ∈ I l)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter,
      Set.Finite.mem_toFinset]
  simp_rw [heq]
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun l w => w ∈ I l)

open Classical in
lemma sum_ncard_inter_le {α β : Type*} [Finite α] (S : Finset β)
    (P : Set α) (I : β → Set α) (k : ℕ)
    (h : ∀ w ∈ P, (S.filter (fun l => w ∈ I l)).card ≤ k) :
    (∑ l ∈ S, (P ∩ I l).ncard) ≤ P.ncard * k := by
  rw [sum_ncard_inter]
  calc
    _ ≤ ∑ _w ∈ P.toFinite.toFinset, k := Finset.sum_le_sum fun w hw =>
      h w ((Set.Finite.mem_toFinset _).mp hw)
    _ = P.ncard * k := by rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card]

open Classical in
lemma ncard_le_sum_inter {α β : Type*} [Finite α] (S : Finset β)
    (P : Set α) (I : β → Set α)
    (h : ∀ w ∈ P, ∃ l ∈ S, w ∈ I l) :
    P.ncard ≤ ∑ l ∈ S, (P ∩ I l).ncard := by
  rw [sum_ncard_inter, Set.ncard_eq_toFinset_card P]
  calc
    _ = ∑ _w ∈ P.toFinite.toFinset, 1 := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun w hw => by
      obtain ⟨l, hl, hwl⟩ := h w ((Set.Finite.mem_toFinset _).mp hw)
      exact Finset.one_le_card.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hwl⟩⟩

open Classical in
lemma same_ruling_through_le_one {K : Type*} [Field K] (Q : SplitQuadric K)
    (side : Bool) (S : Finset (ChartLine K))
    (hS : ∀ l ∈ S, inRuling Q side l) (w : Point K) :
    (S.filter (fun l => w ∈ linePoints l)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl m hm
  obtain ⟨hl, hwl⟩ := Finset.mem_filter.mp hl
  obtain ⟨hm, hwm⟩ := Finset.mem_filter.mp hm
  by_contra hne
  exact not_coplanar_of_same_ruling Q side l m (hS l hl) (hS m hm) hne
    ((coplanar_iff_intersects_or_parallel l m).mpr (Or.inl ⟨w, hwl, hwm⟩))

end ExplicitRIP.Zahl
