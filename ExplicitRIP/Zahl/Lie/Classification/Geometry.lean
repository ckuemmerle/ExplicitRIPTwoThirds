/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Classification.Families
public import ExplicitRIP.Zahl.Lie.Classification.Completion
public import ExplicitRIP.Zahl.Geometry.Rulings

/-!
# Plane pencils and complementary pairs from rulings

Planar Heisenberg lines form a parallel or concurrent family. The two rulings
of a split quadric give independent cross-contact sphere sets, which extend to
a maximal complementary pair without losing any selected spheres.
-/

public section

namespace ExplicitRIP.Zahl

namespace Lie.Classification

/-- Parallel normalized lines sharing a point have identical coefficients. -/
theorem eq_of_parallel_of_common_point {K : Type*} [CommRing K]
    {l m : ChartLine K} (hp : Parallel l m) {w : Point K}
    (hl : w ∈ linePoints l) (hm : w ∈ linePoints m) : l = m := by
  obtain ⟨hl1, hl2⟩ := (mem_linePoints_iff l w).mp hl
  obtain ⟨hm1, hm2⟩ := (mem_linePoints_iff m w).mp hm
  have hs := hl1.symm.trans hm1
  have ht := hl2.symm.trans hm2
  rw [hp.1] at hs
  rw [hp.2] at ht
  exact ChartLine.ext_of_coefficients (add_right_cancel hs) (add_right_cancel ht) hp.1 hp.2

end Lie.Classification

open Polynomial

open Classical in
/-- Planar Heisenberg lines are parallel or concurrent, with no other rich point. -/
theorem heisenberg_plane_pencil {F : Type*} [Field F]
    [Fact (¬ IsSquare (-1 : F))]
    (normal : Point (QuadraticExtension F)) (hnormal : normal ≠ 0)
    (offset : QuadraticExtension F) (L : Finset (HLine F))
    (hL : ∀ l ∈ L, planeContains normal offset l.toChart) :
    ((∀ l ∈ L, ∀ m ∈ L, Parallel l.toChart m.toChart) ∧
      ∀ w : Point (QuadraticExtension F),
        ((chartImage L).filter (fun l => w ∈ linePoints l)).card ≤ 1) ∨
      ∃ w₀ : Point (QuadraticExtension F),
        (∀ l ∈ L, w₀ ∈ linePoints l.toChart) ∧
          ∀ w : Point (QuadraticExtension F), w ≠ w₀ →
            ((chartImage L).filter (fun l => w ∈ linePoints l)).card ≤ 1 := by
  have hn : ¬ IsSquare (-1 : F) := Fact.out
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  have hchart (l : HLine F) : sphereLine (parametersSphere l) = l.toChart := by
    rw [sphereLine, sphereParameters_parametersSphere h2]
  by_cases hparallel : ∀ l ∈ L, ∀ m ∈ L, Parallel l.toChart m.toChart
  · refine Or.inl ⟨hparallel, ?_⟩
    intro w
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haL, hwa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbL, hwb⟩ := Finset.mem_filter.mp hb
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp haL
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hbL
    exact Lie.Classification.eq_of_parallel_of_common_point (hparallel l hl m hm) hwa hwb
  · push Not at hparallel
    obtain ⟨l, hl, m, hm, hnonparallel⟩ := hparallel
    have hne : parametersSphere l ≠ parametersSphere m := by
      intro heq
      have heq' := congrArg sphereLine heq
      rw [hchart, hchart] at heq'
      apply hnonparallel
      rw [heq']
      exact ⟨rfl, rfl⟩
    have hcontact (a : HLine F) (ha : a ∈ L) (b : HLine F) (hb : b ∈ L) :
        ExplicitRIP.SphereContact (parametersSphere a) (parametersSphere b) := by
      rw [sphereContact_iff_coplanar, hchart, hchart]
      exact coplanar_of_planeContains normal hnormal offset _ _ (hL a ha) (hL b hb)
    let P := affinePencil (parametersSphere l) (parametersSphere m)
    have hP : ExplicitRIP.IsContactPencil P :=
      affinePencil_isContactPencil hn _ _ hne (hcontact l hl m hm)
    have hmem (a : HLine F) (ha : a ∈ L) : parametersSphere a ∈ P := by
      change parametersSphere a ∈ affinePencil (parametersSphere l) (parametersSphere m)
      rw [← common_contacts_eq_affinePencil hn _ _ hne (hcontact l hl m hm)]
      exact ⟨hcontact a ha l hl, hcontact a ha m hm⟩
    rcases (isContactPencil_iff_point_or_direction hn P).mp hP with
      ⟨w₀, _hw₀, heq⟩ | ⟨v, heq⟩
    · have hconcur (a : HLine F) (ha : a ∈ L) : w₀ ∈ linePoints a.toChart := by
        have h := hmem a ha
        rw [heq] at h
        change w₀ ∈ linePoints (sphereLine (parametersSphere a)) at h
        rwa [hchart] at h
      refine Or.inr ⟨w₀, hconcur, ?_⟩
      intro w hw
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haL, hwa⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbL, hwb⟩ := Finset.mem_filter.mp hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp haL
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hbL
      by_contra hab
      obtain ⟨hfin, hcard⟩ := line_intersection_ncard_le_one a'.toChart b'.toChart hab
      exact hw ((Set.ncard_le_one hfin).mp hcard w ⟨hwa, hwb⟩
        w₀ ⟨hconcur a' ha', hconcur b' hb'⟩)
    · have hlP : parametersSphere l ∈ directionPencil v := heq ▸ hmem l hl
      have hmP : parametersSphere m ∈ directionPencil v := heq ▸ hmem m hm
      have hp := Lie.Classification.parallel_of_mem_directionPencil hlP hmP
      rw [hchart, hchart] at hp
      exact False.elim (hnonparallel hp)

open Classical in
/-- Both sphere-line rulings extend to a complementary conic pair. -/
theorem complementaryConicPair_of_rulings {F : Type*} [Field F]
    [Fact (¬ IsSquare (-1 : F))] (S : Finset (Sphere F))
    (Q : SplitQuadric (QuadraticExtension F))
    (h0 : 3 ≤ rulingCount Q false (sphereImage S))
    (h1 : 3 ≤ rulingCount Q true (sphereImage S)) :
    ∃ C C' : Set (Sphere F), ExplicitRIP.IsComplementaryConicPair C C' ∧
      (rulingCount Q false (sphereImage S) : ℝ) ≤
        ((S.filter (· ∈ C)).card : ℝ) ∧
      (rulingCount Q true (sphereImage S) : ℝ) ≤
        ((S.filter (· ∈ C')).card : ℝ) := by
  have hn : ¬ IsSquare (-1 : F) := Fact.out
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  let A := S.filter (fun T => inRuling Q false (sphereLine T))
  let B := S.filter (fun T => inRuling Q true (sphereLine T))
  rw [rulingCount_sphereImage] at h0 h1
  have hA : 3 ≤ (A : Set (Sphere F)).encard := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast h0
  have hB : 3 ≤ (B : Set (Sphere F)).encard := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast h1
  have hcross : ∀ U ∈ (A : Set (Sphere F)), ∀ V ∈ (B : Set (Sphere F)),
      ExplicitRIP.SphereContact U V := by
    intro U hU V hV
    exact (sphereContact_iff_coplanar U V).mpr
      (coplanar_of_opposite_ruling Q false _ _
        (Finset.mem_filter.mp hU).2 (Finset.mem_filter.mp hV).2)
  have hind (side : Bool) :
      ∀ U ∈ (S.filter (fun T => inRuling Q side (sphereLine T)) : Set (Sphere F)),
      ∀ V ∈ (S.filter (fun T => inRuling Q side (sphereLine T)) : Set (Sphere F)),
      U ≠ V → ¬ ExplicitRIP.SphereContact U V := by
    intro U hU V hV hne hc
    exact not_coplanar_of_same_ruling Q side _ _ (Finset.mem_filter.mp hU).2
      (Finset.mem_filter.mp hV).2 ((sphereLine_injective h2).ne hne)
      ((sphereContact_iff_coplanar U V).mp hc)
  obtain ⟨hpair, hAC, hBC'⟩ := complementaryConicPair_of_cross_contact hn
    (A : Set (Sphere F)) (B : Set (Sphere F)) hA hB hcross (hind false) (hind true)
  refine ⟨_, _, hpair, ?_, ?_⟩
  · have hbound : rulingCount Q false (sphereImage S) ≤
        (S.filter (· ∈ commonContacts (commonContacts (A : Set (Sphere F))))).card := by
      rw [rulingCount_sphereImage]
      apply Finset.card_le_card
      intro T hT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).1, hAC hT⟩
    exact_mod_cast hbound
  · have hbound : rulingCount Q true (sphereImage S) ≤
        (S.filter (· ∈ commonContacts (A : Set (Sphere F)))).card := by
      rw [rulingCount_sphereImage]
      apply Finset.card_le_card
      intro T hT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).1, hBC' hT⟩
    exact_mod_cast hbound

end ExplicitRIP.Zahl
