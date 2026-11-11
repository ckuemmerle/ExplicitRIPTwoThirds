/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Counting.Finite
public import ExplicitRIP.Zahl.Incidence.Counting.Coloring

/-!
# The half-average bound for bichromatic points

Choose two incident lines at every two-rich point. Their colors differ in half
of all two-colorings, and a disagreement witnesses a bichromatic point.
-/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
/-- Bichromatic points in disjoint subfamilies are two-rich in the ambient family. -/
theorem bichromaticPoints_subset_richPoints_two {K : Type*} [CommRing K]
    {L R B : Finset (ChartLine K)} (hR : R ⊆ L) (hB : B ⊆ L)
    (hd : Disjoint R B) : bichromaticPoints R B ⊆ richPoints L 2 := by
  classical
  rintro w ⟨⟨l, hl, hwl⟩, m, hm, hwm⟩
  apply (mem_richPoints_two_iff L w).mpr
  refine ⟨l, hR hl, m, hB hm, ?_, hwl, hwm⟩
  intro heq
  subst m
  exact Finset.disjoint_left.mp hd hl hm

open Classical in
/-- Two distinct coordinates of a two-coloring disagree with mean one half. -/
theorem finiteMean_two_colors_ne {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    finiteMean Finset.univ (fun χ : α → Fin 2 => if χ a ≠ χ b then (1 : ℝ) else 0) =
      1 / 2 := by
  classical
  rw [finiteMean_fun_apply_two a b hab
    (fun x y : Fin 2 => if x ≠ y then (1 : ℝ) else 0)]
  norm_num [finiteMean, Finset.expect_eq_sum_div_card, Fin.sum_univ_two]

open Classical in
/-- Differing witness colors give a bichromatic point. -/
theorem mem_bichromaticPoints_of_color_ne {K : Type*} [CommRing K]
    (L : Finset (ChartLine K)) (χ : ↥L → Fin 2) (w : Point K)
    (l m : ↥L) (hl : w ∈ linePoints l.val) (hm : w ∈ linePoints m.val)
    (hne : χ l ≠ χ m) :
    w ∈ bichromaticPoints (colorSample L χ) (L \ colorSample L χ) := by
  classical
  have hmem (a : ↥L) : a.val ∈ colorSample L χ ↔ (χ a).val = 0 := by
    rw [mem_colorSample_iff]
    exact ⟨fun h => h.choose_spec, fun h => ⟨a.property, h⟩⟩
  have hcolors : ((χ l).val = 0 ∧ (χ m).val ≠ 0) ∨
      ((χ m).val = 0 ∧ (χ l).val ≠ 0) := by
    have hval : (χ l).val ≠ (χ m).val := fun h => hne (Fin.ext h)
    have hlbound := (χ l).isLt
    have hmbound := (χ m).isLt
    omega
  rcases hcolors with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact ⟨⟨l.val, (hmem l).mpr h₀, hl⟩,
      m.val, Finset.mem_sdiff.mpr ⟨m.property, fun h => h₁ ((hmem m).mp h)⟩, hm⟩
  · exact ⟨⟨m.val, (hmem m).mpr h₀, hm⟩,
      l.val, Finset.mem_sdiff.mpr ⟨l.property, fun h => h₁ ((hmem l).mp h)⟩, hl⟩

open Classical in
/-- Uniform two-coloring retains at least half the two-rich points on average. -/
theorem mean_bichromatic_of_two_rich {K : Type*} [Field K]
    (L : Finset (ChartLine K)) :
    (richCount L 2 : ℝ) / 2 ≤
      finiteMean (Finset.univ : Finset (↥L → Fin 2))
        (fun χ => ((bichromaticPoints (colorSample L χ)
          (L \ colorSample L χ)).ncard : ℝ)) := by
  classical
  let P := (richPoints_finite L 2 le_rfl).toFinset
  have hPcard : P.card = richCount L 2 :=
    (Set.ncard_eq_toFinset_card (richPoints L 2) (richPoints_finite L 2 le_rfl)).symm
  have hw (w : ↥P) : ∃ l m : ↥L, l ≠ m ∧
      w.val ∈ linePoints l.val ∧ w.val ∈ linePoints m.val := by
    have hp : w.val ∈ richPoints L 2 :=
      (Set.Finite.mem_toFinset (richPoints_finite L 2 le_rfl)).mp w.property
    obtain ⟨l, hl, m, hm, hne, hwl, hwm⟩ := (mem_richPoints_two_iff L w.val).mp hp
    exact ⟨⟨l, hl⟩, ⟨m, hm⟩, fun h => hne (congrArg Subtype.val h), hwl, hwm⟩
  choose l m hne hl hm using hw
  have hpoint (χ : ↥L → Fin 2) :
      (∑ w : ↥P, if χ (l w) ≠ χ (m w) then (1 : ℝ) else 0) ≤
        ((bichromaticPoints (colorSample L χ) (L \ colorSample L χ)).ncard : ℝ) := by
    let T := (Finset.univ : Finset ↥P).filter (fun w => χ (l w) ≠ χ (m w))
    have hT : ((T.image Subtype.val : Finset (Point K)) : Set (Point K)) ⊆
        bichromaticPoints (colorSample L χ) (L \ colorSample L χ) := by
      intro w hwT
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwT
      exact mem_bichromaticPoints_of_color_ne L χ v.val (l v) (m v)
        (hl v) (hm v) (Finset.mem_filter.mp hv).2
    have hf : (bichromaticPoints (colorSample L χ) (L \ colorSample L χ)).Finite :=
      (richPoints_finite L 2 le_rfl).subset
        (bichromaticPoints_subset_richPoints_two (colorSample_subset L χ)
          Finset.sdiff_subset Finset.disjoint_sdiff)
    have hcard : T.card ≤ (bichromaticPoints (colorSample L χ)
        (L \ colorSample L χ)).ncard := by
      have hh := Set.ncard_le_ncard hT hf
      rw [Set.ncard_coe_finset,
        Finset.card_image_of_injective T Subtype.val_injective] at hh
      exact hh
    simpa only [Finset.sum_boole] using (Nat.cast_le (α := ℝ)).mpr hcard
  calc
    (richCount L 2 : ℝ) / 2 = ∑ _w : ↥P, (1 / 2 : ℝ) := by
      simp [hPcard, div_eq_mul_inv]
    _ = ∑ w : ↥P, finiteMean Finset.univ
        (fun χ : ↥L → Fin 2 => if χ (l w) ≠ χ (m w) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      exact (finiteMean_two_colors_ne (l w) (m w) (hne w)).symm
    _ = finiteMean Finset.univ (fun χ : ↥L → Fin 2 =>
        ∑ w : ↥P, if χ (l w) ≠ χ (m w) then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm _ _ _).symm
    _ ≤ _ := Finset.expect_le_expect (fun χ _ => hpoint χ)

end ExplicitRIP.Zahl
