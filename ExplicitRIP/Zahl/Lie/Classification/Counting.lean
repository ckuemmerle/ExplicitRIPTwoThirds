/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Classification.Families
public import ExplicitRIP.Zahl.Lie.Pencils

/-!
# Counting classified contact pencils

The rich pencils split disjointly into point and direction pencils. Two-rich
pencils inject into unordered sphere pairs, and the direction contribution is
absorbed into the affine incidence estimates.
-/

public section

namespace ExplicitRIP.Zahl

section

variable {F : Type*} [Field F]

namespace Lie.Classification

open Classical in
/-- The sphere-line injection preserves the number of lines through a point. -/
theorem card_filter_sphereImage_point (h2 : (2 : F) ≠ 0)
    (S : Finset (Sphere F)) (w : Point (QuadraticExtension F)) :
    ((sphereImage S).filter (fun l => w ∈ linePoints l)).card =
      (S.filter (· ∈ pointPencil w)).card := by
  rw [sphereImage, Finset.filter_image]
  exact Finset.card_image_of_injective _ (sphereLine_injective h2)

/-- Any point incident to a chosen sphere line lies in the Heisenberg locus. -/
theorem richPoints_subset_heisenberg (S : Finset (Sphere F))
    (k : ℕ) (hk : 1 ≤ k) : richPoints (sphereImage S) k ⊆ heisenberg := by
  classical
  intro w hw
  have hpos : 0 < ((sphereImage S).filter (fun l => w ∈ linePoints l)).card :=
    lt_of_lt_of_le (by omega) hw
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  obtain ⟨hlS, hwl⟩ := Finset.mem_filter.mp hl
  obtain ⟨T, _hT, rfl⟩ := Finset.mem_image.mp hlS
  exact (sphereParameters T).linePoints_subset_heisenberg hwl

end Lie.Classification

/-- Rich pencils are counted by finite points and parallel directions. -/
theorem richPencilCount_eq_richCount_add_parallelRichCount [Fintype F]
    (hn : ¬ IsSquare (-1 : F)) (S : Finset (Sphere F)) (k : ℕ) (hk : 2 ≤ k) :
    ExplicitRIP.richPencilCount S k =
      richCount (sphereImage S) k + parallelRichCount S k := by
  classical
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  let R := richPoints (sphereImage S) k
  let D := {v : F × F × F | k ≤ (S.filter (· ∈ directionPencil v)).card}
  have hR : R ⊆ heisenberg := Lie.Classification.richPoints_subset_heisenberg S k (by omega)
  have hset :
      {P : Set (Sphere F) | ExplicitRIP.IsContactPencil P ∧
        k ≤ (S.filter (· ∈ P)).card} = pointPencil '' R ∪ directionPencil '' D := by
    ext P
    constructor
    · rintro ⟨hP, hPk⟩
      rcases (isContactPencil_iff_point_or_direction hn P).mp hP with
        ⟨w, _hw, rfl⟩ | ⟨v, rfl⟩
      · left
        refine ⟨w, ?_, rfl⟩
        change k ≤ ((sphereImage S).filter (fun l => w ∈ linePoints l)).card
        rw [Lie.Classification.card_filter_sphereImage_point h2]
        exact hPk
      · exact Or.inr ⟨v, hPk, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨pointPencil_isContactPencil hn w (hR hw), ?_⟩
        rw [← Lie.Classification.card_filter_sphereImage_point h2]
        exact hw
      · exact ⟨directionPencil_isContactPencil hn v, hv⟩
  have hdisj : Disjoint (pointPencil '' R) (directionPencil '' D) := by
    apply Set.disjoint_left.mpr
    rintro P ⟨w, hw, rfl⟩ ⟨v, _hv, heq⟩
    exact pointPencil_ne_directionPencil h2 w (hR hw) v heq.symm
  have hinj : Set.InjOn pointPencil R := (pointPencil_injOn h2).mono hR
  change {P : Set (Sphere F) | ExplicitRIP.IsContactPencil P ∧
    k ≤ (S.filter (· ∈ P)).card}.ncard = R.ncard + D.ncard
  rw [hset, Set.ncard_union_eq hdisj, hinj.ncard_image,
    Set.ncard_image_of_injective D (directionPencil_injective h2)]

/-- Two distinct members determine each two-rich pencil. -/
theorem richPencilCount_two_le_choose [Fintype F]
    (hn : ¬ IsSquare (-1 : F)) (S : Finset (Sphere F)) :
    ExplicitRIP.richPencilCount S 2 ≤ S.card.choose 2 := by
  classical
  let R := {P : Set (Sphere F) | ExplicitRIP.IsContactPencil P ∧
    2 ≤ (S.filter (· ∈ P)).card}
  have hpairs (P : R) : ∃ t : Finset (Sphere F), t ⊆ S.filter (· ∈ P.val) ∧ t.card = 2 :=
    Finset.exists_subset_card_eq P.property.2
  choose f hf hcard using hpairs
  have hfS (P : R) : f P ∈ S.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨(hf P).trans (Finset.filter_subset _ _), hcard P⟩
  let g : R → ↥(S.powersetCard 2) := fun P => ⟨f P, hfS P⟩
  have hg : Function.Injective g := by
    intro P Q heq
    have hfEq : f P = f Q := congrArg Subtype.val heq
    obtain ⟨U, V, hUV, hpair⟩ := Finset.card_eq_two.mp (hcard P)
    have hUP : U ∈ P.val := (Finset.mem_filter.mp (hf P (by simp [hpair]))).2
    have hVP : V ∈ P.val := (Finset.mem_filter.mp (hf P (by simp [hpair]))).2
    have hUQ : U ∈ Q.val := (Finset.mem_filter.mp (hf Q (by rw [← hfEq]; simp [hpair]))).2
    have hVQ : V ∈ Q.val := (Finset.mem_filter.mp (hf Q (by rw [← hfEq]; simp [hpair]))).2
    exact Subtype.ext (pencil_unique_of_two_mem hn P.property.1 Q.property.1
      hUV hUP hVP hUQ hVQ)
  have hbound := Nat.card_le_card_of_injective g hg
  change R.ncard ≤ S.card.choose 2
  calc
    R.ncard = Nat.card R := rfl
    _ ≤ Nat.card ↥(S.powersetCard 2) := hbound
    _ = S.card.choose 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard]

end

/-- The direction term costs one in the rich-pencil estimate. -/
theorem rich_pencil_bound_of_affine {F : Type*} [Field F] [Fintype F]
    (hn : ¬ IsSquare (-1 : F)) (S : Finset (Sphere F)) (k : ℕ)
    (hk : 3 ≤ k) (C : ℝ) (hC : 0 ≤ C)
    (haff : (richCount (sphereImage S) k : ℝ) ≤
      C * (S.card : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ))) :
    (ExplicitRIP.richPencilCount S k : ℝ) ≤
      (C + 1) * (S.card : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  by_cases hkn : k ≤ S.card
  · have hp := parallelRichCount_le_div S k (by omega)
    have hr := div_le_three_halves_scale S.card k (by omega) hkn
    rw [richPencilCount_eq_richCount_add_parallelRichCount hn S k (by omega),
      Nat.cast_add]
    calc
      (richCount (sphereImage S) k : ℝ) + (parallelRichCount S k : ℝ) ≤
          C * (S.card : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) +
            (S.card : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
        add_le_add haff (hp.trans hr)
      _ = _ := by ring
  · rw [richPencilCount_eq_zero_of_card_lt S k (by omega)]
    simp only [Nat.cast_zero]
    positivity

/-- The direction term costs one in the two-rich-pencil estimate. -/
theorem two_rich_pencil_bound_of_affine {F : Type*} [Field F] [Fintype F]
    (hn : ¬ IsSquare (-1 : F)) (S : Finset (Sphere F)) (C : ℝ)
    (haff : (richCount (sphereImage S) 2 : ℝ) ≤ C * (S.card : ℝ) ^ (3 / 2 : ℝ)) :
    (ExplicitRIP.richPencilCount S 2 : ℝ) ≤ (C + 1) * (S.card : ℝ) ^ (3 / 2 : ℝ) := by
  have hp := parallelRichCount_le_div S 2 (by decide)
  have hr := half_le_three_halves S.card
  rw [richPencilCount_eq_richCount_add_parallelRichCount hn S 2 (by decide), Nat.cast_add]
  norm_num only [Nat.cast_ofNat] at hp
  calc
    (richCount (sphereImage S) 2 : ℝ) + (parallelRichCount S 2 : ℝ) ≤
        C * (S.card : ℝ) ^ (3 / 2 : ℝ) + (S.card : ℝ) ^ (3 / 2 : ℝ) :=
      add_le_add haff (hp.trans hr)
    _ = _ := by ring

end ExplicitRIP.Zahl
