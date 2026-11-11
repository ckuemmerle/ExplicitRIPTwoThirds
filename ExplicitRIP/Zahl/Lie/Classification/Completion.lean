/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Pencils.Affine

/-!
# Completion of cross-contact families

Contact polarity completes two internally independent cross-contact sets to
a maximal complementary pair. An internal contact instead forces both
sets into the pencil determined by two spheres.
-/

public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

namespace Lie.Classification

/-- Every set is contained in its double contact polar. -/
theorem subset_commonContacts_commonContacts (A : Set (Sphere F)) :
    A ⊆ commonContacts (commonContacts A) := by
  intro S hS T hT
  exact sphereContact_symm (hT S hS)

/-- Two independent spheres prevent contacts between distinct members of their polar. -/
theorem commonContacts_independent (hn : ¬ IsSquare (-1 : F))
    (A : Set (Sphere F)) (hA : 1 < A.encard)
    (hind : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ ExplicitRIP.SphereContact S T) :
    ∀ S ∈ commonContacts A, ∀ T ∈ commonContacts A,
      S ≠ T → ¬ ExplicitRIP.SphereContact S T := by
  intro S hS T hT hne hc
  obtain ⟨U, V, hU, hV, hUV⟩ := Set.one_lt_encard_iff.mp hA
  have hP := affinePencil_isContactPencil hn S T hne hc
  have hmem (W : Sphere F) (hW : W ∈ A) : W ∈ affinePencil S T := by
    rw [← common_contacts_eq_affinePencil hn S T hne hc]
    exact ⟨sphereContact_symm (hS W hW), sphereContact_symm (hT W hW)⟩
  exact hind U hU V hV hUV (hP.1 U (hmem U hU) V (hmem V hV))

/-- One contacting pair on one side forces both cross-contact families into its pencil. -/
theorem union_subset_pencil_of_contact (hn : ¬ IsSquare (-1 : F))
    (A B : Set (Sphere F)) (hB : 1 < B.encard)
    (hcross : ∀ S ∈ A, ∀ T ∈ B, ExplicitRIP.SphereContact S T)
    {S T : Sphere F} (hS : S ∈ A) (hT : T ∈ A) (hne : S ≠ T)
    (hc : ExplicitRIP.SphereContact S T) :
    ∃ P : Set (Sphere F), ExplicitRIP.IsContactPencil P ∧ A ∪ B ⊆ P := by
  let P := affinePencil S T
  have hP : ExplicitRIP.IsContactPencil P := affinePencil_isContactPencil hn S T hne hc
  have hBP : B ⊆ P := by
    intro U hU
    change U ∈ affinePencil S T
    rw [← common_contacts_eq_affinePencil hn S T hne hc]
    exact ⟨sphereContact_symm (hcross S hS U hU),
      sphereContact_symm (hcross T hT U hU)⟩
  obtain ⟨U, V, hU, hV, hUV⟩ := Set.one_lt_encard_iff.mp hB
  have heq := eq_affinePencil_of_two_mem hn hP hUV (hBP hU) (hBP hV)
  refine ⟨P, hP, Set.union_subset ?_ hBP⟩
  intro W hW
  rw [heq, ← common_contacts_eq_affinePencil hn U V hUV
    (hP.1 U (hBP hU) V (hBP hV))]
  exact ⟨hcross W hW U hU, hcross W hW V hV⟩

end Lie.Classification

/-- Contact polarity gives the full complementary-pair predicate. -/
theorem complementaryConicPair_of_cross_contact
    (hn : ¬ IsSquare (-1 : F)) (A B : Set (Sphere F))
    (hA : 3 ≤ A.encard) (hB : 3 ≤ B.encard)
    (hcross : ∀ S ∈ A, ∀ T ∈ B, ExplicitRIP.SphereContact S T)
    (hindA : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ ExplicitRIP.SphereContact S T)
    (hindB : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → ¬ ExplicitRIP.SphereContact S T) :
    ExplicitRIP.IsComplementaryConicPair (commonContacts (commonContacts A))
      (commonContacts A) ∧
      A ⊆ commonContacts (commonContacts A) ∧ B ⊆ commonContacts A := by
  have hAC := Lie.Classification.subset_commonContacts_commonContacts A
  have hBC' : B ⊆ commonContacts A := by
    intro T hT S hS
    exact sphereContact_symm (hcross S hS T hT)
  have hA₂ : 1 < A.encard := lt_of_lt_of_le (by norm_num) hA
  have hB₂ : 1 < B.encard := lt_of_lt_of_le (by norm_num) hB
  have hindC' := Lie.Classification.commonContacts_independent hn A hA₂ hindA
  have hindB' := Lie.Classification.commonContacts_independent hn B hB₂ hindB
  refine ⟨?_, hAC, hBC'⟩
  refine ⟨⟨hA.trans (Set.encard_mono hAC), hB.trans (Set.encard_mono hBC'),
    fun S hS T hT => hS T hT, ?_, hindC'⟩, ?_, ?_⟩
  · intro S hS T hT hne
    exact hindB' S (fun U hU => hS U (hBC' hU))
      T (fun U hU => hT U (hBC' hU)) hne
  · intro S hS hgood
    apply hS
    intro T hT
    exact hgood.2.2.1 S (Set.mem_insert S _) T hT
  · intro T hT hgood
    apply hT
    intro S hS
    exact sphereContact_symm (hgood.2.2.1 S (hAC hS) T (Set.mem_insert T _))

/-- A complete cross-contact relation gives one pencil or a complementary pair. -/
theorem cross_contact_pencil_or_complementaryConicPair
    (hn : ¬ IsSquare (-1 : F)) (A B : Set (Sphere F))
    (hA : 3 ≤ A.encard) (hB : 3 ≤ B.encard)
    (hcross : ∀ S ∈ A, ∀ T ∈ B, ExplicitRIP.SphereContact S T) :
    (∃ P : Set (Sphere F), ExplicitRIP.IsContactPencil P ∧ A ∪ B ⊆ P) ∨
      ∃ C C' : Set (Sphere F), ExplicitRIP.IsComplementaryConicPair C C' ∧
        A ⊆ C ∧ B ⊆ C' := by
  classical
  by_cases hindA : ∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ ExplicitRIP.SphereContact S T
  · by_cases hindB : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → ¬ ExplicitRIP.SphereContact S T
    · exact Or.inr ⟨_, _,
        complementaryConicPair_of_cross_contact hn A B hA hB hcross hindA hindB⟩
    · push Not at hindB
      obtain ⟨S, hS, T, hT, hne, hc⟩ := hindB
      obtain ⟨P, hP, hsub⟩ := Lie.Classification.union_subset_pencil_of_contact hn B A
        (lt_of_lt_of_le (by norm_num) hA)
        (fun T hT S hS => sphereContact_symm (hcross S hS T hT)) hS hT hne hc
      exact Or.inl ⟨P, hP, by simpa only [Set.union_comm] using hsub⟩
  · push Not at hindA
    obtain ⟨S, hS, T, hT, hne, hc⟩ := hindA
    exact Or.inl (Lie.Classification.union_subset_pencil_of_contact hn A B
      (lt_of_lt_of_le (by norm_num) hB) hcross hS hT hne hc)

end ExplicitRIP.Zahl
