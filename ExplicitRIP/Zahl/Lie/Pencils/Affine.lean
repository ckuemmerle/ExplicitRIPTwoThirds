/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Correspondence

/-!
# Affine contact pencils

Common contacts of two distinct contacting spheres form their affine null line.
The maximality condition consequently characterizes these affine lines.
-/

public section

namespace ExplicitRIP.Zahl

@[ext]
theorem HLine.ext {F : Type*} {l m : HLine F} (ha : l.a = m.a) (hb : l.b = m.b)
    (hc : l.c = m.c) (hd : l.d = m.d) : l = m := by
  cases l
  cases m
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

variable {F : Type*} [Field F]

theorem sphereContact_refl (S : Sphere F) : ExplicitRIP.SphereContact S S := by
  simp only [ExplicitRIP.SphereContact, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem sphereContact_symm {S T : Sphere F} (h : ExplicitRIP.SphereContact S T) :
    ExplicitRIP.SphereContact T S := by
  dsimp [ExplicitRIP.SphereContact] at h ⊢
  linear_combination h

/-- Contact in the literal Heisenberg line parameters. -/
theorem sphereContact_iff_parameters (S T : Sphere F) :
    ExplicitRIP.SphereContact S T ↔
      ((sphereParameters S).c - (sphereParameters T).c) ^ 2 +
        ((sphereParameters S).d - (sphereParameters T).d) ^ 2 =
      ((sphereParameters S).a - (sphereParameters T).a) *
        ((sphereParameters S).b - (sphereParameters T).b) := by
  dsimp [ExplicitRIP.SphereContact, sphereParameters]
  constructor <;> intro h <;> linear_combination h

/-- The parameter change respects affine combinations. -/
theorem sphereParameters_affine (S T : Sphere F) (t : F) :
    sphereParameters (S + t • (T - S)) =
      ⟨(sphereParameters S).a + t * ((sphereParameters T).a - (sphereParameters S).a),
       (sphereParameters S).b + t * ((sphereParameters T).b - (sphereParameters S).b),
       (sphereParameters S).c + t * ((sphereParameters T).c - (sphereParameters S).c),
       (sphereParameters S).d + t * ((sphereParameters T).d - (sphereParameters S).d)⟩ := by
  apply HLine.ext <;> dsimp [sphereParameters] <;> ring

theorem sphereContact_affine {S T : Sphere F} (hc : ExplicitRIP.SphereContact S T)
    (s t : F) :
    ExplicitRIP.SphereContact (S + s • (T - S)) (S + t • (T - S)) := by
  dsimp [ExplicitRIP.SphereContact] at hc ⊢
  linear_combination (s - t) ^ 2 * hc

theorem left_mem_affinePencil (S T : Sphere F) : S ∈ affinePencil S T := by
  exact ⟨0, by simp only [zero_smul, add_zero]⟩

theorem right_mem_affinePencil (S T : Sphere F) : T ∈ affinePencil S T := by
  exact ⟨1, by simp only [one_smul, add_sub_cancel]⟩

/-- The common contacts are precisely the affine null line. -/
theorem common_contacts_eq_affinePencil (hn : ¬ IsSquare (-1 : F))
    (S T : Sphere F) (hne : S ≠ T) (hc : ExplicitRIP.SphereContact S T) :
    {U | ExplicitRIP.SphereContact U S ∧ ExplicitRIP.SphereContact U T} =
      affinePencil S T := by
  have h2 := two_ne_zero_of_neg_one_not_isSquare hn
  ext U
  constructor
  · rintro ⟨hUS, hUT⟩
    have hv : (sphereParameters T).a - (sphereParameters S).a ≠ 0 ∨
        (sphereParameters T).b - (sphereParameters S).b ≠ 0 ∨
        (sphereParameters T).c - (sphereParameters S).c ≠ 0 ∨
        (sphereParameters T).d - (sphereParameters S).d ≠ 0 := by
      by_contra! hz
      apply hne
      apply parameters_injective h2
      exact HLine.ext (sub_eq_zero.mp hz.1).symm
        (sub_eq_zero.mp hz.2.1).symm (sub_eq_zero.mp hz.2.2.1).symm
        (sub_eq_zero.mp hz.2.2.2).symm
    have hqv := (sphereContact_iff_parameters T S).mp (sphereContact_symm hc)
    have hqu := (sphereContact_iff_parameters U S).mp hUS
    have hqdiff := (sphereContact_iff_parameters U T).mp hUT
    obtain ⟨t, ha, hb, hc', hd⟩ := null_orthogonal_dependent hn
      ((sphereParameters T).a - (sphereParameters S).a)
      ((sphereParameters T).b - (sphereParameters S).b)
      ((sphereParameters T).c - (sphereParameters S).c)
      ((sphereParameters T).d - (sphereParameters S).d)
      ((sphereParameters U).a - (sphereParameters S).a)
      ((sphereParameters U).b - (sphereParameters S).b)
      ((sphereParameters U).c - (sphereParameters S).c)
      ((sphereParameters U).d - (sphereParameters S).d) hv hqv hqu
      (by linear_combination hqv + hqu - hqdiff)
    refine ⟨t, parameters_injective h2 ?_⟩
    rw [sphereParameters_affine]
    apply HLine.ext
    · dsimp; linear_combination -ha
    · dsimp; linear_combination -hb
    · dsimp; linear_combination -hc'
    · dsimp; linear_combination -hd
  · rintro ⟨t, rfl⟩
    constructor
    · simpa only [zero_smul, add_zero] using sphereContact_affine hc t 0
    · simpa only [one_smul, add_sub_cancel] using sphereContact_affine hc t 1

/-- The affine null line satisfies the maximality condition. -/
theorem affinePencil_isContactPencil (hn : ¬ IsSquare (-1 : F))
    (S T : Sphere F) (hne : S ≠ T) (hc : ExplicitRIP.SphereContact S T) :
    ExplicitRIP.IsContactPencil (affinePencil S T) := by
  constructor
  · rintro U ⟨s, rfl⟩ V ⟨t, rfl⟩
    exact sphereContact_affine hc s t
  · intro U hU hcontact
    apply hU
    rw [← common_contacts_eq_affinePencil hn S T hne hc]
    exact ⟨hcontact U (Set.mem_insert U _) S
        (Set.mem_insert_of_mem U (left_mem_affinePencil S T)),
      hcontact U (Set.mem_insert U _) T
        (Set.mem_insert_of_mem U (right_mem_affinePencil S T))⟩

/-- Maximality adds any sphere contacting every member. -/
theorem mem_of_isContactPencil_of_contact {P : Set (Sphere F)}
    (hP : ExplicitRIP.IsContactPencil P) (S : Sphere F)
    (hS : ∀ T ∈ P, ExplicitRIP.SphereContact S T) : S ∈ P := by
  by_contra hnS
  apply hP.2 S hnS
  intro T hT U hU
  rcases Set.mem_insert_iff.mp hT with hTS | hT
  · subst T
    rcases Set.mem_insert_iff.mp hU with hUS | hU
    · subst U
      exact sphereContact_refl S
    · exact hS U hU
  · rcases Set.mem_insert_iff.mp hU with hUS | hU
    · subst U
      exact sphereContact_symm (hS T hT)
    · exact hP.1 T hT U hU

/-- A maximal contact pencil cannot be properly contained in another one. -/
theorem eq_of_isContactPencil_of_subset {P Q : Set (Sphere F)}
    (hP : ExplicitRIP.IsContactPencil P) (hQ : ExplicitRIP.IsContactPencil Q)
    (hPQ : P ⊆ Q) : P = Q := by
  apply Set.Subset.antisymm hPQ
  intro S hS
  exact mem_of_isContactPencil_of_contact hP S (fun T hT => hQ.1 S hS T (hPQ hT))

/-- Two distinct members determine the whole maximal pencil. -/
theorem eq_affinePencil_of_two_mem (hn : ¬ IsSquare (-1 : F))
    {P : Set (Sphere F)} (hP : ExplicitRIP.IsContactPencil P)
    {S T : Sphere F} (hne : S ≠ T) (hS : S ∈ P) (hT : T ∈ P) :
    P = affinePencil S T := by
  have hc := hP.1 S hS T hT
  apply eq_of_isContactPencil_of_subset hP (affinePencil_isContactPencil hn S T hne hc)
  intro U hU
  rw [← common_contacts_eq_affinePencil hn S T hne hc]
  exact ⟨hP.1 U hU S hS, hP.1 U hU T hT⟩

/-- Every maximal contact pencil is an affine null line. -/
theorem isContactPencil_iff_affinePencil (hn : ¬ IsSquare (-1 : F))
    (P : Set (Sphere F)) :
    ExplicitRIP.IsContactPencil P ↔
      ∃ S T : Sphere F, S ≠ T ∧ ExplicitRIP.SphereContact S T ∧
        P = affinePencil S T := by
  constructor
  · intro hP
    have hnonempty : P.Nonempty := by
      by_contra hempty
      have hzero : (0 : Sphere F) ∈ P :=
        mem_of_isContactPencil_of_contact hP 0 (by
          intro T hT
          exact False.elim (hempty ⟨T, hT⟩))
      exact hempty ⟨0, hzero⟩
    obtain ⟨S, hS⟩ := hnonempty
    have htwo : ∃ T ∈ P, S ≠ T := by
      by_contra! hsingle
      let T : Sphere F := S + (0, 0, 1, 1)
      have hne : S ≠ T := by
        intro heq
        have hz := congrArg (fun U : Sphere F => U.2.2.1) heq
        have h01 : (0 : F) = 1 := by
          dsimp [T] at hz
          linear_combination hz
        exact zero_ne_one h01
      have hc : ExplicitRIP.SphereContact S T := by
        dsimp [ExplicitRIP.SphereContact, T]
        ring
      have hT : T ∈ P := mem_of_isContactPencil_of_contact hP T (by
        intro U hU
        rw [← hsingle U hU]
        exact sphereContact_symm hc)
      exact hne (hsingle T hT)
    obtain ⟨T, hT, hne⟩ := htwo
    exact ⟨S, T, hne, hP.1 S hS T hT, eq_affinePencil_of_two_mem hn hP hne hS hT⟩
  · rintro ⟨S, T, hne, hc, rfl⟩
    exact affinePencil_isContactPencil hn S T hne hc

/-- Pencils sharing two distinct spheres agree. -/
theorem pencil_unique_of_two_mem (hn : ¬ IsSquare (-1 : F))
    {P Q : Set (Sphere F)}
    (hP : ExplicitRIP.IsContactPencil P) (hQ : ExplicitRIP.IsContactPencil Q)
    {S T : Sphere F} (hne : S ≠ T) (hSP : S ∈ P) (hTP : T ∈ P)
    (hSQ : S ∈ Q) (hTQ : T ∈ Q) : P = Q :=
  (eq_affinePencil_of_two_mem hn hP hne hSP hTP).trans
    (eq_affinePencil_of_two_mem hn hQ hne hSQ hTQ).symm

end ExplicitRIP.Zahl
