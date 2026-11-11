/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Pencils.Families
public import ExplicitRIP.Zahl.Geometry.Lines

/-!
# Classification of maximal contact pencils

Coplanarity of two sphere lines distinguishes a finite intersection point from
a common direction. Two distinct spheres determine the full contact pencil.
-/

public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

namespace Lie.Classification

/-- Parallel sphere lines have the same three direction parameters. -/
theorem parallel_sphereLine_iff_parameters (S T : Sphere F) :
    Parallel (sphereLine S) (sphereLine T) ↔
      (sphereParameters S).b = (sphereParameters T).b ∧
      (sphereParameters S).c = (sphereParameters T).c ∧
      (sphereParameters S).d = (sphereParameters T).d := by
  constructor
  · rintro ⟨hu, hv⟩
    have hb := congrArg QuadraticAlgebra.re hu
    have hc := congrArg QuadraticAlgebra.re hv
    have hd := congrArg QuadraticAlgebra.im hv
    change (sphereParameters S).b = (sphereParameters T).b at hb
    change (sphereParameters S).c = (sphereParameters T).c at hc
    change -(sphereParameters S).d = -(sphereParameters T).d at hd
    exact ⟨hb, hc, neg_injective hd⟩
  · rintro ⟨hb, hc, hd⟩
    exact ⟨congrArg (algebraMap F (QuadraticExtension F)) hb,
      QuadraticAlgebra.ext hc (congrArg Neg.neg hd)⟩

/-- Any two members of a direction pencil have parallel sphere lines. -/
theorem parallel_of_mem_directionPencil {v : F × F × F} {S T : Sphere F}
    (hS : S ∈ directionPencil v) (hT : T ∈ directionPencil v) :
    Parallel (sphereLine S) (sphereLine T) := by
  exact (parallel_sphereLine_iff_parameters S T).mpr
    ⟨hS.1.trans hT.1.symm, hS.2.1.trans hT.2.1.symm, hS.2.2.trans hT.2.2.symm⟩

end Lie.Classification

/-- Every maximal pencil comes from a point or a direction. -/
theorem isContactPencil_iff_point_or_direction (hn : ¬ IsSquare (-1 : F))
    (P : Set (Sphere F)) :
    ExplicitRIP.IsContactPencil P ↔
      (∃ w ∈ heisenberg, P = pointPencil w) ∨
      ∃ v : F × F × F, P = directionPencil v := by
  let : Fact (¬ IsSquare (-1 : F)) := ⟨hn⟩
  constructor
  · intro hP
    obtain ⟨S, T, hne, hc, heq⟩ := (isContactPencil_iff_affinePencil hn P).mp hP
    have hS : S ∈ P := heq.symm ▸ left_mem_affinePencil S T
    have hT : T ∈ P := heq.symm ▸ right_mem_affinePencil S T
    have hcop := (sphereContact_iff_coplanar S T).mp hc
    rcases (coplanar_iff_intersects_or_parallel _ _).mp hcop with ⟨w, hwS, hwT⟩ | hp
    · have hw : w ∈ heisenberg := (sphereParameters S).linePoints_subset_heisenberg hwS
      exact Or.inl ⟨w, hw, pencil_unique_of_two_mem hn hP
        (pointPencil_isContactPencil hn w hw) hne hS hT hwS hwT⟩
    · obtain ⟨hb, hc, hd⟩ := (Lie.Classification.parallel_sphereLine_iff_parameters S T).mp hp
      let v : F × F × F :=
        ((sphereParameters S).b, (sphereParameters S).c, (sphereParameters S).d)
      exact Or.inr ⟨v, pencil_unique_of_two_mem hn hP
        (directionPencil_isContactPencil hn v) hne hS hT
        ⟨rfl, rfl, rfl⟩ ⟨hb.symm, hc.symm, hd.symm⟩⟩
  · rintro (⟨w, hw, rfl⟩ | ⟨v, rfl⟩)
    · exact pointPencil_isContactPencil hn w hw
    · exact directionPencil_isContactPencil hn v

end ExplicitRIP.Zahl
