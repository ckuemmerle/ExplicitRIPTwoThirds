/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.PlaneLines
public import ExplicitRIP.GuthZahl.RuledSurfaces.LineChart
public import ExplicitRIP.GuthZahl.RuledSurfaces.GenericLine

/-!
# Lines joining an external point to a line

A point and a line lie in a plane. If the point is outside the line, joining it
to the infinitely many points of that line gives infinitely many distinct lines.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A point and an affine line are contained in a plane. -/
theorem exists_plane_containing_point_line (x : Point K) (A : Line K) :
    ∃ P : AffineSubspace K (Point K), Module.finrank K P.direction = 2 ∧ x ∈ P ∧ A.1 ≤ P := by
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization A
  let D := lineThrough x v hv0
  have hxD : x ∈ D.1 := (mem_lineThrough _ _ _ hv0).mpr ⟨0, by simp⟩
  have hdir : A.1.direction = D.1.direction := by
    change A.1.direction = (AffineSubspace.mk' x (Submodule.span K {v})).direction
    rw [AffineSubspace.direction_mk']
    exact eq_span_singleton_of_mem_of_finrank_eq_one A.2 hv hv0
  obtain ⟨P, hP, hAP, hDP⟩ := coplanar_of_direction_eq hdir
  exact ⟨P, hP, hDP hxD, hAP⟩

/-- Infinitely many lines join an external point to a given line. -/
theorem infinite_lines_joining_point_line [Infinite K] (x : Point K) (A : Line K)
    (hxA : x ∉ A.1) :
    {L : Line K | x ∈ L.1 ∧ ∃ y ∈ A.1, y ∈ L.1}.Infinite := by
  classical
  have : Infinite (A.1 : Set (Point K)) := Set.infinite_coe_iff.mpr (infinite_points_line A)
  have hv0 (z : (A.1 : Set (Point K))) : z.1 - x ≠ (0 : Point K) :=
    sub_ne_zero.mpr (fun h => hxA (h ▸ z.2))
  let F : (A.1 : Set (Point K)) → Line K := fun z => lineThrough x (z.1 - x) (hv0 z)
  have hxF (z : (A.1 : Set (Point K))) : x ∈ (F z).1 :=
    (mem_lineThrough _ _ _ (hv0 z)).mpr ⟨0, by simp⟩
  have hzF (z : (A.1 : Set (Point K))) : z.1 ∈ (F z).1 :=
    (mem_lineThrough _ _ _ (hv0 z)).mpr ⟨1, by simp only [one_smul]; abel⟩
  have hFinj : Function.Injective F := by
    intro z z' heq
    by_contra hzz'
    have hne : z.1 ≠ z'.1 := fun h => hzz' (Subtype.ext h)
    have hz' : z'.1 ∈ (F z).1 := heq.symm ▸ hzF z'
    have hFA : F z = A := line_eq_of_le
      (line_le_of_two_points hne (hzF z) hz' z.2 z'.2)
    exact hxA (hFA ▸ hxF z)
  apply (Set.infinite_range_of_injective hFinj).mono
  rintro L ⟨z, rfl⟩
  exact ⟨hxF z, z.1, z.2, hzF z⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
