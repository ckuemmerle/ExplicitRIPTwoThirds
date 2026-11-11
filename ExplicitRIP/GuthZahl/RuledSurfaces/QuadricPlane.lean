/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.PlaneLines
public import ExplicitRIP.GuthZahl.RuledSurfaces.Transversals
public import ExplicitRIP.GuthZahl.RuledSurfaces.GenericLine
public import ExplicitRIP.GuthZahl.RuledSurfaces.LineChart

/-!
# Plane sections of irreducible quadrics

Three distinct contained lines in one plane would force infinitely many other
contained lines in that plane: almost every line joining a suitable point of
the first line to a point of the second has three distinct zeros. This
contradicts finite common-line intersection with the plane equation.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

/-- An irreducible quadric cannot contain three distinct lines in one affine plane. -/
theorem not_three_lines_in_plane {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (P : AffineSubspace K (Point K))
    (hP : Module.finrank K P.direction = 2) (A B C : Line K)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (hAP : A.1 ≤ P) (hBP : B.1 ≤ P) (hCP : C.1 ≤ P) : False := by
  classical
  have hxinf := (infinite_points_line A).sdiff
    ((line_inter_subsingleton _ _ hAB).finite.union (line_inter_subsingleton _ _ hAC).finite)
  obtain ⟨x, hxA, hxavoid⟩ := hxinf.nonempty
  have hxB : x ∉ B.1 := fun h => hxavoid (Or.inl ⟨hxA, h⟩)
  have hxC : x ∉ C.1 := fun h => hxavoid (Or.inr ⟨hxA, h⟩)
  let Z : Set (Point K) := {z | z ∈ B.1 ∧ z ∉ C.1}
  have hZ : Z.Infinite := by
    apply ((infinite_points_line B).sdiff (line_inter_subsingleton _ _ hBC).finite).mono
    rintro z ⟨hzB, hnot⟩
    exact ⟨hzB, fun hzC => hnot ⟨hzB, hzC⟩⟩
  have : Infinite Z := Set.infinite_coe_iff.mpr hZ
  have hv0 (z : Z) : z.1 - x ≠ (0 : Point K) :=
    sub_ne_zero.mpr (fun h => hxB (h ▸ z.2.1))
  let F : Z → Line K := fun z => lineThrough x (z.1 - x) (hv0 z)
  have hxF (z : Z) : x ∈ (F z).1 := (mem_lineThrough _ _ _ (hv0 z)).mpr ⟨0, by simp⟩
  have hzF (z : Z) : z.1 ∈ (F z).1 :=
    (mem_lineThrough _ _ _ (hv0 z)).mpr ⟨1, by simp only [one_smul]; abel⟩
  have hFP (z : Z) : (F z).1 ≤ P :=
    line_le_of_two_points (x := x) (y := z.1) (fun h => hxB (h.symm ▸ z.2.1)) (hxF z) (hzF z)
      (hAP hxA) (hBP z.2.1)
  have hFinj : Function.Injective F := by
    intro z z' heq
    by_contra hzz'
    have hne : z.1 ≠ z'.1 := fun h => hzz' (Subtype.ext h)
    have hz' : z'.1 ∈ (F z).1 := heq.symm ▸ hzF z'
    have hFB : F z = B := line_eq_of_le
      (line_le_of_two_points hne (hzF z) hz' z.2.1 z'.2.1)
    exact hxB (hFB ▸ hxF z)
  obtain ⟨c, v, hc, hv, hvne, hparam⟩ := exists_line_parametrization C
  let D : Line K := lineThrough x v hvne
  have hxD : x ∈ D.1 := (mem_lineThrough _ _ _ hvne).mpr ⟨0, by simp⟩
  have hDdir : D.1.direction = C.1.direction := by
    change (AffineSubspace.mk' x (Submodule.span K {v})).direction = C.1.direction
    rw [AffineSubspace.direction_mk']
    exact (eq_span_singleton_of_mem_of_finrank_eq_one C.2 hv hvne).symm
  have hlines := (Set.infinite_range_of_injective hFinj).sdiff (Set.finite_singleton D)
  have hfinite := finite_lines_in_plane hq (by omega) P hP
  apply hlines
  apply hfinite.subset
  rintro L ⟨⟨z, rfl⟩, hnotD⟩
  have hdir : (F z).1.direction ≠ C.1.direction := by
    intro heq
    apply hnotD
    apply Set.mem_singleton_iff.mpr
    exact Subtype.ext (AffineSubspace.ext_of_direction_eq (heq.trans hDdir.symm)
      ⟨x, hxF z, hxD⟩)
  have hcop : Coplanar (F z) C := ⟨P, hP, hFP z, hCP⟩
  obtain ⟨y, hyF, hyC⟩ :=
    (inter_nonempty_or_direction_eq_of_coplanar hcop).resolve_right hdir
  have hxy : x ≠ y := fun h => hxC (h.symm ▸ hyC)
  have hzy : z.1 ≠ y := fun h => z.2.2 (h.symm ▸ hyC)
  have hxz : x ≠ z.1 := fun h => hxB (h.symm ▸ z.2.1)
  refine ⟨?_, hFP z⟩
  apply lineOn_of_totalDegree_lt_card ![x, z.1, y]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact hxF z
    · exact hzF z
    · exact hyF
  · intro i
    fin_cases i
    · exact eval_eq_zero_of_lineOn hA hxA
    · exact eval_eq_zero_of_lineOn hB z.2.1
    · exact eval_eq_zero_of_lineOn hC hyC
  · simp only [hdegree, Fintype.card_fin]
    omega

/-- A finite family of lines in a plane section of an irreducible quadric has at most two
members. -/
theorem card_lines_in_plane_le_two {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (P : AffineSubspace K (Point K))
    (hP : Module.finrank K P.direction = 2) (Ls : Finset (Line K))
    (hLs : ∀ L ∈ Ls, LineOn q L ∧ L.1 ≤ P) : Ls.card ≤ 2 := by
  classical
  by_contra hcard
  have hthree : 2 < Ls.card := Nat.lt_of_not_ge hcard
  obtain ⟨A, hA, B, hB, C, hC, hAB, hAC, hBC⟩ := Finset.two_lt_card.mp hthree
  exact not_three_lines_in_plane hq hdegree P hP A B C hAB hAC hBC
    (hLs A hA).1 (hLs B hB).1 (hLs C hC).1 (hLs A hA).2 (hLs B hB).2 (hLs C hC).2

end ExplicitRIP.GuthZahl.RuledSurfaces
end
