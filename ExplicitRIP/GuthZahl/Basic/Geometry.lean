/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Elementary incidence geometry of affine lines

Distinct one-dimensional affine subspaces have at most one common point. Consequently a
finite line family has only finitely many points incident to at least two members.
-/

public section

namespace ExplicitRIP.GuthZahl

variable {K : Type*} [Field K]

theorem line_inter_subsingleton {K : Type*} [Field K] (L M : Line K) (hLM : L ≠ M) :
    ((L.1 : Set (Point K)) ∩ M.1).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hv : y -ᵥ x ≠ (0 : Point K) := vsub_ne_zero.mpr (Ne.symm hxy)
  have hL := eq_span_singleton_of_mem_of_finrank_eq_one L.2
    (AffineSubspace.vsub_mem_direction hy.1 hx.1) hv
  have hM := eq_span_singleton_of_mem_of_finrank_eq_one M.2
    (AffineSubspace.vsub_mem_direction hy.2 hx.2) hv
  exact hLM (Subtype.ext (AffineSubspace.ext_of_direction_eq
    (hL.trans hM.symm) ⟨x, hx⟩))

theorem richPoints_finite {K : Type*} [Field K] (Ls : Finset (Line K))
    (r : ℕ) (hr : 2 ≤ r) : (richPoints Ls r).Finite := by
  classical
  have hfin : (⋃ LM ∈ Ls.offDiag,
      ((LM.1.1 : Set (Point K)) ∩ LM.2.1)).Finite :=
    Ls.offDiag.finite_toSet.biUnion fun LM hLM =>
      (line_inter_subsingleton LM.1 LM.2 (Finset.mem_offDiag.mp hLM).2.2).finite
  apply hfin.subset
  intro x hx
  obtain ⟨L, hL, M, hM, hLM⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) (hr.trans hx))
  obtain ⟨hLs, hxL⟩ := Finset.mem_filter.mp hL
  obtain ⟨hMs, hxM⟩ := Finset.mem_filter.mp hM
  exact Set.mem_iUnion.mpr ⟨(L, M), Set.mem_iUnion.mpr
    ⟨Finset.mem_offDiag.mpr ⟨hLs, hMs, hLM⟩, hxL, hxM⟩⟩

/-- Every line in the fixed carrier is nonempty. -/
theorem line_nonempty (L : Line K) : (L.1 : Set (Point K)).Nonempty := by
  apply (AffineSubspace.nonempty_iff_ne_bot _).2
  intro h
  have hd := L.2
  rw [h, AffineSubspace.direction_bot, finrank_bot] at hd
  exact Nat.zero_ne_one hd

/-- An inclusion of two lines is an equality. -/
theorem line_eq_of_le {L M : Line K} (h : L.1 ≤ M.1) : L = M := by
  apply Subtype.ext
  apply AffineSubspace.ext_of_direction_eq
  · exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h)
      (L.2.trans M.2.symm)
  · obtain ⟨x, hx⟩ := line_nonempty L
    exact ⟨x, hx, h hx⟩

/-- A nonzero direction vector parametrizes the whole line from any of its points. -/
theorem mem_line_iff_exists_smul {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0) (x : Point K) :
    x ∈ L.1 ↔ ∃ t : K, a + t • v = x := by
  constructor
  · intro hx
    have hsub : x - a ∈ L.1.direction := AffineSubspace.vsub_mem_direction hx ha
    rw [eq_span_singleton_of_mem_of_finrank_eq_one L.2 hv hv0] at hsub
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hsub
    exact ⟨t, by rw [ht]; abel⟩
  · rintro ⟨t, rfl⟩
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (L.1.direction.smul_mem t hv) ha

/-- Every line has a base point and a nonzero direction. -/
theorem exists_line_parametrization (L : Line K) :
    ∃ a v : Point K, a ∈ L.1 ∧ v ∈ L.1.direction ∧ v ≠ 0 ∧
      ∀ x : Point K, x ∈ L.1 ↔ ∃ t : K, a + t • v = x := by
  obtain ⟨a, ha⟩ := line_nonempty L
  obtain ⟨v, hv, hv0⟩ := L.1.direction.ne_bot_iff.mp (by
    intro h
    have hd := L.2
    rw [h, finrank_bot] at hd
    exact Nat.zero_ne_one hd)
  exact ⟨a, v, ha, hv, hv0, mem_line_iff_exists_smul ha hv hv0⟩

end ExplicitRIP.GuthZahl

end
