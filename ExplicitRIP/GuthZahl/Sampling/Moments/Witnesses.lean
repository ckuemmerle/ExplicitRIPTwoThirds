/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Geometry

/-!
# Distinct witnesses for rich points on a line

A two-rich point has an incident line other than a designated original line.
The intersection uniqueness of distinct affine lines makes these witnesses
distinct when their points on the designated line are distinct.
-/

public section

namespace ExplicitRIP.GuthZahl
namespace Sampling

open Classical in
theorem exists_other_line_of_mem_richPoints {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) (hL : L ∈ Ls) (x : Point K)
    (hx : x ∈ richPoints Ls 2) (hxL : x ∈ L.1) :
    ∃ M ∈ Ls, M ≠ L ∧ x ∈ M.1 := by
  have hLfilter : L ∈ Ls.filter (fun M => x ∈ M.1) :=
    Finset.mem_filter.mpr ⟨hL, hxL⟩
  have hpos : 0 < ((Ls.filter (fun M => x ∈ M.1)).erase L).card := by
    rw [Finset.card_erase_of_mem hLfilter]
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hx)
  obtain ⟨M, hM⟩ := Finset.card_pos.mp hpos
  obtain ⟨hML, hM⟩ := Finset.mem_erase.mp hM
  obtain ⟨hMs, hxM⟩ := Finset.mem_filter.mp hM
  exact ⟨M, hMs, hML, hxM⟩

open Classical in
/-- Distinct points on L have distinct witness lines. -/
theorem _root_.ExplicitRIP.GuthZahl.rich_point_witnesses {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) (hL : L ∈ Ls) (m : ℕ)
    (hm : m ≤ (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard) :
    ∃ x : Fin m → Point K, ∃ W : Fin m → Line K,
      Function.Injective x ∧ Function.Injective W ∧
        ∀ i, W i ∈ Ls ∧ W i ≠ L ∧ x i ∈ L.1 ∧ x i ∈ (W i).1 := by
  have hfinite : (richPoints Ls 2 ∩ (L.1 : Set (Point K))).Finite :=
    (richPoints_finite Ls 2 le_rfl).subset Set.inter_subset_left
  have hencard : (m : ℕ∞) ≤
      (richPoints Ls 2 ∩ (L.1 : Set (Point K))).encard := by
    rw [← hfinite.cast_ncard_eq]
    exact_mod_cast hm
  obtain ⟨x, hx, hinj⟩ := (Set.le_encard_iff_exists_fin_injective _ m).mp hencard
  choose W hWs hWL hxW using
    (fun i => exists_other_line_of_mem_richPoints Ls L hL (x i) (hx i).1 (hx i).2)
  refine ⟨x, W, hinj, ?_, fun i => ⟨hWs i, hWL i, (hx i).2, hxW i⟩⟩
  intro i j hij
  apply hinj
  exact line_inter_subsingleton L (W i) (hWL i).symm
    ⟨(hx i).2, hxW i⟩ ⟨(hx j).2, hij.symm ▸ hxW j⟩

open Classical in
theorem _root_.ExplicitRIP.GuthZahl.rich_points_on_line_le {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) (hL : L ∈ Ls) :
    (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard ≤ Ls.card - 1 := by
  obtain ⟨x, W, _, hW, hmem⟩ := rich_point_witnesses Ls L hL
    (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard le_rfl
  let f : Fin (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard → Ls.erase L :=
    fun i => ⟨W i, Finset.mem_erase.mpr ⟨(hmem i).2.1, (hmem i).1⟩⟩
  have hf : Function.Injective f := fun _ _ h => hW (congrArg Subtype.val h)
  simpa only [Fintype.card_fin, Fintype.card_coe, Finset.card_erase_of_mem hL] using
    Fintype.card_le_of_injective f hf

end Sampling
end ExplicitRIP.GuthZahl

end
