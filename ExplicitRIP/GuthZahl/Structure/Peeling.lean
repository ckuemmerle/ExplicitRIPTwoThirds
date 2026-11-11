/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs
import ExplicitRIP.GuthZahl.Basic
import ExplicitRIP.GuthZahl.Sampling.Moments

/-!
# Deleting lines with few remaining rich points

Deleting one line loses only rich points on that line. Induction therefore
either bounds the original count or leaves a nonempty popular subfamily.
-/

public section

namespace ExplicitRIP.GuthZahl.Structure

open Classical in
theorem richPoints_erase_subset {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) :
    richPoints Ls 2 ⊆ richPoints (Ls.erase L) 2 ∪
      (richPoints Ls 2 ∩ (L.1 : Set (Point K))) := by
  intro x hx
  by_cases hxL : x ∈ L.1
  · exact Or.inr ⟨hx, hxL⟩
  · apply Or.inl
    have heq : (Ls.erase L).filter (fun M => x ∈ M.1) =
        Ls.filter (fun M => x ∈ M.1) := by
      ext M
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · rintro ⟨hM, hxM⟩
        exact ⟨⟨fun h => hxL (h ▸ hxM), hM⟩, hxM⟩
    change 2 ≤ ((Ls.erase L).filter (fun M => x ∈ M.1)).card
    rwa [heq]

open Classical in
theorem richPoints_ncard_le_erase_add {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) :
    (richPoints Ls 2).ncard ≤ (richPoints (Ls.erase L) 2).ncard +
      (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard := by
  have hfinite : (richPoints (Ls.erase L) 2 ∪
      (richPoints Ls 2 ∩ (L.1 : Set (Point K)))).Finite :=
    (richPoints_finite (Ls.erase L) 2 le_rfl).union
    ((richPoints_finite Ls 2 le_rfl).subset Set.inter_subset_left)
  exact (Set.ncard_le_ncard (richPoints_erase_subset Ls L) hfinite).trans
    (Set.ncard_union_le _ _)

theorem count_or_popular_subset {K : Type*} [Field K]
    (Ls : Finset (Line K)) (B : ℝ) :
    ((richPoints Ls 2).ncard : ℝ) ≤ B * Ls.card ∨
      ∃ Rs : Finset (Line K), Rs ⊆ Ls ∧ Rs.Nonempty ∧
        ∀ L ∈ Rs, B ≤ ((richPoints Rs 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) := by
  classical
  induction Ls using Finset.strongInductionOn with
  | _ Ls ih =>
    by_cases hne : Ls.Nonempty
    · by_cases hpop : ∀ L ∈ Ls,
          B ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)
      · exact Or.inr ⟨Ls, Finset.Subset.rfl, hne, hpop⟩
      · push Not at hpop
        obtain ⟨L, hL, hsmall⟩ := hpop
        rcases ih (Ls.erase L) (Finset.erase_ssubset hL) with hbound | ⟨Rs, hRs, hn, hp⟩
        · apply Or.inl
          have hloss : ((richPoints Ls 2).ncard : ℝ) ≤
              (richPoints (Ls.erase L) 2).ncard +
                (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard := by
            exact_mod_cast richPoints_ncard_le_erase_add Ls L
          have hcard : ((Ls.erase L).card : ℝ) + 1 = Ls.card := by
            exact_mod_cast Finset.card_erase_add_one hL
          nlinarith only [hloss, hsmall, hbound, hcard]
        · exact Or.inr ⟨Rs, hRs.trans (Finset.erase_subset L Ls), hn, hp⟩
    · have hempty : Ls = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst Ls
      left
      simp only [richPoints, Finset.filter_empty, Finset.card_empty,
        Nat.reduceLeDiff, Set.ofPred_false, Set.ncard_empty, Nat.cast_zero, mul_zero, le_refl]

theorem richPoints_ncard_le_card_sq {K : Type*} [Field K] (Ls : Finset (Line K)) :
    ((richPoints Ls 2).ncard : ℝ) ≤ (Ls.card : ℝ) ^ 2 := by
  rcases count_or_popular_subset Ls (Ls.card : ℝ) with hbound | ⟨Rs, hRs, hne, hpop⟩
  · simpa only [pow_two] using hbound
  · obtain ⟨L, hL⟩ := hne
    have hless : (richPoints Rs 2 ∩ (L.1 : Set (Point K))).ncard < Ls.card :=
      (rich_points_on_line_le Rs L hL).trans_lt
        ((Nat.sub_lt (Finset.card_pos.mpr ⟨L, hL⟩) Nat.zero_lt_one).trans_le
          (Finset.card_le_card hRs))
    have hlessR : ((richPoints Rs 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) < Ls.card := by
      exact_mod_cast hless
    exact False.elim ((not_le_of_gt hlessR) (hpop L hL))

end ExplicitRIP.GuthZahl.Structure

end
