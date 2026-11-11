/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Components.Defs

/-!
# Counting lines by their containing factors

A covered line either lies in multiple factors or belongs to a unique-factor family.
-/

public section

namespace ExplicitRIP.GuthZahl.Components.Selection

open Classical in
/-- The multiple-factor family and the unique-factor families cover all original lines. -/
theorem card_le_multiple_add_sum_unique {K : Type*} [Field K] {m : ℕ}
    (Ls : Finset (Line K)) (F : Fin m → Poly K)
    (hcover : ∀ L ∈ Ls, ∃ i, LineOn (F i) L) :
    Ls.card ≤ (multipleFactorLines Ls F).card +
      ∑ i, (uniqueFactorLines Ls F i).card := by
  have hsub : Ls ⊆ multipleFactorLines Ls F ∪
      Finset.univ.biUnion (uniqueFactorLines Ls F) := by
    intro L hL
    by_cases hmultiple : L ∈ multipleFactorLines Ls F
    · exact Finset.mem_union_left _ hmultiple
    · obtain ⟨i, hi⟩ := hcover L hL
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hL, hi, ?_⟩⟩
      intro j hji hj
      exact hmultiple (Finset.mem_filter.mpr ⟨hL, i, j, hji.symm, hi, hj⟩)
  calc
    Ls.card ≤ (multipleFactorLines Ls F ∪
        Finset.univ.biUnion (uniqueFactorLines Ls F)).card := Finset.card_le_card hsub
    _ ≤ (multipleFactorLines Ls F).card +
        (Finset.univ.biUnion (uniqueFactorLines Ls F)).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

end ExplicitRIP.GuthZahl.Components.Selection

end
