/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Counting.Bichromatic

/-! # Deleting lines of small current degree -/

public section

namespace ExplicitRIP.Zahl.Incidence.Pruning

open Classical in
lemma exists_pruning {α β : Type*} [DecidableEq α] (L : Finset α) (P : Finset α → Set β)
    (inc : α → Set β) (hfinite : ∀ T ⊆ L, (P T).Finite)
    (hdelete : ∀ T ⊆ L, ∀ l ∈ T, P T ⊆ P (T.erase l) ∪ (P T ∩ inc l))
    (d : ℝ) :
    ∃ T ⊆ L, (P L).ncard - d * ((L.card : ℝ) - T.card) ≤ (P T).ncard ∧
      ∀ l ∈ T, d < ((P T ∩ inc l).ncard : ℝ) := by
  classical
  suffices h : ∀ S : Finset α, S ⊆ L →
      ∃ T ⊆ S, (P S).ncard - d * ((S.card : ℝ) - T.card) ≤ (P T).ncard ∧
        ∀ l ∈ T, d < ((P T ∩ inc l).ncard : ℝ) from h L Finset.Subset.rfl
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hSL
    by_cases hgood : ∀ l ∈ S, d < ((P S ∩ inc l).ncard : ℝ)
    · exact ⟨S, Finset.Subset.rfl, by simp, hgood⟩
    · push Not at hgood
      obtain ⟨l, hl, hdegree⟩ := hgood
      obtain ⟨T, hT, hbound, hgood⟩ := ih (S.erase l) (Finset.erase_ssubset hl)
        ((Finset.erase_subset l S).trans hSL)
      have hfin := hfinite S hSL
      have hfin' := hfinite (S.erase l) ((Finset.erase_subset l S).trans hSL)
      have hcard : (P S).ncard ≤ (P (S.erase l)).ncard + (P S ∩ inc l).ncard :=
        (Set.ncard_le_ncard (hdelete S hSL l hl)
          (hfin'.union (hfin.subset Set.inter_subset_left))).trans (Set.ncard_union_le _ _)
      have hcard' : ((P S).ncard : ℝ) ≤
          (P (S.erase l)).ncard + (P S ∩ inc l).ncard := by exact_mod_cast hcard
      have herase : ((S.erase l).card : ℝ) = (S.card : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem hl, Nat.cast_sub (Finset.one_le_card.mpr ⟨l, hl⟩)]
        norm_num
      rw [herase] at hbound
      exact ⟨T, hT.trans (Finset.erase_subset l S),
        by linarith only [hcard', hdegree, hbound], hgood⟩

open Classical in
lemma richPoints_delete_subset {K : Type*} [CommRing K]
    (T : Finset (ChartLine K)) (k : ℕ) (l : ChartLine K) :
    richPoints T k ⊆ richPoints (T.erase l) k ∪ (richPoints T k ∩ linePoints l) := by
  classical
  intro w hw
  by_cases hwl : w ∈ linePoints l
  · exact Or.inr ⟨hw, hwl⟩
  · apply Or.inl
    change k ≤ ((T.erase l).filter (fun a => w ∈ linePoints a)).card
    have heq : (T.erase l).filter (fun a => w ∈ linePoints a) =
        T.filter (fun a => w ∈ linePoints a) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · rintro ⟨ha, hwa⟩
        exact ⟨⟨fun h => hwl (h ▸ hwa), ha⟩, hwa⟩
    rwa [heq]

end ExplicitRIP.Zahl.Incidence.Pruning

namespace ExplicitRIP.Zahl

-- The statement includes the nonnegativity premise.
set_option linter.unusedVariables false in
open Classical in
theorem exists_rich_pruning {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (k : ℕ) (hk : 2 ≤ k)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ T : Finset (ChartLine K), T ⊆ L ∧
      (richCount L k : ℝ) - d * ((L.card : ℝ) - (T.card : ℝ)) ≤
        (richCount T k : ℝ) ∧
      ∀ l ∈ T, d < ((richPoints T k ∩ linePoints l).ncard : ℝ) := by
  exact Incidence.Pruning.exists_pruning L (fun T => richPoints T k) linePoints
    (fun T _ => richPoints_finite T k hk)
    (fun T _ l _ => Incidence.Pruning.richPoints_delete_subset T k l) d

-- The statement includes the nonnegativity premise.
set_option linter.unusedVariables false in
open Classical in
theorem exists_bichromatic_pruning {K : Type*} [Field K]
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (d : ℝ) (hd : 0 ≤ d) :
    ∃ R' B' : Finset (ChartLine K), R' ⊆ R ∧ B' ⊆ B ∧
      ((bichromaticPoints R B).ncard : ℝ) -
          d * (((R ∪ B).card : ℝ) - ((R' ∪ B').card : ℝ)) ≤
        ((bichromaticPoints R' B').ncard : ℝ) ∧
      ∀ l ∈ R' ∪ B',
        d < ((bichromaticPoints R' B' ∩ linePoints l).ncard : ℝ) := by
  classical
  let P := fun T => bichromaticPoints (T ∩ R) (T ∩ B)
  have hf (T : Finset (ChartLine K)) (_ : T ⊆ R ∪ B) : (P T).Finite :=
    (richPoints_finite (R ∪ B) 2 le_rfl).subset
      (bichromaticPoints_subset_richPoints_two
        (Finset.inter_subset_right.trans Finset.subset_union_left)
        (Finset.inter_subset_right.trans Finset.subset_union_right)
        (hRB.mono Finset.inter_subset_right Finset.inter_subset_right))
  have hdel (T : Finset (ChartLine K)) (_ : T ⊆ R ∪ B)
      (l : ChartLine K) (_ : l ∈ T) : P T ⊆ P (T.erase l) ∪ (P T ∩ linePoints l) := by
    intro w hw
    by_cases hwl : w ∈ linePoints l
    · exact Or.inr ⟨hw, hwl⟩
    · rcases hw with ⟨⟨r, hr, hwr⟩, b, hb, hwb⟩
      apply Or.inl
      exact ⟨⟨r, Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨fun h => hwl (h ▸ hwr), (Finset.mem_inter.mp hr).1⟩,
          (Finset.mem_inter.mp hr).2⟩, hwr⟩,
        b, Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨fun h => hwl (h ▸ hwb), (Finset.mem_inter.mp hb).1⟩,
          (Finset.mem_inter.mp hb).2⟩, hwb⟩
  obtain ⟨T, hT, hbound, hgood⟩ :=
    Incidence.Pruning.exists_pruning (R ∪ B) P linePoints hf hdel d
  have hsplit : T ∩ R ∪ T ∩ B = T := by
    ext l
    simp only [Finset.mem_union, Finset.mem_inter]
    exact ⟨fun h => h.elim And.left And.left, fun hl =>
      (Finset.mem_union.mp (hT hl)).elim (fun hr => Or.inl ⟨hl, hr⟩)
        (fun hb => Or.inr ⟨hl, hb⟩)⟩
  refine ⟨T ∩ R, T ∩ B, Finset.inter_subset_right, Finset.inter_subset_right, ?_, ?_⟩
  · simpa only [P, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, hsplit]
      using hbound
  · simpa only [hsplit, P] using hgood

end ExplicitRIP.Zahl
