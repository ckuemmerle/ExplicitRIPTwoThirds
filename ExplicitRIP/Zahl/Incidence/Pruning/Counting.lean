/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Counting.Finite
public import ExplicitRIP.Zahl.Incidence.Sampling.FixedSize
public import ExplicitRIP.Zahl.Incidence.Sampling.SetCounts

/-! # Pair counting and fixed-size rich-point sampling -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
theorem richCount_pair_bound {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (k : ℕ) (hk : 2 ≤ k) :
    (richCount L k : ℝ) * (k : ℝ) * ((k : ℝ) - 1) ≤
      (L.card : ℝ) * ((L.card : ℝ) - 1) := by
  classical
  let P := (richPoints_finite L k hk).toFinset
  let pairs := fun w : Point K => (L.filter (fun l => w ∈ linePoints l)).offDiag
  have hdisj : (P : Set (Point K)).PairwiseDisjoint pairs := by
    intro w _ z _ hwz
    apply Finset.disjoint_left.mpr
    intro lm hw hz
    obtain ⟨hl, hm, hne⟩ := Finset.mem_offDiag.mp hw
    obtain ⟨hl', hm', _⟩ := Finset.mem_offDiag.mp hz
    exact hwz (linePoints_inter_subsingleton hne
      ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hm).2⟩
      ⟨(Finset.mem_filter.mp hl').2, (Finset.mem_filter.mp hm').2⟩)
  have hsub : P.biUnion pairs ⊆ L.offDiag := by
    intro lm h
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hl, hm, hne⟩ := Finset.mem_offDiag.mp hw
    exact Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp hl).1, (Finset.mem_filter.mp hm).1, hne⟩
  have hcard : (∑ w ∈ P, (pairs w).card) ≤ L.offDiag.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  have hreal : (∑ w ∈ P, ((pairs w).card : ℝ)) ≤ (L.offDiag.card : ℝ) := by
    exact_mod_cast hcard
  have hPcard : P.card = richCount L k :=
    (Set.ncard_eq_toFinset_card _ (richPoints_finite L k hk)).symm
  calc
    _ = ∑ _w ∈ P, (k : ℝ) * ((k : ℝ) - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, hPcard, mul_assoc]
    _ ≤ ∑ w ∈ P, ((pairs w).card : ℝ) := by
      apply Finset.sum_le_sum
      intro w hw
      have hwk : k ≤ (L.filter (fun l => w ∈ linePoints l)).card :=
        (Set.Finite.mem_toFinset (richPoints_finite L k hk)).mp hw
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hwk' : (k : ℝ) ≤ (L.filter (fun l => w ∈ linePoints l)).card := by
        exact_mod_cast hwk
      rw [Sampling.offDiag_card_real]
      exact mul_le_mul hwk' (sub_le_sub_right hwk' 1)
        (by linarith only [hk']) (by linarith only [hk', hwk'])
    _ ≤ (L.offDiag.card : ℝ) := hreal
    _ = _ := Sampling.offDiag_card_real L

open Classical in
theorem mean_richCount_fixed_size {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (k m : ℕ) (hk : 2 ≤ k)
    (hkm : k ≤ m) (hmn : m ≤ L.card) :
    (Nat.choose m k : ℝ) * (richCount L k : ℝ) ≤
      (Nat.choose L.card k : ℝ) *
        finiteMean (L.powersetCard m) (fun T => (richCount T k : ℝ)) := by
  classical
  have hs := Sampling.mean_ncard_lower (L.powersetCard m) (richPoints L k)
    (richPoints_finite L k hk) (fun T => richPoints T k)
    (fun T _ => richPoints_finite T k hk)
    ((Nat.choose m k : ℝ) / (Nat.choose L.card k : ℝ)) (by
      intro w hw
      obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hw
      have hWL : W ⊆ L := hW.trans (Finset.filter_subset _ _)
      have hexp := Sampling.expect_subset_powersetCard L W hWL m hmn
      rw [hWcard] at hexp
      rw [← hexp]
      apply Finset.expect_le_expect
      intro T _
      by_cases hWT : W ⊆ T
      · have hwr : w ∈ richPoints T k := by
          change k ≤ (T.filter (fun l => w ∈ linePoints l)).card
          rw [← hWcard]
          apply Finset.card_le_card
          intro l hl
          exact Finset.mem_filter.mpr ⟨hWT hl, (Finset.mem_filter.mp (hW hl)).2⟩
        simp only [ite_eq_left hWT, ite_eq_left hwr, le_refl]
      · simp only [ite_eq_right hWT]
        split_ifs <;> norm_num)
  have hn : (0 : ℝ) < (Nat.choose L.card k : ℝ) := by
    exact_mod_cast Nat.choose_pos (hkm.trans hmn)
  rw [div_mul_eq_mul_div] at hs
  have hs' := (div_le_iff₀ hn).mp hs
  simpa only [finiteMean, richCount, mul_comm] using hs'

end ExplicitRIP.Zahl
