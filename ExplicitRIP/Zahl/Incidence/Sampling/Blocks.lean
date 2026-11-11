/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Colors

/-! # Three disjoint witness blocks -/

public section

namespace ExplicitRIP.Zahl.Sampling

open scoped BigOperators

lemma exists_three_blocks {α : Type*} (W : Finset α) (m : ℕ) (hm : 3 * m ≤ W.card) :
    ∃ blocks : Fin 3 → Finset α,
      (∀ i, blocks i ⊆ W ∧ (blocks i).card = m) ∧
      Pairwise (fun i j => Disjoint (blocks i) (blocks j)) := by
  classical
  obtain ⟨A, hAW, hA⟩ := Finset.exists_subset_card_eq (show m ≤ W.card by omega)
  have hmB : m ≤ (W \ A).card := by
    rw [Finset.card_sdiff_of_subset hAW, hA]
    omega
  obtain ⟨B, hBWA, hB⟩ := Finset.exists_subset_card_eq hmB
  have hBW : B ⊆ W := hBWA.trans Finset.sdiff_subset
  have hAB : Disjoint A B := Finset.disjoint_sdiff.mono_right hBWA
  have hABW : A ∪ B ⊆ W := Finset.union_subset hAW hBW
  have hmC : m ≤ (W \ (A ∪ B)).card := by
    rw [Finset.card_sdiff_of_subset hABW, Finset.card_union_of_disjoint hAB, hA, hB]
    omega
  obtain ⟨C, hCWAB, hC⟩ := Finset.exists_subset_card_eq hmC
  have hCW : C ⊆ W := hCWAB.trans Finset.sdiff_subset
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_sdiff.mono_right hCWAB
  obtain ⟨hAC, hBC⟩ := Finset.disjoint_union_left.mp hABC
  refine ⟨![A, B, C], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]

lemma block_probability_lower (m k : ℕ) (hk : 0 < k) (hmk : m ≤ k) (hkm : k ≤ 5 * m) :
    (1 / 10 : ℝ) ≤ (m : ℝ) / (k : ℝ) -
      (m : ℝ) * ((m : ℝ) - 1) / (2 * (k : ℝ) ^ 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let t : ℝ := (m : ℝ) / (k : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg m) hkR.le
  have ht1 : t ≤ 1 := (div_le_one hkR).mpr (by exact_mod_cast hmk)
  have ht5 : (1 / 5 : ℝ) ≤ t := by
    apply (le_div_iff₀ hkR).mpr
    have h : (k : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast hkm
    linarith
  have hquad : (m : ℝ) * ((m : ℝ) - 1) / (2 * (k : ℝ) ^ 2) ≤ t ^ 2 / 2 := by
    calc
      _ ≤ ((m : ℝ) * (m : ℝ)) / (2 * (k : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      _ = _ := by dsimp [t]; ring
  change 1 / 10 ≤ t - _
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]

open Classical in
lemma three_blocks_rich {K : Type*} [Field K] [DecidableEq (ChartLine K)]
    (S : Finset (ChartLine K)) (w : Point K)
    (blocks : Fin 3 → Finset (ChartLine K))
    (hincident : ∀ i, ∀ l ∈ blocks i, w ∈ linePoints l)
    (hd : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (hne : ∀ i, (S ∩ blocks i).Nonempty) : w ∈ richPoints S 3 := by
  let B (i : Fin 3) := S ∩ blocks i
  have hB : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact (hd hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hsub : Finset.univ.biUnion B ⊆ S.filter (fun l => w ∈ linePoints l) := by
    intro l hl
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨hlS, hli⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_filter.mpr ⟨hlS, hincident i l hli⟩
  change 3 ≤ (S.filter (fun l => w ∈ linePoints l)).card
  calc
    3 = ∑ _i : Fin 3, 1 := by simp
    _ ≤ ∑ i : Fin 3, (B i).card := Finset.sum_le_sum fun i _ => (hne i).card_pos
    _ = (Finset.univ.biUnion B).card := (Finset.card_biUnion hB).symm
    _ ≤ _ := Finset.card_le_card hsub

end ExplicitRIP.Zahl.Sampling
