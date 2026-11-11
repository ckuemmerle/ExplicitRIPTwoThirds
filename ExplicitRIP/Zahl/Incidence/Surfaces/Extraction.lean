/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Surfaces.Bichromatic

/-! # Extraction of opposite color rulings from a pruned family -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
lemma contained_card_le_four_ruling_counts {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K) (R B : Finset (ChartLine K)) :
    ((R ∪ B).filter (quadricContains Q)).card ≤
      rulingCount Q false R + rulingCount Q true R +
        rulingCount Q false B + rulingCount Q true B := by
  have hsplit (T : Finset (ChartLine K)) :
      (T.filter (quadricContains Q)).card ≤ rulingCount Q false T + rulingCount Q true T := by
    have heq : T.filter (quadricContains Q) =
        T.filter (inRuling Q false) ∪ T.filter (inRuling Q true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_union, quadricContains_iff_inRuling h2,
        and_or_left]
    rw [heq]
    exact Finset.card_union_le _ _
  rw [Finset.filter_union]
  have h := (Finset.card_union_le (R.filter (quadricContains Q))
    (B.filter (quadricContains Q))).trans (Nat.add_le_add (hsplit R) (hsplit B))
  omega

open Classical in
lemma opposite_ruling_large {K : Type*} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K) (side : Bool)
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (n A : ℝ) (hN : ((R ∪ B).card : ℝ) ≤ n) (hA : 0 ≤ A)
    (hsq : 2 * n < A ^ 2)
    (hdegree : ∀ l ∈ R ∪ B,
      2 * A < ((bichromaticPoints R B ∩ linePoints l).ncard : ℝ))
    (hlarge : A ≤ (rulingCount Q side R : ℝ)) :
    A ≤ (rulingCount Q (!side) B : ℝ) := by
  by_contra hsmall
  have ht : (rulingCount Q (!side) B : ℝ) ≤ A := le_of_lt (lt_of_not_ge hsmall)
  have hsum : 2 * A * (rulingCount Q side R : ℝ) ≤
      ∑ l ∈ R.filter (inRuling Q side),
        ((bichromaticPoints R B ∩ linePoints l).ncard : ℝ) := by
    calc
      _ = ∑ _l ∈ R.filter (inRuling Q side), (2 * A) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        rfl
      _ ≤ _ := Finset.sum_le_sum fun l hl =>
        le_of_lt (hdegree l (Finset.mem_union_left B (Finset.mem_filter.mp hl).1))
  have hbudget := ruling_bichromatic_degree_sum_le h2 Q side R B hRB
  have hbudget' : (∑ l ∈ R.filter (inRuling Q side),
        ((bichromaticPoints R B ∩ linePoints l).ncard : ℝ)) ≤
      (rulingCount Q side R : ℝ) * (rulingCount Q (!side) B : ℝ) + 2 * (B.card : ℝ) := by
    exact_mod_cast hbudget
  have hB : (B.card : ℝ) ≤ n :=
    (Nat.cast_le.mpr (Finset.card_le_card Finset.subset_union_right)).trans hN
  have hs0 : (0 : ℝ) ≤ rulingCount Q side R := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_left ht hs0
  have hprod' := mul_le_mul_of_nonneg_left hlarge hA
  nlinarith only [hsum, hbudget', hB, hprod, hprod', hsq]

open Classical in
lemma quadric_extract {K : Type*} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (Q : SplitQuadric K)
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (n A : ℝ) (hN : ((R ∪ B).card : ℝ) ≤ n) (hA : 0 ≤ A)
    (hsq : 2 * n < A ^ 2)
    (hdegree : ∀ l ∈ R ∪ B,
      2 * A < ((bichromaticPoints R B ∩ linePoints l).ncard : ℝ))
    (hQ : 4 * A ≤ (((R ∪ B).filter (quadricContains Q)).card : ℝ)) :
    ∃ side : Bool, A ≤ (rulingCount Q side R : ℝ) ∧
      A ≤ (rulingCount Q (!side) B : ℝ) := by
  have hsum : (((R ∪ B).filter (quadricContains Q)).card : ℝ) ≤
      (rulingCount Q false R : ℝ) + (rulingCount Q true R : ℝ) +
        (rulingCount Q false B : ℝ) + (rulingCount Q true B : ℝ) := by
    exact_mod_cast contained_card_le_four_ruling_counts h2 Q R B
  have hfour : A ≤ (rulingCount Q false R : ℝ) ∨
      A ≤ (rulingCount Q true R : ℝ) ∨ A ≤ (rulingCount Q false B : ℝ) ∨
      A ≤ (rulingCount Q true B : ℝ) := by
    by_contra h
    push Not at h
    linarith only [hsum, hQ, h.1, h.2.1, h.2.2.1, h.2.2.2]
  have hswap : ∀ l ∈ B ∪ R,
      2 * A < ((bichromaticPoints B R ∩ linePoints l).ncard : ℝ) := by
    simpa only [Finset.union_comm B R, bichromaticPoints_comm B R] using hdegree
  have hNswap : ((B ∪ R).card : ℝ) ≤ n := by
    simpa only [Finset.union_comm B R] using hN
  rcases hfour with h | h | h | h
  · exact ⟨false, h, opposite_ruling_large h2 Q false R B hRB n A hN hA hsq hdegree h⟩
  · exact ⟨true, h, opposite_ruling_large h2 Q true R B hRB n A hN hA hsq hdegree h⟩
  · exact ⟨true, opposite_ruling_large h2 Q false B R hRB.symm n A
      hNswap hA hsq hswap h, h⟩
  · exact ⟨false, opposite_ruling_large h2 Q true B R hRB.symm n A
      hNswap hA hsq hswap h, h⟩

end ExplicitRIP.Zahl
