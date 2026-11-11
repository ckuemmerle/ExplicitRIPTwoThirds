/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Surfaces.Extraction

/-!
# Bichromatic extraction in the admissible characteristic range

This estimate assumes the Guth–Zahl structure theorem for Heisenberg lines, proved by
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`.
-/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_admissible_bichromatic_constant
    (hG10 : (open Classical in
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
          ∀ L : Finset (HLine (ZMod p)),
            (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 →
            ∀ A : ℝ, C * Real.sqrt (L.card : ℝ) ≤ A →
              (richCount (chartImage L) 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
                (∃ normal : Point (QuadraticExtension (ZMod p)), normal ≠ 0 ∧
                  ∃ offset : QuadraticExtension (ZMod p),
                    A ≤ (((chartImage L).filter (planeContains normal offset)).card : ℝ)) ∨
                ∃ Q : SplitQuadric (QuadraticExtension (ZMod p)),
                  A ≤ (((chartImage L).filter (quadricContains Q)).card : ℝ))) :
    ∃ c a D : ℝ, 0 < c ∧ c ≤ 1 ∧ 3 ≤ a ∧ 1 ≤ D ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
        (R B : Finset (HLine (ZMod p))), Disjoint R B →
        ((R ∪ B).card : ℝ) ≤ c * (p : ℝ) ^ 2 →
        ∀ A : ℝ, a * Real.sqrt ((R ∪ B).card : ℝ) ≤ A →
          ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) ≤
              D * A * ((R ∪ B).card : ℝ) ∨
            ∃ Q : SplitQuadric (QuadraticExtension (ZMod p)), ∃ side : Bool,
              A ≤ (rulingCount Q side (chartImage R) : ℝ) ∧
              A ≤ (rulingCount Q (!side) (chartImage B) : ℝ)
 := by
  obtain ⟨c, C, hc, hc1, hC, hG⟩ := hG10
  refine ⟨c, C + 4, 2 + 4 * C, hc, hc1, by linarith, by linarith, ?_⟩
  intro p _ _ R B hRB hn A hA
  let : DecidableEq (QuadraticExtension (ZMod p)) := Classical.decEq _
  by_cases hempty : R ∪ B = ∅
  · obtain ⟨rfl, rfl⟩ := Finset.union_eq_empty.mp hempty
    left
    simp [chartImage, bichromaticPoints]
  let n : ℝ := (R ∪ B).card
  have hn1 : 1 ≤ n := by
    change (1 : ℝ) ≤ (R ∪ B).card
    exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn1
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrt1 : 1 ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hn1
    simpa only [Real.sqrt_one] using h
  have hA3 : 3 * Real.sqrt n ≤ A := by
    have h := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ C + 4 by linarith) hsqrt0
    exact h.trans hA
  have hA0 : 0 ≤ A := (mul_nonneg (by norm_num) hsqrt0).trans hA3
  have hA1 : 1 ≤ A := by linarith only [hA3, hsqrt1]
  have hsq : 2 * n < A ^ 2 := by
    have h := mul_self_le_mul_self (mul_nonneg (by norm_num) hsqrt0) hA3
    nlinarith only [h, Real.sq_sqrt hn0, hn1]
  by_cases hbound : ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) ≤
      (2 + 4 * C) * A * n
  · exact Or.inl hbound
  apply Or.inr
  have hd := chartImage_disjoint hRB
  obtain ⟨R', B', hR', hB', hprune, hdegree⟩ :=
    exists_bichromatic_pruning (chartImage R) (chartImage B) hd (2 * A) (by positivity)
  obtain ⟨R₁, hR₁, hRchart⟩ := exists_chartImage_subfamily R hR'
  obtain ⟨B₁, hB₁, hBchart⟩ := exists_chartImage_subfamily B hB'
  let T := R₁ ∪ B₁
  have hTchart : chartImage T = R' ∪ B' := by
    change chartImage (R₁ ∪ B₁) = R' ∪ B'
    rw [chartImage_union R₁ B₁, hRchart, hBchart]
  have hTsub : T ⊆ R ∪ B := Finset.union_subset_union hR₁ hB₁
  have hm : (T.card : ℝ) ≤ n := Nat.cast_le.mpr (Finset.card_le_card hTsub)
  have hmn : ((R' ∪ B').card : ℝ) ≤ n := by
    rw [← hTchart, chartImage_card]
    exact hm
  have hdisj : Disjoint R' B' := hd.mono hR' hB'
  rw [← chartImage_union R B, chartImage_card] at hprune
  have hb : 4 * C * A * n < ((bichromaticPoints R' B').ncard : ℝ) := by
    have hpos := mul_nonneg hA0 (Nat.cast_nonneg (α := ℝ) (R' ∪ B').card)
    change ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) -
      2 * A * (n - ((R' ∪ B').card : ℝ)) ≤ _ at hprune
    nlinarith only [hprune, hpos, lt_of_not_ge hbound]
  have hb' : C * (4 * A) * (T.card : ℝ) <
      ((bichromaticPoints R' B').ncard : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ C * (4 * A) by positivity)
    nlinarith only [h, hb]
  have hrich : ((bichromaticPoints R' B').ncard : ℝ) ≤
      (richCount (chartImage T) 2 : ℝ) := by
    apply Nat.cast_le.mpr
    apply Set.ncard_le_ncard ?_ (richPoints_finite (chartImage T) 2 le_rfl)
    rw [hTchart]
    exact bichromaticPoints_subset_richPoints_two
      Finset.subset_union_left Finset.subset_union_right hdisj
  have hthreshold : C * Real.sqrt (T.card : ℝ) ≤ 4 * A := by
    have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (show 0 ≤ C by linarith)
    change (C + 4) * Real.sqrt n ≤ A at hA
    nlinarith only [hs, hA, hsqrt0, hA0]
  rcases hG p T (hm.trans hn) (4 * A) hthreshold with hcount | hplane | ⟨Q, hQ⟩
  · exact False.elim (not_lt_of_ge (hrich.trans hcount) hb')
  · obtain ⟨normal, hnormal, offset, hplane⟩ := hplane
    obtain ⟨w₀, hthrough⟩ := heisenberg_plane_through_le_one T normal hnormal offset
    rw [hTchart] at hthrough hplane
    have hsum := plane_bichromatic_degree_sum_le R' B' hdisj normal hnormal offset w₀ hthrough
    let S := (R' ∪ B').filter (planeContains normal offset)
    have hsum' : (∑ l ∈ S, ((bichromaticPoints R' B' ∩ linePoints l).ncard : ℝ)) ≤
        (S.card : ℝ) + ((R' ∪ B').card : ℝ) := by exact_mod_cast hsum
    have hlo : 2 * A * (S.card : ℝ) ≤
        ∑ l ∈ S, ((bichromaticPoints R' B' ∩ linePoints l).ncard : ℝ) := by
      calc
        _ = ∑ _l ∈ S, (2 * A) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun l hl => le_of_lt
          (hdegree l (Finset.mem_filter.mp hl).1)
    have hprod := mul_le_mul_of_nonneg_left hplane hA0
    have hprod' := mul_le_mul_of_nonneg_right hA1 (Nat.cast_nonneg (α := ℝ) S.card)
    change A * (4 * A) ≤ A * (S.card : ℝ) at hprod
    exact False.elim (by nlinarith only [hsum', hlo, hmn, hprod, hprod', hsq])
  · rw [hTchart] at hQ
    have h2 : (2 : QuadraticExtension (ZMod p)) ≠ 0 := by
      intro heq
      have hbase := two_ne_zero_of_neg_one_not_isSquare
        (show ¬ IsSquare (-1 : ZMod p) from Fact.out)
      apply hbase
      apply (algebraMap (ZMod p) (QuadraticExtension (ZMod p))).injective
      simpa only [map_ofNat, map_zero] using heq
    obtain ⟨side, hr, hb⟩ := quadric_extract h2 Q R' B' hdisj n A hmn hA0 hsq hdegree hQ
    exact ⟨Q, side, hr.trans (Nat.cast_le.mpr (rulingCount_mono Q side hR')),
      hb.trans (Nat.cast_le.mpr (rulingCount_mono Q (!side) hB'))⟩

end ExplicitRIP.Zahl
