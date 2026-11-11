/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Surfaces.ThreeRich
public import ExplicitRIP.Zahl.Incidence.Pruning.Deletion

/-!
# The admissible three-rich estimate

This estimate assumes the Guth–Zahl structure theorem for Heisenberg lines, proved by
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`.
-/

public section

namespace ExplicitRIP.Zahl


open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_admissible_three_rich_constant
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
    ∃ c B : ℝ, 0 < c ∧ c ≤ 1 ∧ 4 ≤ B ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
        (L : Finset (HLine (ZMod p))),
        (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 →
        (richCount (chartImage L) 3 : ℝ) ≤ B * (L.card : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨c, C, hc, hc1, hC, hstructure⟩ := hG10
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨c, 4 + C * (C + 4), hc, hc1, by nlinarith only [hC], ?_⟩
  intro p _ _ L hL
  by_cases hn : L.card = 0
  · rw [richCount_eq_zero_of_card_lt (chartImage L) (by rw [chartImage_card, hn]; omega)]
    simp only [Nat.cast_zero]
    positivity
  have hnpos : (0 : ℝ) < L.card := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 ≤ Real.sqrt (L.card : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (L.card : ℝ) ^ 2 = (L.card : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hrpow : (L.card : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (L.card : ℝ) * (L.card : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  by_contra hbound
  have hbad := lt_of_not_ge hbound
  rw [hrpow] at hbad
  obtain ⟨T, hT, hprune, hdegree⟩ := exists_rich_pruning (chartImage L) 3 (by omega)
    (4 * Real.sqrt (L.card : ℝ)) (by positivity)
  obtain ⟨S, hSL, hST⟩ := exists_chartImage_subfamily L hT
  subst T
  simp only [chartImage_card] at hprune
  have hmn : (S.card : ℝ) ≤ (L.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSL
  have hCA : 0 ≤ C * ((C + 4) * Real.sqrt (L.card : ℝ)) := by positivity
  have hlower : C * ((C + 4) * Real.sqrt (L.card : ℝ)) * (L.card : ℝ) <
      (richCount (chartImage S) 3 : ℝ) := by
    have hnonneg : 0 ≤ (4 * Real.sqrt (L.card : ℝ)) * (S.card : ℝ) := by positivity
    nlinarith only [hbad, hprune, hnonneg]
  have hlower' : C * ((C + 4) * Real.sqrt (L.card : ℝ)) * (S.card : ℝ) <
      (richCount (chartImage S) 3 : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmn hCA) hlower
  have hthreshold : C * Real.sqrt (S.card : ℝ) ≤
      (C + 4) * Real.sqrt (L.card : ℝ) := by
    calc
      _ ≤ C * Real.sqrt (L.card : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmn) hC0
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only : C ≤ C + 4) hs0
  have hcontr (R : Finset (ChartLine (QuadraticExtension (ZMod p))))
      (hRsub : R ⊆ chartImage S)
      (hR : (C + 4) * Real.sqrt (L.card : ℝ) ≤ (R.card : ℝ))
      (hbudget : (∑ l ∈ R, (richPoints (chartImage S) 3 ∩ linePoints l).ncard) ≤
        4 * (chartImage S).card) : False := by
    have hsum : (4 * Real.sqrt (L.card : ℝ)) * (R.card : ℝ) ≤
        ((∑ l ∈ R, (richPoints (chartImage S) 3 ∩ linePoints l).ncard) : ℝ) := by
      calc
        _ = ∑ _l ∈ R, 4 * Real.sqrt (L.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ l ∈ R, ((richPoints (chartImage S) 3 ∩ linePoints l).ncard : ℝ) :=
          Finset.sum_le_sum (fun l hl => (hdegree l (hRsub hl)).le)
        _ = _ := rfl
    have hbudget' :
        ((∑ l ∈ R, (richPoints (chartImage S) 3 ∩ linePoints l).ncard) : ℝ) ≤
          4 * (S.card : ℝ) := by
      rw [chartImage_card] at hbudget
      exact_mod_cast hbudget
    have hprod : 4 * (C + 4) * (L.card : ℝ) ≤
        (4 * Real.sqrt (L.card : ℝ)) * (R.card : ℝ) := by
      calc
        _ = (4 * Real.sqrt (L.card : ℝ)) *
            ((C + 4) * Real.sqrt (L.card : ℝ)) := by
          calc
            _ = 4 * (C + 4) * (Real.sqrt (L.card : ℝ) ^ 2) :=
              congrArg (fun x : ℝ => 4 * (C + 4) * x) hsq.symm
            _ = _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
    have hstrict : 4 * (L.card : ℝ) < 4 * (C + 4) * (L.card : ℝ) := by
      exact mul_lt_mul_of_pos_right (by linarith only [hC]) hnpos
    linarith only [hprod, hsum, hbudget', hmn, hstrict]
  rcases hstructure p S (hmn.trans hL) ((C + 4) * Real.sqrt (L.card : ℝ)) hthreshold with
    hcount | ⟨normal, hnormal, offset, hplane⟩ | ⟨Q, hquadric⟩
  · have hmono : (richCount (chartImage S) 3 : ℝ) ≤ (richCount (chartImage S) 2 : ℝ) := by
      exact_mod_cast richCount_antitone (chartImage S) (by omega : 2 ≤ 2) (by omega : 2 ≤ 3)
    linarith only [hlower', hcount, hmono]
  · exact hcontr _ (Finset.filter_subset _ _) hplane
      (plane_three_rich_degree_sum_le S normal hnormal offset)
  · have h2 : (2 : QuadraticExtension (ZMod p)) ≠ 0 := by
      have hbase := two_ne_zero_of_neg_one_not_isSquare (zmod_neg_one_not_isSquare p)
      have hm := (algebraMap (ZMod p) (QuadraticExtension (ZMod p))).injective.ne hbase
      simpa only [map_ofNat, map_zero] using hm
    exact hcontr _ (Finset.filter_subset _ _) hquadric
      (quadric_three_rich_degree_sum_le h2 (chartImage S) Q)

end ExplicitRIP.Zahl
