/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Relative.Zahl.TwoRich.Admissible

/-!
# Bichromatic extraction throughout the full characteristic range

This estimate assumes the Guth–Zahl structure theorem for Heisenberg lines, proved by
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`.
-/

public section

namespace ExplicitRIP.Zahl


open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_affine_bichromatic_constant
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
    ∃ a D : ℝ, 3 ≤ a ∧ 0 < D ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
        (R B : Finset (HLine (ZMod p))), Disjoint R B →
        (R ∪ B).card ≤ p ^ 2 →
        ∀ A : ℝ, a * Real.sqrt ((R ∪ B).card : ℝ) ≤ A →
          ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) ≤
              D * A * ((R ∪ B).card : ℝ) ∨
            ∃ Q : SplitQuadric (QuadraticExtension (ZMod p)), ∃ side : Bool,
              A ≤ (rulingCount Q side (chartImage R) : ℝ) ∧
              A ≤ (rulingCount Q (!side) (chartImage B) : ℝ)
 := by
  obtain ⟨c, a, D, hc, hc1, ha, hD, hbase⟩ :=
    ExplicitRIP.Relative.Zahl.exists_admissible_bichromatic_constant hG10
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hcoef : 0 < 8 * D / c ^ 2 := by positivity
  have hcoef4 : 4 / c ≤ 8 * D / c ^ 2 := by
    apply (div_le_div_iff₀ hc (sq_pos_of_pos hc)).mpr
    have h := mul_le_mul_of_nonneg_right (show 4 * c ≤ 8 * D by linarith only [hc1, hD]) hc.le
    nlinarith only [h]
  refine ⟨a, 8 * D / c ^ 2, ha, hcoef, ?_⟩
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
  have hsqrt1 : 1 ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hA1 : 1 ≤ A := by
    have h := mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg n)
    change a * Real.sqrt n ≤ A at hA
    nlinarith only [h, hA, hsqrt1]
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA1
  have hd := chartImage_disjoint hRB
  by_cases hlarge : 4 / c ≤ n
  · obtain ⟨R', B', hR', hB', hsize, hcount⟩ :=
      exists_small_bichromatic_subfamily (chartImage R) (chartImage B) hd c hc hc1 (by
        rw [← chartImage_union R B, chartImage_card]
        exact hlarge)
    obtain ⟨R₁, hR₁, hRchart⟩ := exists_chartImage_subfamily R hR'
    obtain ⟨B₁, hB₁, hBchart⟩ := exists_chartImage_subfamily B hB'
    have hTchart : chartImage (R₁ ∪ B₁) = R' ∪ B' := by
      rw [chartImage_union R₁ B₁, hRchart, hBchart]
    have hm : ((R₁ ∪ B₁).card : ℝ) ≤ n :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.union_subset_union hR₁ hB₁))
    have hsmall : ((R₁ ∪ B₁).card : ℝ) ≤ c * (p : ℝ) ^ 2 := by
      rw [← hTchart, chartImage_card, ← chartImage_union R B, chartImage_card] at hsize
      apply hsize.trans
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact_mod_cast hn
    have hthreshold : a * Real.sqrt ((R₁ ∪ B₁).card : ℝ) ≤ A :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) ha0).trans hA
    rcases hbase p R₁ B₁ (hRB.mono hR₁ hB₁) hsmall A hthreshold with h | ⟨Q, side, hr, hb⟩
    · left
      rw [hRchart, hBchart] at h
      have hupper := hcount.trans
        (h.trans (mul_le_mul_of_nonneg_left hm (show 0 ≤ D * A by positivity)))
      have hfactor : 0 < c ^ 2 / 8 := by positivity
      apply (mul_le_mul_iff_right₀ hfactor).mp
      calc
        _ ≤ D * A * n := hupper
        _ = c ^ 2 / 8 * (8 * D / c ^ 2 * A * n) := by field_simp
    · right
      exact ⟨Q, side, hr.trans (Nat.cast_le.mpr (rulingCount_mono Q side (chartImage_mono hR₁))),
        hb.trans (Nat.cast_le.mpr (rulingCount_mono Q (!side) (chartImage_mono hB₁)))⟩
  · left
    have hbi : ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) ≤
        (richCount (chartImage (R ∪ B)) 2 : ℝ) := by
      apply Nat.cast_le.mpr
      apply Set.ncard_le_ncard ?_ (richPoints_finite (chartImage (R ∪ B)) 2 le_rfl)
      rw [chartImage_union R B]
      exact bichromaticPoints_subset_richPoints_two
        Finset.subset_union_left Finset.subset_union_right hd
    have hpair := richCount_pair_bound (chartImage (R ∪ B)) 2 le_rfl
    rw [chartImage_card] at hpair
    norm_num only [Nat.cast_ofNat] at hpair
    change (richCount (chartImage (R ∪ B)) 2 : ℝ) * 2 * 1 ≤ n * (n - 1) at hpair
    have hb : ((bichromaticPoints (chartImage R) (chartImage B)).ncard : ℝ) ≤ n ^ 2 := by
      nlinarith only [hbi, hpair, hn0, sq_nonneg n]
    calc
      _ ≤ n ^ 2 := hb
      _ ≤ (4 / c) * n := by nlinarith only [mul_le_mul_of_nonneg_right (le_of_not_ge hlarge) hn0]
      _ ≤ (8 * D / c ^ 2) * n := mul_le_mul_of_nonneg_right hcoef4 hn0
      _ ≤ (8 * D / c ^ 2) * A * n := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right hcoef.le hA1) hn0

end ExplicitRIP.Zahl
