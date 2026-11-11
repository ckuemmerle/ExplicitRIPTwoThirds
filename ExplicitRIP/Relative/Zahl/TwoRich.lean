/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Relative.Zahl.TwoRich.Affine

/-!
# The two-rich alternative

This alternative assumes the Guth–Zahl structure theorem for Heisenberg lines, proved by
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`.
-/

public section

namespace ExplicitRIP.Zahl


open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_affine_two_rich_constant
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
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
        (L : Finset (HLine (ZMod p))), L.card ≤ p ^ 2 →
        (richCount (chartImage L) 2 : ℝ) ≤ C * (L.card : ℝ) ^ (3 / 2 : ℝ) ∨
          ∃ Q : SplitQuadric (QuadraticExtension (ZMod p)),
            3 ≤ rulingCount Q false (chartImage L) ∧
            3 ≤ rulingCount Q true (chartImage L) ∧
            Real.sqrt (L.card : ℝ) ≤ (rulingCount Q false (chartImage L) : ℝ) ∧
            Real.sqrt (L.card : ℝ) ≤ (rulingCount Q true (chartImage L) : ℝ)
 := by
  obtain ⟨a, D, ha, hD, hbase⟩ :=
    ExplicitRIP.Relative.Zahl.exists_affine_bichromatic_constant hG10
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  refine ⟨2 * a * D, by positivity, ?_⟩
  intro p _ _ L hn
  let : DecidableEq (QuadraticExtension (ZMod p)) := Classical.decEq _
  by_cases hempty : L = ∅
  · subst L
    left
    have heq : richPoints (chartImage (∅ : Finset (HLine (ZMod p)))) 2 = ∅ := by
      ext w
      simp [richPoints, chartImage]
    simp [richCount, heq]
  have hn1 : (1 : ℝ) ≤ L.card := by
    exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hsqrt1 : 1 ≤ Real.sqrt (L.card : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have hA3 : 3 ≤ a * Real.sqrt (L.card : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt1 ha0.le, ha]
  have hsqrtA : Real.sqrt (L.card : ℝ) ≤ a * Real.sqrt (L.card : ℝ) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) (by linarith only [ha])
  obtain ⟨χ, _, hcolor⟩ := Finset.exists_le_of_le_expect
    (Finset.univ_nonempty : (Finset.univ : Finset (↥(chartImage L) → Fin 2)).Nonempty)
    (mean_bichromatic_of_two_rich (chartImage L))
  let R := colorSample (chartImage L) χ
  let B := chartImage L \ R
  have hR : R ⊆ chartImage L := colorSample_subset _ _
  have hB : B ⊆ chartImage L := Finset.sdiff_subset
  have hd : Disjoint R B := Finset.disjoint_sdiff
  have hunion : R ∪ B = chartImage L := Finset.union_sdiff_of_subset hR
  obtain ⟨R₁, hR₁, hRchart⟩ := exists_chartImage_subfamily L hR
  obtain ⟨B₁, hB₁, hBchart⟩ := exists_chartImage_subfamily L hB
  have hd₁ : Disjoint R₁ B₁ := by
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    apply Finset.disjoint_left.mp hd
    · rw [← hRchart]
      simp only [chartImage, Finset.mem_image]
      exact ⟨l, hl, rfl⟩
    · rw [← hBchart]
      simp only [chartImage, Finset.mem_image]
      exact ⟨l, hl', rfl⟩
  have hcard : (R₁ ∪ B₁).card = L.card := by
    rw [← chartImage_card (R₁ ∪ B₁), chartImage_union R₁ B₁, hRchart, hBchart,
      hunion, chartImage_card]
  rcases hbase p R₁ B₁ hd₁ (by rwa [hcard])
      (a * Real.sqrt (L.card : ℝ)) (by rw [hcard]) with hcount | ⟨Q, side, hr, hb⟩
  · left
    rw [hRchart, hBchart, hcard] at hcount
    have hrpow : (L.card : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (L.card : ℝ) * L.card := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) (by norm_num),
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hrpow]
    change (richCount (chartImage L) 2 : ℝ) / 2 ≤ ((bichromaticPoints R B).ncard : ℝ) at hcolor
    nlinarith only [hcolor, hcount]
  · right
    have hr' : a * Real.sqrt (L.card : ℝ) ≤ (rulingCount Q side (chartImage L) : ℝ) :=
      hr.trans (Nat.cast_le.mpr (rulingCount_mono Q side (chartImage_mono hR₁)))
    have hb' : a * Real.sqrt (L.card : ℝ) ≤ (rulingCount Q (!side) (chartImage L) : ℝ) :=
      hb.trans (Nat.cast_le.mpr (rulingCount_mono Q (!side) (chartImage_mono hB₁)))
    have hr3 : 3 ≤ rulingCount Q side (chartImage L) := by exact_mod_cast hA3.trans hr'
    have hb3 : 3 ≤ rulingCount Q (!side) (chartImage L) := by exact_mod_cast hA3.trans hb'
    cases side with
    | false => exact ⟨Q, hr3, hb3, hsqrtA.trans hr', hsqrtA.trans hb'⟩
    | true => exact ⟨Q, hb3, hr3, hsqrtA.trans hb', hsqrtA.trans hr'⟩

end ExplicitRIP.Zahl
