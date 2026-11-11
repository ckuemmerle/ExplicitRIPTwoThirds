/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Relative.Zahl.ThreeRich.Admissible
public import ExplicitRIP.Zahl.Incidence.Pruning.Small
public import ExplicitRIP.Zahl.Incidence.Moments.Coloring
public import ExplicitRIP.Zahl.Incidence.Sampling.Rich

/-!
# Enlarging the admissible range and sampling higher multiplicities

These estimates assume the Guth–Zahl structure theorem for Heisenberg lines, proved by
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`.
-/

public section

namespace ExplicitRIP.Zahl


open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_affine_three_rich_constant
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
        (richCount (chartImage L) 3 : ℝ) ≤ C * (L.card : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨c, B, hc, hc1, hB, hbound⟩ :=
    ExplicitRIP.Relative.Zahl.exists_admissible_three_rich_constant hG10
  have hB0 : 0 ≤ B := le_trans (by norm_num : (0 : ℝ) ≤ 4) hB
  have hlargeC : 0 ≤ 48 * B / c ^ 3 := by positivity
  have hsmallC : 0 < 6 / c := by positivity
  refine ⟨48 * B / c ^ 3 + 6 / c, by positivity, ?_⟩
  intro p _ _ L hL
  have hn0 : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
  have hn32 : 0 ≤ (L.card : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hn0 _
  by_cases hlarge : 6 / c ≤ (L.card : ℝ)
  · obtain ⟨T, hT, hsize, hretain⟩ := exists_small_rich_subfamily (chartImage L) c hc hc1
      (by simpa only [chartImage_card] using hlarge)
    obtain ⟨S, hSL, hST⟩ := exists_chartImage_subfamily L hT
    subst T
    simp only [chartImage_card] at hsize
    have hScut : (S.card : ℝ) ≤ c * (p : ℝ) ^ 2 :=
      hsize.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hL) hc.le)
    have hboundS := hbound p S hScut
    have hpow : (S.card : ℝ) ^ (3 / 2 : ℝ) ≤ (L.card : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_le_card hSL)
        (by norm_num)
    have hscale : (richCount (chartImage L) 3 : ℝ) ≤
        (48 * B / c ^ 3) * (L.card : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        _ ≤ (B * (L.card : ℝ) ^ (3 / 2 : ℝ)) / (c ^ 3 / 48) := by
          apply (le_div_iff₀ (by positivity : 0 < c ^ 3 / 48)).mpr
          calc
            _ = c ^ 3 / 48 * (richCount (chartImage L) 3 : ℝ) := mul_comm _ _
            _ ≤ (richCount (chartImage S) 3 : ℝ) := hretain
            _ ≤ B * (S.card : ℝ) ^ (3 / 2 : ℝ) := hboundS
            _ ≤ _ := mul_le_mul_of_nonneg_left hpow hB0
        _ = _ := by field_simp
    exact hscale.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsmallC.le) hn32)
  · have hpair := richCount_pair_bound (chartImage L) 3 (by omega)
    simp only [chartImage_card] at hpair
    norm_num at hpair
    have hcrude : (richCount (chartImage L) 3 : ℝ) ≤ (L.card : ℝ) ^ 2 := by
      have hr0 : (0 : ℝ) ≤ (richCount (chartImage L) 3 : ℝ) := Nat.cast_nonneg _
      nlinarith only [hpair, hr0, hn0]
    have hpower : (L.card : ℝ) ≤ (L.card : ℝ) ^ (3 / 2 : ℝ) := by
      by_cases hn : L.card = 0
      · simp only [hn, Nat.cast_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), le_refl]
      · exact Real.self_le_rpow_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
          (by norm_num)
    calc
      _ ≤ (L.card : ℝ) ^ 2 := hcrude
      _ ≤ (6 / c) * (L.card : ℝ) := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (le_of_not_ge hlarge) hn0
      _ ≤ (6 / c) * (L.card : ℝ) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpower hsmallC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hlargeC) hn32

open Classical in
theorem _root_.ExplicitRIP.Relative.Zahl.exists_affine_rich_constant
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
        ∀ k : ℕ, 3 ≤ k →
          (richCount (chartImage L) k : ℝ) ≤
            C * (L.card : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  obtain ⟨B, hB, hbound⟩ := ExplicitRIP.Relative.Zahl.exists_affine_three_rich_constant hG10
  refine ⟨2000 * B, by positivity, ?_⟩
  intro p _ _ L hL k hk
  by_cases hkn : k ≤ L.card
  · have hsamples (χ : ↥(chartImage L) → Fin k) :
        (richCount (colorSample (chartImage L) χ) 3 : ℝ) ≤
          B * ((colorSample (chartImage L) χ).card : ℝ) ^ (3 / 2 : ℝ) := by
      obtain ⟨S, hSL, hS⟩ := exists_chartImage_subfamily L (colorSample_subset (chartImage L) χ)
      have h := hbound p S ((Finset.card_le_card hSL).trans hL)
      rw [← chartImage_card S, hS] at h
      exact h
    have hsurvive := mean_three_rich_of_k_rich (chartImage L) k hk
    have hmoment := mean_colorSample_card_three_halves (chartImage L) k (by omega)
      (by simpa only [chartImage_card] using hkn)
    have hmean : finiteMean (Finset.univ : Finset (↥(chartImage L) → Fin k))
        (fun χ => (richCount (colorSample (chartImage L) χ) 3 : ℝ)) ≤
          B * finiteMean (Finset.univ : Finset (↥(chartImage L) → Fin k))
            (fun χ => ((colorSample (chartImage L) χ).card : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [finiteMean, finiteMean, Finset.mul_expect]
      exact Finset.expect_le_expect (fun χ _ => hsamples χ)
    have hmoment' := mul_le_mul_of_nonneg_left hmoment hB.le
    simp only [chartImage_card] at hmoment'
    simp only [finiteMean, Sampling.expect_univ_canonical] at hsurvive hmean hmoment'
    have htotal : (richCount (chartImage L) k : ℝ) ≤
        2000 * B * ((L.card : ℝ) / (k : ℝ)) ^ (3 / 2 : ℝ) := by
      have hchain := hsurvive.trans (hmean.trans hmoment')
      calc
        _ ≤ (B * (2 * ((L.card : ℝ) / (k : ℝ)) ^ (3 / 2 : ℝ))) * 1000 :=
          (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)).mp hchain
        _ = _ := by ring
    calc
      _ ≤ 2000 * B * ((L.card : ℝ) / (k : ℝ)) ^ (3 / 2 : ℝ) := htotal
      _ = _ := by
        rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          Real.rpow_neg (Nat.cast_nonneg _)]
        ring
  · rw [richCount_eq_zero_of_card_lt (chartImage L)
      (by simpa only [chartImage_card] using Nat.lt_of_not_ge hkn)]
    simp only [Nat.cast_zero]
    positivity

end ExplicitRIP.Zahl
