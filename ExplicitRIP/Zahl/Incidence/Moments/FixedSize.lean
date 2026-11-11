/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Bichromatic

/-! # Small bichromatic subfamilies from exact-size sampling -/

public section

namespace ExplicitRIP.Zahl

open Classical in
/-- Exact-size sampling preserves a fixed fraction of bichromatic points. -/
theorem exists_small_bichromatic_subfamily {K : Type*} [Field K]
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : 4 / c ≤ ((R ∪ B).card : ℝ)) :
    ∃ R' B' : Finset (ChartLine K), R' ⊆ R ∧ B' ⊆ B ∧
      ((R' ∪ B').card : ℝ) ≤ c * ((R ∪ B).card : ℝ) ∧
      c ^ 2 / 8 * ((bichromaticPoints R B).ncard : ℝ) ≤
        ((bichromaticPoints R' B').ncard : ℝ) := by
  classical
  let n : ℕ := (R ∪ B).card
  let m : ℕ := ⌊c * (n : ℝ)⌋₊
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hcn : 4 ≤ c * (n : ℝ) := by
    have h := (div_le_iff₀ hc).mp hlarge
    simpa only [n, mul_comm] using h
  have hfloor : (m : ℝ) ≤ c * (n : ℝ) := Nat.floor_le (by positivity)
  have hfloor' : c * (n : ℝ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : 2 ≤ m := Nat.le_floor (by
    norm_num only [Nat.cast_ofNat]
    linarith only [hcn])
  have hmn : m ≤ n := Nat.floor_le_of_le (mul_le_of_le_one_left hn0 hc1)
  have hmlo : c * (n : ℝ) / 2 ≤ (m : ℝ) := by linarith only [hcn, hfloor']
  have hmlo' : c * (n : ℝ) / 2 ≤ (m : ℝ) - 1 := by
    linarith only [hcn, hfloor']
  have hprod : (c * (n : ℝ) / 2) ^ 2 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    simpa only [pow_two] using mul_le_mul hmlo hmlo' (by positivity)
      (Nat.cast_nonneg (α := ℝ) m)
  have hchoose : (Nat.choose n 2 : ℝ) * (c ^ 2 / 8) ≤ (Nat.choose m 2 : ℝ) := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    nlinarith only [hprod, mul_nonneg (sq_nonneg c) hn0, sq_nonneg (c * (n : ℝ))]
  have hnchoose : (0 : ℝ) < Nat.choose n 2 := by
    exact_mod_cast Nat.choose_pos (hm.trans hmn)
  have hmean := mean_bichromatic_fixed_size R B hRB m hm hmn
  have hscaled := mul_le_mul_of_nonneg_right hchoose
    (Nat.cast_nonneg (α := ℝ) (bichromaticPoints R B).ncard)
  have havg : c ^ 2 / 8 * ((bichromaticPoints R B).ncard : ℝ) ≤
      finiteMean ((R ∪ B).powersetCard m)
        (fun T => ((bichromaticPoints (T ∩ R) (T ∩ B)).ncard : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hnchoose).mp
    calc
      _ = ((Nat.choose n 2 : ℝ) * (c ^ 2 / 8)) *
          ((bichromaticPoints R B).ncard : ℝ) := by ring
      _ ≤ _ := hscaled.trans hmean
  obtain ⟨T, hT, hcount⟩ := Finset.exists_le_of_le_expect
    (Finset.powersetCard_nonempty.mpr hmn) havg
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T ∩ R, T ∩ B, Finset.inter_subset_right, Finset.inter_subset_right, ?_, hcount⟩
  have hunion : T ∩ R ∪ T ∩ B = T := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hTsub]
  rw [hunion, hTcard]
  exact hfloor

end ExplicitRIP.Zahl
