/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Pruning.Counting

/-! # A small subfamily retaining a cubic fraction of three-rich points -/

public section

namespace ExplicitRIP.Zahl.Incidence.Pruning

lemma six_mul_choose_three (m : ℕ) (hm : 2 ≤ m) :
    6 * (Nat.choose m 3 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one] at h
  have h' : ((m - 2 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) * (m : ℝ)) =
      6 * (Nat.choose m 3 : ℝ) := by exact_mod_cast h
  rw [Nat.cast_sub hm, Nat.cast_sub (by omega : 1 ≤ m)] at h'
  norm_num at h'
  nlinarith only [h']

lemma choose_three_lower (m n : ℕ) (c : ℝ) (hc : 0 < c)
    (hlarge : 6 ≤ c * (n : ℝ)) (hm : c * (n : ℝ) - 1 ≤ (m : ℝ)) :
    c ^ 3 / 48 * (Nat.choose n 3 : ℝ) ≤ (Nat.choose m 3 : ℝ) := by
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have ha : 0 ≤ c * (n : ℝ) / 2 := by positivity
  have h₀ : c * (n : ℝ) / 2 ≤ (m : ℝ) := by linarith
  have h₁ : c * (n : ℝ) / 2 ≤ (m : ℝ) - 1 := by linarith
  have h₂ : c * (n : ℝ) / 2 ≤ (m : ℝ) - 2 := by linarith
  have hprod : (c * (n : ℝ) / 2) * (c * (n : ℝ) / 2) * (c * (n : ℝ) / 2) ≤
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) :=
    mul_le_mul (mul_le_mul h₀ h₁ ha (by linarith)) h₂ ha
      (mul_nonneg (Nat.cast_nonneg m) (by linarith))
  have hchoose : (Nat.choose n 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast Nat.choose_le_pow n 3
  calc
    _ ≤ c ^ 3 / 48 * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ ≤ (Nat.choose m 3 : ℝ) := by
      rw [← six_mul_choose_three m hm2] at hprod
      nlinarith only [hprod]

end ExplicitRIP.Zahl.Incidence.Pruning

namespace ExplicitRIP.Zahl

open Classical in
theorem exists_small_rich_subfamily {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : 6 / c ≤ (L.card : ℝ)) :
    ∃ T : Finset (ChartLine K), T ⊆ L ∧
      (T.card : ℝ) ≤ c * (L.card : ℝ) ∧
      c ^ 3 / 48 * (richCount L 3 : ℝ) ≤ (richCount T 3 : ℝ) := by
  classical
  let m := ⌊c * (L.card : ℝ)⌋₊
  have hcn : 6 ≤ c * (L.card : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlarge
  have hmupper : (m : ℝ) ≤ c * (L.card : ℝ) := Nat.floor_le (by positivity)
  have hmlower : c * (L.card : ℝ) - 1 ≤ (m : ℝ) := by
    have := Nat.lt_floor_add_one (c * (L.card : ℝ))
    linarith
  have hm3 : 3 ≤ m := by
    have : (3 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hmn : m ≤ L.card := Nat.floor_le_of_le
    (mul_le_of_le_one_left (Nat.cast_nonneg L.card) hc1)
  have hmean := mean_richCount_fixed_size L 3 m (by omega) hm3 hmn
  have hratio := Incidence.Pruning.choose_three_lower m L.card c hc hcn hmlower
  have hchoose : (0 : ℝ) < (Nat.choose L.card 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (hm3.trans hmn)
  have hmean' : c ^ 3 / 48 * (richCount L 3 : ℝ) ≤
      finiteMean (L.powersetCard m) (fun T => (richCount T 3 : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hchoose).mp
    calc
      _ = (c ^ 3 / 48 * (Nat.choose L.card 3 : ℝ)) * (richCount L 3 : ℝ) := by ring
      _ ≤ (Nat.choose m 3 : ℝ) * (richCount L 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
      _ ≤ _ := hmean
  obtain ⟨T, hT, hbound⟩ := Finset.exists_le_of_le_expect
    (Finset.powersetCard_nonempty.mpr hmn) hmean'
  obtain ⟨hTL, hTcard⟩ := Finset.mem_powersetCard.mp hT
  exact ⟨T, hTL, by simpa only [hTcard] using hmupper, hbound⟩

end ExplicitRIP.Zahl
