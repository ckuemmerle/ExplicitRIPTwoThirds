/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.FixedSize
public import ExplicitRIP.Zahl.Incidence.Sampling.SetCounts

/-! # Survival of bichromatic points in fixed-size samples -/

public section

namespace ExplicitRIP.Zahl

open Classical in
theorem mean_bichromatic_fixed_size {K : Type*} [Field K]
    (R B : Finset (ChartLine K)) (hRB : Disjoint R B)
    (m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ (R ∪ B).card) :
    (Nat.choose m 2 : ℝ) * ((bichromaticPoints R B).ncard : ℝ) ≤
      (Nat.choose (R ∪ B).card 2 : ℝ) *
        finiteMean ((R ∪ B).powersetCard m)
          (fun T => ((bichromaticPoints (T ∩ R) (T ∩ B)).ncard : ℝ)) := by
  classical
  by_cases hP : (bichromaticPoints R B).Finite
  · have hsub (T : Finset (ChartLine K)) :
        bichromaticPoints (T ∩ R) (T ∩ B) ⊆ bichromaticPoints R B := by
      rintro w ⟨⟨r, hr, hwr⟩, ⟨b, hb, hwb⟩⟩
      exact ⟨⟨r, (Finset.mem_inter.mp hr).2, hwr⟩,
        ⟨b, (Finset.mem_inter.mp hb).2, hwb⟩⟩
    have hs := Sampling.mean_ncard_lower ((R ∪ B).powersetCard m)
      (bichromaticPoints R B) hP (fun T => bichromaticPoints (T ∩ R) (T ∩ B))
      (fun T _ => hP.subset (hsub T))
      ((Nat.choose m 2 : ℝ) / (Nat.choose (R ∪ B).card 2 : ℝ)) (by
        rintro w ⟨⟨r, hr, hwr⟩, ⟨b, hb, hwb⟩⟩
        have hrb : r ≠ b := fun h => Finset.disjoint_left.mp hRB hr (h.symm ▸ hb)
        rw [← Sampling.expect_pair_mem_powersetCard (R ∪ B) m hmn r b
          (Finset.mem_union_left _ hr) (Finset.mem_union_right _ hb) hrb]
        apply Finset.expect_le_expect
        intro T _
        by_cases h : r ∈ T ∧ b ∈ T
        · have hw : w ∈ bichromaticPoints (T ∩ R) (T ∩ B) :=
            ⟨⟨r, Finset.mem_inter.mpr ⟨h.1, hr⟩, hwr⟩,
              ⟨b, Finset.mem_inter.mpr ⟨h.2, hb⟩, hwb⟩⟩
          simp only [ite_eq_left h, ite_eq_left hw, le_refl]
        · simp only [ite_eq_right h]
          split_ifs <;> norm_num)
    have hn : (0 : ℝ) < (Nat.choose (R ∪ B).card 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (hm.trans hmn)
    rw [div_mul_eq_mul_div] at hs
    have hs' := (div_le_iff₀ hn).mp hs
    simpa only [finiteMean, mul_comm] using hs'
  · rw [Set.Infinite.ncard hP, Nat.cast_zero, mul_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.expect_nonneg fun _ _ => Nat.cast_nonneg _

end ExplicitRIP.Zahl
