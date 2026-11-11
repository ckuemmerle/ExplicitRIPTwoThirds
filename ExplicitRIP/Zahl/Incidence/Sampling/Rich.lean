/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Blocks
public import ExplicitRIP.Zahl.Incidence.Counting.Finite
public import ExplicitRIP.Zahl.Incidence.Sampling.SetCounts

/-! # Survival of rich points under uniform coloring -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
theorem mean_three_rich_of_k_rich {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (k : ℕ) (hk : 3 ≤ k) :
    (richCount L k : ℝ) / 1000 ≤
      finiteMean (Finset.univ : Finset (↥L → Fin k))
        (fun χ => (richCount (colorSample L χ) 3 : ℝ)) := by
  classical
  let : DecidableEq (ChartLine K) := Classical.decEq _
  have hk0 : 0 < k := by omega
  let : NeZero k := ⟨hk0.ne'⟩
  have hsurvive (w : Point K) (hw : w ∈ richPoints L k) :
      (1 / 1000 : ℝ) ≤ Finset.expect (Finset.univ : Finset (↥L → Fin k))
        (fun χ => if w ∈ richPoints (colorSample L χ) 3 then (1 : ℝ) else 0) := by
    let W := L.filter (fun l => w ∈ linePoints l)
    have hW : k ≤ W.card := hw
    obtain ⟨blocks, hb, hd⟩ := Sampling.exists_three_blocks W (k / 3) (by omega)
    have hbL (i : Fin 3) : blocks i ⊆ L := (hb i).1.trans (Finset.filter_subset _ _)
    have hincident (i : Fin 3) (l : ChartLine K) (hl : l ∈ blocks i) :
        w ∈ linePoints l := (Finset.mem_filter.mp ((hb i).1 hl)).2
    let f (i : Fin 3) (χ : ↥L → Fin k) : ℝ :=
      if (colorSample L χ ∩ blocks i).Nonempty then 1 else 0
    have hprob (i : Fin 3) : (1 / 10 : ℝ) ≤ Finset.expect Finset.univ (f i) := by
      have hlow := mean_nonempty_color_block_lower L (blocks i) (hbL i) k hk0
      rw [(hb i).2] at hlow
      have hlow' : ((k / 3 : ℕ) : ℝ) / (k : ℝ) -
          ((k / 3 : ℕ) : ℝ) * (((k / 3 : ℕ) : ℝ) - 1) / (2 * (k : ℝ) ^ 2) ≤
            Finset.expect Finset.univ (f i) := by
        simpa only [finiteMean, f, Sampling.expect_univ_canonical] using hlow
      exact (Sampling.block_probability_lower (k / 3) k hk0 (by omega) (by omega)).trans hlow'
    calc
      (1 / 1000 : ℝ) = ∏ _i : Fin 3, (1 / 10 : ℝ) := by norm_num
      _ ≤ ∏ i : Fin 3, Finset.expect Finset.univ (f i) := by
        exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hprob i)
      _ = Finset.expect Finset.univ (fun χ => ∏ i : Fin 3, f i χ) :=
        by simpa only [finiteMean, f, Sampling.expect_univ_canonical] using
          (mean_disjoint_color_blocks L blocks hbL hd k hk0).symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro χ _
        by_cases hne : ∀ i, (colorSample L χ ∩ blocks i).Nonempty
        · have hw3 := Sampling.three_blocks_rich (colorSample L χ) w blocks hincident hd hne
          simp only [f, ite_eq_left (hne _), Finset.prod_const_one, ite_eq_left hw3, le_refl]
        · obtain ⟨i, hi⟩ := not_forall.mp hne
          have hz : ∏ j : Fin 3, f j χ = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [f, ite_eq_right hi])
          rw [hz]
          split_ifs <;> norm_num
  have h := Sampling.mean_ncard_lower (Finset.univ : Finset (↥L → Fin k))
    (richPoints L k) (richPoints_finite L k (by omega))
    (fun χ => richPoints (colorSample L χ) 3)
    (fun χ _ => richPoints_finite (colorSample L χ) 3 (by decide))
    (1 / 1000) hsurvive
  simpa only [finiteMean, richCount, div_eq_mul_inv, one_mul, mul_comm,
    Sampling.expect_univ_canonical] using h

end ExplicitRIP.Zahl
