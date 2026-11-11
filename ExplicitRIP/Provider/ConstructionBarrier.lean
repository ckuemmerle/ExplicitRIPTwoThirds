/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.TwoDistanceBarrier.Asymptotics

/-!
# Proof of Proposition 10 of [KM]: the construction barrier

Source: [KM, Proposition 10 and its proof].

Subframes of increasing dimension and unbounded redundancy have the uniform star lower bound
`δ_k ≥ min {μ √(k - 1), 1}`. Here “for all sufficiently large `m`” is read as eventually along
the sequence of subframes. A coherence of order at least the inverse cube root of the dimension
forces vanishing-distortion sparsity `k = o(m^{2/3})`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.construction_barrier :
    ∀ (m N : ℕ → ℕ) (F : ∀ j, Matrix (Fin (m j)) (Fin (N j)) ℝ) (S : ∀ j, Finset (Fin (N j))),
      (∀ j, ExplicitRIP.IsTwoDistanceTightFrame (F j)) →
      (∀ᶠ j in Filter.atTop, (S j).Nonempty) →
      Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun j => (m j : ℝ) / (S j).card) Filter.atTop (nhds 0) →
      (∀ᶠ j in Filter.atTop, ∀ k : ℕ, 1 ≤ k → k ≤ (S j).card →
          min (ExplicitRIP.coherence (F j) * Real.sqrt ((k : ℝ) - 1)) 1 ≤
            ExplicitRIP.ripConstant ((F j).submatrix id (Subtype.val : S j → Fin (N j))) k) ∧
        ((∃ C : ℝ, 0 < C ∧ ∀ᶠ j in Filter.atTop,
            C * (m j : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ExplicitRIP.coherence (F j)) →
          ∀ k : ℕ → ℕ, (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (S j).card) →
            Filter.Tendsto (fun j => ExplicitRIP.ripConstant
                ((F j).submatrix id (Subtype.val : S j → Fin (N j))) (k j)) Filter.atTop (nhds 0) →
            (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ))) := by
  intro m N F S hF _ hm hratio
  have hbar := ExplicitRIP.TwoDistanceBarrier.eventual_barrier m N F S
    (fun j => ExplicitRIP.TwoDistanceBarrier.isWeakTwoDistanceTightFrame_of (hF j)) hm hratio
  refine ⟨hbar, ?_⟩
  rintro ⟨C, hC, hcoh⟩ k hk hδ
  apply ExplicitRIP.TwoDistanceBarrier.sparsity_isLittleO m k
    (fun j => ExplicitRIP.ripConstant
      ((F j).submatrix id (Subtype.val : S j → Fin (N j))) (k j)) C hC hm hδ
  have hsmall := hδ.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbar, hcoh, hk, hsmall] with j hj hμj hkj hδj
  refine ⟨hkj.1, ExplicitRIP.Actbar.rip_nonneg _ _, ?_⟩
  have h := hj (k j) hkj.1 hkj.2
  have hstar : ExplicitRIP.coherence (F j) * Real.sqrt ((k j : ℝ) - 1) ≤
      ExplicitRIP.ripConstant
        ((F j).submatrix id (Subtype.val : S j → Fin (N j))) (k j) := by
    by_contra! hgt
    exact (not_lt_of_ge h) (lt_min hgt hδj)
  exact (mul_le_mul_of_nonneg_right hμj (Real.sqrt_nonneg _)).trans hstar
