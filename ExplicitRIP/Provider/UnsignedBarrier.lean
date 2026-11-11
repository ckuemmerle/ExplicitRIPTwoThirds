/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedBarrier.AllSparsity

/-!
# Proof of Theorem 4 of [KM]: the unsigned barrier

Source: [KM, Theorem 4, (10)].

The finite inequality of [KM, Theorem 4] holds for every `k ≥ 1`
(`AllSparsity.unsigned_barrier_finite`), in particular under the hypotheses `2 ≤ k ≤ m ≤ n` of
the theorem. Its asymptotic consequence bounds `k - 1` (`AllSparsity.unsigned_barrier_littleO`);
with `m → ∞` this gives `k = o(m^{2/3})`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.unsigned_barrier :
    (∀ (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
      ∀ k : ℕ, 2 ≤ k → k ≤ m → m ≤ n →
        ((n : ℝ) - m) * ((k : ℝ) - 1) ^ (3 / 2 : ℝ) /
            ((m : ℝ) * ((n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ))) ≤
          ExplicitRIP.unsignedRIPConstant Φ k ^ 2) ∧
      ∀ (m n k : ℕ → ℕ) (Φ : ∀ j, Matrix (Fin (m j)) (Fin (n j)) ℂ),
        (∀ᶠ j in Filter.atTop,
          (∀ c, ∑ i, ‖Φ j i c‖ ^ 2 = 1) ∧ 2 ≤ k j ∧ k j ≤ m j ∧ m j ≤ n j) →
        Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (m j : ℝ) / n j) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun j => ExplicitRIP.unsignedRIPConstant (Φ j) (k j)) Filter.atTop
          (nhds 0) →
        (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) := by
  refine ⟨fun m n Φ hΦ k hk _ _ =>
    ExplicitRIP.AllSparsity.unsigned_barrier_finite m n Φ hΦ k (by omega), ?_⟩
  intro m n k Φ hev hm hmn hΔ
  have hold := ExplicitRIP.AllSparsity.unsigned_barrier_littleO m n k Φ
    (hev.mono fun j hj => ⟨hj.1, by omega, by omega⟩) hmn hΔ
  have hpow : Filter.Tendsto (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hm
  have hone : (fun _ : ℕ => (1 : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) :=
    Asymptotics.isLittleO_const_left.2 (Or.inr
      (Filter.tendsto_abs_atTop_atTop.comp hpow |>.congr' (by
        filter_upwards with j; simp [Real.norm_eq_abs])))
  simpa using hold.add hone
