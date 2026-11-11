/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
import ExplicitRIP.Provider.UnsignedBarrier

/-!
# Theorem 4 of [KM]: the limit of phase agnosticism

Source: [KM, Theorem 4, (10)].

The asymptotic conclusion is stated along sequences that eventually satisfy the finite
hypotheses `2 ≤ k ≤ m ≤ n` and have unit-norm columns.
-/

public section

open scoped Matrix

/-- [KM, Theorem 4]. If `Φ ∈ ℂ^{m×n}` has unit-norm columns and `2 ≤ k ≤ m ≤ n`, then
`Δ_k² ≥ (n - m)(k - 1)^{3/2} / (m (n - 1 + (k - 1)^{3/2}))`. In particular, along any
sequence that eventually satisfies these hypotheses, if `m → ∞` and `m/n → 0`, then
`Δ_k → 0` requires `k = o(m^{2/3})`. -/
theorem ExplicitRIP.unsigned_barrier :
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
        (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) :=
by exact ExplicitRIP.Provider.unsigned_barrier
