/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.ConstructionBarrier.Host

/-!
# Proposition 10 of [KM] for the host subframes

Source: [KM, Section 5, Proposition 10].

Vanishing restricted isometry constants for the host subframes force sparsity `k = o(m^{2/3})`,
where `m` is the row count and the row-to-column ratio tends to zero.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.construction_barrier_host :
    ∀ (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
      (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))
      (Φ : ∀ j, Matrix (Fin ((p j - 1) * (p j ^ 2 + 1))) (Γ j) ℝ) (k : ℕ → ℕ),
      (∀ j, (Φ j)ᵀ * Φ j = (ExplicitRIP.hostGram ℝ (p j)).submatrix Subtype.val Subtype.val) →
      (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (Γ j).card) →
      Filter.Tendsto (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ j).card) Filter.atTop
        (nhds 0) →
      Filter.Tendsto (fun j => ExplicitRIP.ripConstant (Φ j) (k j)) Filter.atTop (nhds 0) →
      (fun j => (k j : ℝ)) =o[Filter.atTop]
        (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
  intro p _ _ Γ Φ k hGram hk hratio hδ
  have hΓ : ∀ᶠ j in Filter.atTop, (Γ j).Nonempty := by
    filter_upwards [hk] with j hj
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < k j) hj.2)
  exact ((ExplicitRIP.Actbar.host_construction_barrier p Γ Φ hΓ hGram k hratio).1 hδ).2
