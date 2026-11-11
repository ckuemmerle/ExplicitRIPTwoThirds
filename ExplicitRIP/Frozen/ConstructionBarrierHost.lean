/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.HostGram
import ExplicitRIP.Provider.ConstructionBarrierHost

/-!
# Proposition 10 of [KM]: the barrier for the host subframes

Source: [KM, Section 5, Proposition 10].
-/

public section

open scoped Matrix

/-- [KM, Proposition 10] applied to the host subframes used in [KM, Theorem 1]. Let
`Φ_j ∈ ℝ^{m_j × Γ_j}` be real subframes of the host frames of `VO₄⁻(p_j)`, for primes
`p_j ≡ 3 (mod 4)`, that is, with Gram matrix `Φ_jᵀ Φ_j = G[Γ_j]` and
`m_j = (p_j - 1)(p_j² + 1)`. If `m_j / |Γ_j| → 0` and `1 ≤ k_j ≤ |Γ_j|` eventually, then
`δ_{k_j}(Φ_j) → 0` requires `k_j = o(m_j^{2/3})`: these matrices do not break the `2/3`
barrier. -/
theorem ExplicitRIP.construction_barrier_host :
    ∀ (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
      (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))
      (Φ : ∀ j, Matrix (Fin ((p j - 1) * (p j ^ 2 + 1))) (Γ j) ℝ) (k : ℕ → ℕ),
      (∀ j, (Φ j)ᵀ * Φ j = (ExplicitRIP.hostGram ℝ (p j)).submatrix Subtype.val Subtype.val) →
      (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (Γ j).card) →
      Filter.Tendsto (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ j).card) Filter.atTop
        (nhds 0) →
      Filter.Tendsto (fun j => ExplicitRIP.ripConstant (Φ j) (k j)) Filter.atTop (nhds 0) →
      (fun j => (k j : ℝ)) =o[Filter.atTop]
        (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :=
by exact ExplicitRIP.Provider.construction_barrier_host
