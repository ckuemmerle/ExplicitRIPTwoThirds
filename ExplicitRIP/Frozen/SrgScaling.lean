/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
import ExplicitRIP.Provider.SrgScaling

/-!
# Lemma 5 of [KM]: strongly regular graph scaling laws

Source: [KM, Lemma 5, Section 3, and Appendix A].

[KM, Lemma 5] is read with the standing assumption in [KM, Section 3] that the graph and its
complement are connected. The projection is onto an entire eigenspace of the adjacency matrix
restricted to the orthogonal complement of the all-ones vector.
-/

public section

open scoped Matrix

/-- [KM, Lemma 5]. Consider a sequence of strongly regular graphs `Γ_j` with parameters
`(v_j, k_j, λ_j, μ'_j)`, written `(v, k, l, c)` in Lean using Mathlib's `IsSRGWith`, each
connected with connected complement, as assumed in [KM, Section 3]. For each `j`, let `P_j`
be the orthogonal projection onto the entire eigenspace `E_j = {x ⊥ 𝟙 : A_j x = θ_j x}` of
the adjacency matrix `A_j` in `𝟙^⊥`, one of the two nontrivial eigenspaces described in
[KM, Section 3], with `m_j = dim E_j = rank P_j`. Suppose
`G_j := (v_j/m_j) P_j = I + ε_j (μ_j A_j - ν_j Ā_j)` with `ε_j ∈ {±1}` and `μ_j > ν_j > 0`,
where `Ā_j` is the adjacency matrix of the complement. If `m → ∞`, `m = o(v)` and
`μ ≍ m^{-1/3}`, then `ν ≍ m^{-2/3}`, `k/v ∼ ν/μ ∼ 1/(mμ²) ≍ m^{-1/3}`, `μ' ∼ k²/v` and
`λ/μ' = 1 + ε m μ³ + o(1)`. In particular, `λ = o(μ')` if and only if `ε = -1` eventually
and `μ ∼ m^{-1/3}`, in which case `ν ∼ m^{-2/3}`. -/
theorem ExplicitRIP.srg_scaling :
    ∀ (V : ℕ → Type) [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
      (Γ : ∀ j, SimpleGraph (V j)) [∀ j, DecidableRel (Γ j).Adj]
      (v k l c m : ℕ → ℕ) (θ μ ν ε : ℕ → ℝ) (P : ∀ j, Matrix (V j) (V j) ℝ),
      (∀ j, (Γ j).IsSRGWith (v j) (k j) (l j) (c j) ∧ (Γ j).Connected ∧ (Γ j)ᶜ.Connected) →
      (∀ j, (P j)ᵀ = P j ∧ P j * P j = P j ∧
        (Γ j).adjMatrix ℝ * P j = θ j • P j ∧ P j *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
        (∀ x : V j → ℝ, (Γ j).adjMatrix ℝ *ᵥ x = θ j • x → ∑ i, x i = 0 → P j *ᵥ x = x) ∧
        (P j).rank = m j) →
      (∀ j, ((v j : ℝ) / m j) • P j =
          1 + ε j • (μ j • (Γ j).adjMatrix ℝ - ν j • (Γ j)ᶜ.adjMatrix ℝ) ∧
        (ε j = 1 ∨ ε j = -1) ∧ 0 < ν j ∧ ν j < μ j) →
      Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
      (fun j => (m j : ℝ)) =o[Filter.atTop] (fun j => (v j : ℝ)) →
      μ =Θ[Filter.atTop] (fun j => (m j : ℝ) ^ (-(1 / 3 : ℝ))) →
      ν =Θ[Filter.atTop] (fun j => (m j : ℝ) ^ (-(2 / 3 : ℝ))) ∧
        Asymptotics.IsEquivalent Filter.atTop (fun j => (k j : ℝ) / v j) (fun j => ν j / μ j) ∧
        Asymptotics.IsEquivalent Filter.atTop (fun j => ν j / μ j)
          (fun j => 1 / ((m j : ℝ) * μ j ^ 2)) ∧
        (fun j => 1 / ((m j : ℝ) * μ j ^ 2)) =Θ[Filter.atTop]
          (fun j => (m j : ℝ) ^ (-(1 / 3 : ℝ))) ∧
        Asymptotics.IsEquivalent Filter.atTop (fun j => (c j : ℝ)) (fun j => (k j : ℝ) ^ 2 / v j) ∧
        Filter.Tendsto (fun j => (l j : ℝ) / c j - (1 + ε j * m j * μ j ^ 3)) Filter.atTop
          (nhds 0) ∧
        ((fun j => (l j : ℝ)) =o[Filter.atTop] (fun j => (c j : ℝ)) ↔
          (∀ᶠ j in Filter.atTop, ε j = -1) ∧
            Asymptotics.IsEquivalent Filter.atTop μ (fun j => (m j : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
        ((fun j => (l j : ℝ)) =o[Filter.atTop] (fun j => (c j : ℝ)) →
          Asymptotics.IsEquivalent Filter.atTop ν (fun j => (m j : ℝ) ^ (-(2 / 3 : ℝ)))) :=
by exact ExplicitRIP.Provider.srg_scaling
