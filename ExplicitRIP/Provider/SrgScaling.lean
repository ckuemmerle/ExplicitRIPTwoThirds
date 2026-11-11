/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Eigen
public import ExplicitRIP.Analysis.SrgScaling.Scaling

/-!
# Proof of Lemma 5 of [KM]: strongly regular graph scaling laws

Source: [KM, Lemma 5 and Appendix A].

The finite identities and real asymptotics of [KM, Appendix A] prove [KM, Lemma 5]. The graph
and its complement are connected, as assumed in [KM, Section 3], and each projection is onto an
entire eigenspace of the adjacency matrix in the orthogonal complement of the all-ones vector.
-/

public section

open scoped Matrix

/-- Scaling laws for the two angles and common-neighbor parameters of a projected SRG. -/
theorem ExplicitRIP.Provider.srg_scaling :
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
by
  intro V _ _ Γ _ v k l c m θ μ ν ε P hΓ hP hG hm hmv hμ
  have hnonempty : ∀ j, Nonempty (V j) := fun j => (hΓ j).2.1.nonempty
  have hdim : ∀ j, 0 < m j := by
    intro j
    have := hnonempty j
    exact ExplicitRIP.SrgScaling.projection_dimension_pos (Γ j) (P j)
      (v j) (m j) (μ j) (ν j) (ε j) (hG j).1
  have hvpos : ∀ j, 0 < (v j : ℝ) := by
    intro j
    have := hnonempty j
    have hc : 0 < Fintype.card (V j) := Fintype.card_pos
    rw [(hΓ j).1.card] at hc
    exact Nat.cast_pos.mpr hc
  have hnontrivial : ∀ j, Nontrivial (V j) := by
    intro j
    have := hnonempty j
    exact ExplicitRIP.SrgScaling.projection_nontrivial (Γ j) (P j)
      (v j) (m j) (μ j) (ν j) (ε j) (hP j).2.2.2.1 (hG j).1
  have hmom := fun j =>
    @ExplicitRIP.SrgScaling.projection_moments (V j) _ _ (Γ j) _
      (v j) (k j) (l j) (c j) (hnonempty j) (hΓ j).1 (P j) (m j)
      (μ j) (ν j) (ε j) (hP j).2.1 (hP j).2.2.2.1 (hG j).1 (hG j).2.1
  have hparams := fun j =>
    @ExplicitRIP.SrgScaling.eigenvalue_parameters (V j) _ _ (Γ j) _
      (v j) (k j) (l j) (c j) (hnontrivial j) (hΓ j).1 (hΓ j).2.1 (hΓ j).2.2
      (P j) (m j) (θ j) (μ j) (ν j) (ε j) (hP j).2.2.1 (hG j).1 (hG j).2.1
  exact ExplicitRIP.SrgScaling.scaling_laws
    (fun j => (v j : ℝ)) (fun j => (k j : ℝ)) (fun j => (l j : ℝ))
    (fun j => (c j : ℝ)) (fun j => (m j : ℝ)) μ ν ε
    hvpos (fun j => Nat.cast_pos.mpr (hdim j))
    (fun j => (hG j).2.2.1) (fun j => (hG j).2.2.2) (fun j => (hG j).2.1)
    hm hmv hμ
    (fun j => ExplicitRIP.SrgScaling.eliminate_degree (v j) (k j) (m j) (μ j) (ν j)
      (ε j) (hmom j).1 (hmom j).2)
    (fun j => (hmom j).2) (fun j => (hparams j).2.1) (fun j => (hparams j).2.2)
