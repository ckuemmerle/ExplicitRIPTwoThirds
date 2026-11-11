/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.ConstructionBarrier.Asymptotics

/-!
# The construction barrier in Hermitian coordinates

For subframes of the Hermitian-forms model of the host frame with vanishing row-to-column ratio,
bounded restricted isometry forces sparsity of order at most `m^(2/3)`, and vanishing distortion
forces little-o growth. The sphere map transports this result to the contact coordinates
(`ExplicitRIP.Analysis.ConstructionBarrier.Host`), where it yields
`ExplicitRIP.construction_barrier_host`.

The vanishing-distortion conclusion is the host-frame case of [KM, Proposition 10], with the
parameters of [KM, (13)]. The result also bounds sparsity when distortion stays bounded.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Hermitian.construction_barrier :
    ∀ (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
      (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))
        (Φ : ∀ j, Matrix (Fin ((p j - 1) * (p j ^ 2 + 1))) (Γ j) ℝ),
        (∀ᶠ j in Filter.atTop, (Γ j).Nonempty) →
        (∀ j, (Φ j)ᵀ * Φ j =
          (ExplicitRIP.hermitianHostGram ℝ (p j)).submatrix Subtype.val Subtype.val) →
        ∀ k : ℕ → ℕ,
          Filter.Tendsto (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ j).card)
            Filter.atTop (nhds 0) →
          (Filter.Tendsto (fun j => ExplicitRIP.ripConstant (Φ j) (k j)) Filter.atTop (nhds 0) →
              (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (p j : ℝ) ^ 2) ∧
                (fun j => (k j : ℝ)) =o[Filter.atTop]
                  (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ∧
            ((fun j => ExplicitRIP.ripConstant (Φ j) (k j)) =O[Filter.atTop] (fun _ => (1 : ℝ)) →
              (fun j => (k j : ℝ)) =O[Filter.atTop]
                (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ))) :=
by
  intro p _ _ Γ Φ hΓ hGram k hratio
  have hscale := ExplicitRIP.Actbar.parameter_sq_isBigO_rows p
  constructor
  · intro hδ
    have h := ExplicitRIP.Actbar.sparsity_isLittleO_sq p Γ Φ hΓ hGram k hratio hδ
    exact ⟨h, h.trans_isBigO hscale⟩
  · intro hδ
    exact (ExplicitRIP.Actbar.sparsity_isBigO_sq p Γ Φ hΓ hGram k hratio hδ).trans hscale
