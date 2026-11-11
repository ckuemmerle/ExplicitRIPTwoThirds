/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.TwoDistanceBarrier.HostTransport
import ExplicitRIP.HermitianForms.Anchors.ConstructionBarrier

/-!
# The host construction barrier in contact coordinates

The barrier for subframes of the host frame follows from the Hermitian-coordinate barrier by
pulling back the selected columns through the sphere map. Column reindexing preserves the Gram
entries and restricted isometry constants. The vanishing-distortion conclusion is the host-frame
case of [KM, Proposition 10]; the result also bounds sparsity when distortion stays bounded.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Actbar.host_construction_barrier :
    ∀ (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
      (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))
        (Φ : ∀ j, Matrix (Fin ((p j - 1) * (p j ^ 2 + 1))) (Γ j) ℝ),
        (∀ᶠ j in Filter.atTop, (Γ j).Nonempty) →
        (∀ j, (Φ j)ᵀ * Φ j = (ExplicitRIP.hostGram ℝ (p j)).submatrix Subtype.val Subtype.val) →
        ∀ k : ℕ → ℕ,
          Filter.Tendsto (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ j).card)
            Filter.atTop (nhds 0) →
          (Filter.Tendsto (fun j => ExplicitRIP.ripConstant (Φ j) (k j)) Filter.atTop (nhds 0) →
              (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (p j : ℝ) ^ 2) ∧
                (fun j => (k j : ℝ)) =o[Filter.atTop]
                  (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ∧
            ((fun j => ExplicitRIP.ripConstant (Φ j) (k j)) =O[Filter.atTop] (fun _ => (1 : ℝ)) →
              (fun j => (k j : ℝ)) =O[Filter.atTop]
                (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ))) := by
  intro p _ _ Γ Φ hΓ hGram k hratio
  classical
  let Γ' := fun j => (Γ j).map (ExplicitRIP.HostCoordinates.sphereMap (p j)).symm.toEmbedding
  let e := fun j => ExplicitRIP.HostCoordinates.columnEquiv (p j) (Γ j)
  let Ψ := fun j => (Φ j).submatrix id (e j)
  have hΓ' : ∀ᶠ j in Filter.atTop, (Γ' j).Nonempty := by
    simpa only [Γ', Finset.map_nonempty] using hΓ
  have hGram' : ∀ j, (Ψ j)ᵀ * Ψ j =
      (ExplicitRIP.hermitianHostGram ℝ (p j)).submatrix Subtype.val Subtype.val := by
    intro j
    ext x y
    change ((Φ j)ᵀ * Φ j) (e j x) (e j y) =
      ExplicitRIP.hermitianHostGram ℝ (p j) x.val y.val
    rw [hGram j]
    exact ExplicitRIP.HostCoordinates.hostGram_sphereMap (p j) ℝ x.val y.val
  have hratio' : Filter.Tendsto
      (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ' j).card)
      Filter.atTop (nhds 0) := by
    simpa only [Γ', Finset.card_map] using hratio
  have h := ExplicitRIP.Hermitian.construction_barrier p Γ' Ψ hΓ' hGram' k hratio'
  have hδ : (fun j => ExplicitRIP.ripConstant (Ψ j) (k j)) =
      (fun j => ExplicitRIP.ripConstant (Φ j) (k j)) :=
    funext fun j => ExplicitRIP.Contact.Barrier.ripConstant_submatrix_columns (Φ j) (e j) (k j)
  simpa only [hδ] using h
