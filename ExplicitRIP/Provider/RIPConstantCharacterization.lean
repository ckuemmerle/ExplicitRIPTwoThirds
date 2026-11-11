/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Analysis.RIPConstant.Sparse

/-!
# The least restricted isometry parameter

Source: [KM, Section 1, the definition of δ_k before (1)].

The principal-Gram norm formula is the least nonnegative sparse-vector distortion. It is the
smallest `δ ≥ 0` for which `(1 - δ) ‖z‖² ≤ ‖Φ z‖² ≤ (1 + δ) ‖z‖²` whenever `|supp z| ≤ k`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.ripConstant_isLeast :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜) (k : ℕ),
      IsLeast {δ : ℝ | 0 ≤ δ ∧ ∀ z : n → 𝕜, (Function.support z).ncard ≤ k →
          (1 - δ) * ∑ j, ‖z j‖ ^ 2 ≤ ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ∧
            ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ≤ (1 + δ) * ∑ j, ‖z j‖ ^ 2}
        (ExplicitRIP.ripConstant Φ k) := by
  intro 𝕜 _ m n _ _ _ Φ k
  classical
  let : Nonempty {S : Finset n // S.card ≤ k} := ⟨⟨∅, by simp⟩⟩
  let f : {S : Finset n // S.card ≤ k} → ℝ := fun S ↦
    ExplicitRIP.opNorm ((Φ.submatrix id (Subtype.val : S.1 → n))ᴴ *
      Φ.submatrix id (Subtype.val : S.1 → n) - 1)
  have hbdd : BddAbove (Set.range f) := Finite.bddAbove_range f
  have hnonneg : 0 ≤ ExplicitRIP.ripConstant Φ k := by
    change 0 ≤ iSup f
    exact le_ciSup_of_le hbdd ⟨∅, by simp⟩ (norm_nonneg _)
  constructor
  · refine ⟨hnonneg, (ExplicitRIP.Ripc.sparse_bounds_iff_principal_opNorm Φ k hnonneg).mpr ?_⟩
    intro S hS
    change f ⟨S, hS⟩ ≤ iSup f
    exact le_ciSup hbdd ⟨S, hS⟩
  · intro δ hδ
    have h := (ExplicitRIP.Ripc.sparse_bounds_iff_principal_opNorm Φ k hδ.1).mp hδ.2
    change iSup f ≤ δ
    exact ciSup_le fun S ↦ h S.val S.property
