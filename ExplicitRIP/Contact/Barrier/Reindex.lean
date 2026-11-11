/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
import ExplicitRIP.Frozen.RIPConstantCharacterization

/-!
# Reindexing the columns of a frame

Column equivalences preserve sparse-vector distortion and hence the restricted isometry
constant. This permits the transport of the host-frame case of [KM, Proposition 10] from
Hermitian coordinates to contact coordinates.
-/

public section

namespace ExplicitRIP.Contact.Barrier

variable {𝕜 m n n' : Type} [RCLike 𝕜]
variable [Fintype m] [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']

theorem ripConstant_submatrix_columns_le (Φ : Matrix m n 𝕜) (e : n' ≃ n) (k : ℕ) :
    ExplicitRIP.ripConstant (Φ.submatrix id e) k ≤ ExplicitRIP.ripConstant Φ k := by
  apply (ExplicitRIP.ripConstant_isLeast (Φ.submatrix id e) k).2
  refine ⟨(ExplicitRIP.ripConstant_isLeast Φ k).1.1, ?_⟩
  intro z hz
  have hs : (Function.support (z ∘ e.symm)).ncard = (Function.support z).ncard := by
    change (e.symm ⁻¹' Function.support z).ncard = (Function.support z).ncard
    exact Set.ncard_preimage_of_injective_subset_range e.symm.injective
      (by rw [e.symm.surjective.range_eq]; exact Set.subset_univ _)
  have h := (ExplicitRIP.ripConstant_isLeast Φ k).1.2 (z ∘ e.symm) (hs.le.trans hz)
  have hsum : (∑ j, ‖(z ∘ e.symm) j‖ ^ 2) = ∑ j, ‖z j‖ ^ 2 :=
    e.symm.sum_comp (fun j : n' => ‖z j‖ ^ 2)
  rw [hsum] at h
  simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_id] using h

/-- Relabeling all columns by an equivalence preserves every RIP constant. -/
theorem ripConstant_submatrix_columns (Φ : Matrix m n 𝕜) (e : n' ≃ n) (k : ℕ) :
    ExplicitRIP.ripConstant (Φ.submatrix id e) k = ExplicitRIP.ripConstant Φ k := by
  apply le_antisymm (ripConstant_submatrix_columns_le Φ e k)
  have h := ripConstant_submatrix_columns_le (Φ.submatrix id e) e.symm k
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Function.id_comp,
    Matrix.submatrix_id_id] using h

end ExplicitRIP.Contact.Barrier
