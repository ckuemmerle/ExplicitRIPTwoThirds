/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.OneToOneNorm
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Hermitian operator norm bounded by the maximal column sum

Unitary diagonalization identifies the Euclidean operator norm with the largest eigenvalue
modulus. Gershgorin bounds each modulus by a row sum, and Hermitian symmetry identifies that row
sum with a column sum.

Source: [KM, Section 2.1].
-/

public section

open scoped Matrix Matrix.Norms.L2Operator

namespace ExplicitRIP.Gersh

variable {q : Type*} {M : Matrix q q ℂ}

/-- Transposed entries of a Hermitian matrix have equal moduli. -/
theorem norm_apply_eq_norm_transpose (hM : M.IsHermitian) (i j : q) :
    ‖M i j‖ = ‖M j i‖ := by
  rw [← hM.apply i j, norm_star]

variable [Fintype q]

/-- The maximal column sum is nonnegative, also for an empty index type. -/
theorem oneToOneNorm_nonneg (M : Matrix q q ℂ) : 0 ≤ ExplicitRIP.oneToOneNorm M := by
  exact Real.iSup_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Every absolute column sum is at most their maximum. -/
theorem column_sum_le_oneToOneNorm (M : Matrix q q ℂ) (j : q) :
    ∑ i, ‖M i j‖ ≤ ExplicitRIP.oneToOneNorm M := by
  exact le_ciSup (Finite.bddAbove_range (fun j : q ↦ ∑ i : q, ‖M i j‖)) j

variable [DecidableEq q]

/-- Unitary diagonalization expresses the Euclidean operator norm through eigenvalues. -/
theorem opNorm_eq_norm_eigenvalues {𝕜 : Type*} [RCLike 𝕜]
    {M : Matrix q q 𝕜} (hM : M.IsHermitian) :
    ExplicitRIP.opNorm M = ‖fun i ↦ (RCLike.ofReal (hM.eigenvalues i) : 𝕜)‖ := by
  change ‖M‖ = _
  conv_lhs => rw [hM.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal, Function.comp_def]

/-- Gershgorin and Hermitian symmetry bound every eigenvalue by the maximal column sum. -/
theorem norm_eigenvalue_le_oneToOneNorm (hM : M.IsHermitian) (i : q) :
    ‖(hM.eigenvalues i : ℂ)‖ ≤ ExplicitRIP.oneToOneNorm M := by
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M) (hM.eigenvalues i : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin', hM.spectrum_eq_image_range]
    exact Set.mem_image_of_mem _ (Set.mem_range_self i)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball heig
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  calc
    ‖(hM.eigenvalues i : ℂ)‖ = ‖((hM.eigenvalues i : ℂ) - M k k) + M k k‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(hM.eigenvalues i : ℂ) - M k k‖ + ‖M k k‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.univ.erase k, ‖M k j‖) + ‖M k k‖ := add_le_add hk le_rfl
    _ = ∑ j, ‖M k j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ k)
    _ = ∑ j, ‖M j k‖ := Finset.sum_congr rfl fun j _ ↦ norm_apply_eq_norm_transpose hM k j
    _ ≤ ExplicitRIP.oneToOneNorm M := column_sum_le_oneToOneNorm M k

/-- The Euclidean operator norm of a Hermitian matrix is at most its maximal column sum. -/
theorem opNorm_le_oneToOneNorm_of_isHermitian (hM : M.IsHermitian) :
    ExplicitRIP.opNorm M ≤ ExplicitRIP.oneToOneNorm M := by
  rw [opNorm_eq_norm_eigenvalues hM]
  exact (pi_norm_le_iff_of_nonneg (oneToOneNorm_nonneg M)).2
    (norm_eigenvalue_le_oneToOneNorm hM)

end ExplicitRIP.Gersh
