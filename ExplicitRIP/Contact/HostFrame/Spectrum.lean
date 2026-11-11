/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame.Algebra

/-!
# The least adjacency eigenspace of the contact graph

Nonregular eigenvectors are killed by the all-ones matrix. The SRG quadratic then gives the two
remaining eigenvalues. The Gram polynomial acts by its nonzero scale on the lower eigenspace,
which is therefore exactly its range. This realizes the smaller nontrivial eigenspace used in
[KM, Section 3, (13)].
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace ExplicitRIP.Contact.HostFrame

/-- A left regularity identity kills every eigenvector at a different eigenvalue. -/
theorem mulVec_eq_zero_of_eigenvalue_ne {V : Type*} [Fintype V]
    (A J : Matrix V V ℝ) {k μ : ℝ} (hJA : J * A = k • J)
    {v : V → ℝ} (hv : A *ᵥ v = μ • v) (hμ : μ ≠ k) : J *ᵥ v = 0 := by
  have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ v) hJA
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, Matrix.smul_mulVec] at h
  have hz : (μ - k) • (J *ᵥ v) = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hμ)

/-- The SRG quadratic has exactly the two nonregular roots. -/
theorem eigenvalue_eq_one_of_three {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℝ) (x : ℝ)
    (hAA : A * A = ((x - 1) * (x ^ 2 + 1)) • (1 : Matrix V V ℝ) +
      (x - 2) • A + (x * (x - 1)) • (J - 1 - A))
    (hJA : J * A = ((x - 1) * (x ^ 2 + 1)) • J)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    μ = (x - 1) * (x ^ 2 + 1) ∨ μ = x - 1 ∨ μ = -(x ^ 2 - x + 1) := by
  by_cases hk : μ = (x - 1) * (x ^ 2 + 1)
  · exact Or.inl hk
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hav : A *ᵥ v = μ • v := hv.apply_eq_smul
  have hjv := mulVec_eq_zero_of_eigenvalue_ne A J hJA hav hk
  have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ v) hAA
  simp only [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hav, hjv, Matrix.mulVec_smul] at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv.2
  have he := congrFun h i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul] at he
  have hprod : ((μ - (x - 1)) * (μ + (x ^ 2 - x + 1))) * v i = 0 := by
    linear_combination he
  have hroot := (mul_eq_zero.mp hprod).resolve_right hi
  rcases mul_eq_zero.mp hroot with hr | ht
  · exact Or.inr (Or.inl (sub_eq_zero.mp hr))
  · exact Or.inr (Or.inr (by linarith only [ht]))

/-- The range of the Gram polynomial is exactly the lower adjacency eigenspace. -/
theorem eigenspace_eq_range_of_polynomial {V : Type*} [Fintype V] [DecidableEq V]
    (A J G : Matrix V V ℝ) (x : ℝ) (hx : 1 < x)
    (hJA : J * A = ((x - 1) * (x ^ 2 + 1)) • J)
    (hG : G = (x ^ 2 / ((x - 1) * (x ^ 2 + 1))) •
      ((x - 1) • (1 : Matrix V V ℝ) - A) +
      ((x - 1) / ((x - 1) * (x ^ 2 + 1))) • J)
    (hAG : A * G = (-(x ^ 2 - x + 1)) • G) :
    Module.End.eigenspace (Matrix.toLin' A) (-(x ^ 2 - x + 1)) =
      LinearMap.range G.mulVecLin := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxm : 0 < x - 1 := sub_pos.mpr hx
  have hx1 : x - 1 ≠ 0 := by linarith only [hx]
  have hxq : x ^ 2 + 1 ≠ 0 := by positivity
  have hc : x ^ 4 / ((x - 1) * (x ^ 2 + 1)) ≠ 0 := by positivity
  have ht : -(x ^ 2 - x + 1) ≠ (x - 1) * (x ^ 2 + 1) := by
    have hk : 0 < (x - 1) * (x ^ 2 + 1) := by positivity
    have hs : 0 < x ^ 2 - x + 1 := by nlinarith only [hx, sq_nonneg (x - 1)]
    linarith only [hk, hs]
  ext v
  constructor
  · intro hv
    have hav : A *ᵥ v = (-(x ^ 2 - x + 1)) • v :=
      Module.End.mem_eigenspace_iff.mp hv
    have hjv := mulVec_eq_zero_of_eigenvalue_ne A J hJA hav ht
    have hgv : G *ᵥ v = (x ^ 4 / ((x - 1) * (x ^ 2 + 1))) • v := by
      rw [hG, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hav, Matrix.smul_mulVec, hjv, smul_zero,
        add_zero]
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    refine ⟨(x ^ 4 / ((x - 1) * (x ^ 2 + 1)))⁻¹ • v, ?_⟩
    change G *ᵥ ((x ^ 4 / ((x - 1) * (x ^ 2 + 1)))⁻¹ • v) = v
    rw [Matrix.mulVec_smul, hgv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨v, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change A *ᵥ (G *ᵥ v) = (-(x ^ 2 - x + 1)) • (G *ᵥ v)
    rw [Matrix.mulVec_mulVec, hAG, Matrix.smul_mulVec]

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

open Classical in
theorem eigenspace_eq_range :
    Module.End.eigenspace (Matrix.toLin' ((contactGraph p).adjMatrix ℝ))
        (-((p : ℝ) ^ 2 - p + 1)) =
      LinearMap.range (hostGram ℝ p).mulVecLin :=
  eigenspace_eq_range_of_polynomial _ _ _ (p : ℝ)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt) (ones_mul_adj p)
    (hostGram_eq_polynomial p) (adj_mul_hostGram p)

open Classical in
theorem eigenspace_finrank :
    Module.finrank ℝ (Module.End.eigenspace
      (Matrix.toLin' ((contactGraph p).adjMatrix ℝ)) (-((p : ℝ) ^ 2 - p + 1))) =
      (p - 1) * (p ^ 2 + 1) := by
  rw [eigenspace_eq_range]
  exact hostGram_rank p

open Classical in
theorem hasEigenvalue :
    Module.End.HasEigenvalue (Matrix.toLin' ((contactGraph p).adjMatrix ℝ))
      (-((p : ℝ) ^ 2 - p + 1)) := by
  apply Module.End.hasEigenvalue_iff.mpr
  intro h
  have hd := eigenspace_finrank p
  rw [h, finrank_bot] at hd
  exact (dimension_pos p).ne' hd.symm

open Classical in
theorem least_eigenvalue {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' ((contactGraph p).adjMatrix ℝ)) μ) :
    -((p : ℝ) ^ 2 - p + 1) ≤ μ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs : 0 < (p : ℝ) ^ 2 - p + 1 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  rcases eigenvalue_eq_one_of_three _ _ (p : ℝ) (adj_mul_adj p) (ones_mul_adj p) hμ
    with hk | hr | ht
  · rw [hk]
    have hpos : 0 < ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) := by positivity
    linarith only [hs, hpos]
  · rw [hr]
    linarith only [hp, hs]
  · exact ht.ge

end ExplicitRIP.Contact.HostFrame
