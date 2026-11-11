/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedHybrid.AnyThreshold

/-!
# The unsigned hybrid estimate for every real threshold

Source: [KM, Section 2.3, the claims about Δ_k before Theorem 4; Section 2.2, (6)–(8)].

Unsigned domination `δ_k ≤ Δ_k` and the Gershgorin comparison accompany the uniform threshold
estimate. For unit-norm columns and `|S| ≤ k`, the large-entry part is bounded by its absolute
discrete Rayleigh norm times `log(2k)`, and the small-entry part by its induced `1`-norm, with
an absolute constant.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.unsigned_hybrid_estimate :
    (∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
        (Φ : Matrix m n 𝕜) (k : ℕ),
        ExplicitRIP.ripConstant Φ k ≤ ExplicitRIP.unsignedRIPConstant Φ k) ∧
      (∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
        (Φ : Matrix m n 𝕜) (S : Finset n),
        ExplicitRIP.opNorm (((Φᴴ * Φ - 1).map fun z => ‖z‖).submatrix (Subtype.val : S → n)
            (Subtype.val : S → n)) ≤
          ExplicitRIP.oneToOneNorm ((Φᴴ * Φ - 1).submatrix (Subtype.val : S → n)
            (Subtype.val : S → n))) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n]
        [DecidableEq n] (Φ : Matrix m n 𝕜), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
        ∀ τ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ S : Finset n, S.card ≤ k →
          let M : Matrix n n 𝕜 := Φᴴ * Φ - 1
          let A : Matrix n n 𝕜 := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
          let B : Matrix n n 𝕜 := M - A
          ExplicitRIP.opNorm ((M.map fun z => ‖z‖).submatrix (Subtype.val : S → n)
              (Subtype.val : S → n)) ≤
            C * (Real.log (2 * k) * ExplicitRIP.drNorm
                ((A.map fun z => ‖z‖).submatrix (Subtype.val : S → n) (Subtype.val : S → n)) +
              ExplicitRIP.oneToOneNorm (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n))) :=
by
  refine ⟨?_, ?_, ?_⟩
  · intro 𝕜 _ m n _ _ _ Φ k
    exact ExplicitRIP.UnsignedHybrid.ripConstant_le_unsignedRIPConstant Φ k
  · intro 𝕜 _ m n _ _ _ Φ S
    rw [Matrix.submatrix_map]
    apply ExplicitRIP.UnsignedHybrid.opNorm_map_norm_le_oneToOneNorm
    intro i j
    exact ExplicitRIP.UnsignedHybrid.norm_gram_error_symm Φ i j
  · obtain ⟨C, hC, h⟩ := ExplicitRIP.UnsignedHybrid.abs_split_bound
    refine ⟨C, hC, ?_⟩
    intro 𝕜 _ m n _ _ _ Φ _hΦ τ k hk S hS
    exact h (Φᴴ * Φ - 1) (ExplicitRIP.UnsignedHybrid.norm_gram_error_symm Φ) τ k hk S hS
