/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.OneToOneNorm
import ExplicitRIP.Provider.UnsignedHybridEstimate

/-!
# The unsigned hybrid estimate of [KM, Section 2.3]

Source: [KM, Section 2.3, the claims about Δ_k before Theorem 4; Section 2.2, (6)–(8)].
-/

public section

open scoped Matrix

/-- The claims about `Δ_k` before [KM, Theorem 4]: always `δ_k ≤ Δ_k`, and both the Gershgorin
estimate and the estimate of [KM, Section 2.2] are upper bounds on `Δ_k`. With
`M = Φ^* Φ - I`, `H = |M|` and a threshold `τ`, let the entries of modulus above `τ` form
`A_τ`, and put `B_τ = M - A_τ`. Then `‖H[S]‖_op ≤ ‖M[S]‖_{1→1}` for every support `S`. For
unit-norm columns and `1 ≤ k`, `‖H[S]‖_op ≤ C (log(2k) ‖|A_τ|[S]‖_DR + ‖B_τ[S]‖_{1→1})`
whenever `|S| ≤ k`, for an absolute constant `C`. -/
theorem ExplicitRIP.unsigned_hybrid_estimate :
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
by exact ExplicitRIP.Provider.unsigned_hybrid_estimate
