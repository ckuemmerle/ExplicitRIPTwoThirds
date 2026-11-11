/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The residual matrices of exact LDLᵀ elimination

Source: [KM, proof of Theorem 1, footnote 4].
-/

@[expose] public section

open scoped Matrix

/-- Exact rational symmetric (`LDLᵀ`) elimination of a rational matrix `G` in the order of
`Fin v`, implementing [KM, footnote 4] as a total recursion: `ldlResidual G k` is the
residual after processing the indices `0, …, k - 1`. At index `k` with pivot `d = R(k, k)`,
if `d = 0` the residual is kept; otherwise it is replaced by `R - d⁻¹ R(·, k) R(k, ·)`. For
positive semidefinite `G`, this gives the elimination used for the Cholesky construction;
see `ExplicitRIP.ldl_factorization`. -/
def ExplicitRIP.ldlResidual {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) :
    ℕ → Matrix (Fin v) (Fin v) ℚ
  | 0 => G
  | k + 1 =>
    if h : k < v then
      if ExplicitRIP.ldlResidual G k ⟨k, h⟩ ⟨k, h⟩ = 0 then ExplicitRIP.ldlResidual G k
      else ExplicitRIP.ldlResidual G k -
        (ExplicitRIP.ldlResidual G k ⟨k, h⟩ ⟨k, h⟩)⁻¹ •
          Matrix.of fun i j => ExplicitRIP.ldlResidual G k i ⟨k, h⟩ *
            ExplicitRIP.ldlResidual G k ⟨k, h⟩ j
    else ExplicitRIP.ldlResidual G k
