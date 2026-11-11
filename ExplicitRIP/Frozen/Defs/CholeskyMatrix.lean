/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.SelectedVertices
public import ExplicitRIP.Frozen.Defs.LexGram
public import ExplicitRIP.Frozen.Defs.LDLPivots
public import ExplicitRIP.Frozen.Defs.LDLFactor

/-!
# The selected Cholesky frame

Source: [KM, proof of Theorem 1, footnotes 4 and 5].

`ExplicitRIP.choleskyMatrix` realizes the Cholesky construction of [KM, footnote 4] by exact
rational LDLᵀ elimination followed by positive real square roots. The vertices are ordered
lexicographically and rows corresponding to zero pivots are omitted.
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)` and `T ⊆ 𝔽_p`, the explicit real matrix `Φ_T` in the proof of
[KM, Theorem 1]: the frame `Φ ∈ ℝ^{m × p⁴}` obtained from `G = I - μA + νĀ` by Cholesky
factorization, retaining the columns indexed by `V'_T = selectedVertices p T`. As in
[KM, footnote 4], the vertices are ordered lexicographically and the zero rows corresponding
to zero pivots are deleted: `Φ = ldlFactor (lexGram p)`, with one row per nonzero pivot. -/
noncomputable def ExplicitRIP.choleskyMatrix (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) :
    Matrix (Fin (ExplicitRIP.ldlPivots (ExplicitRIP.lexGram p)).length)
      (ExplicitRIP.selectedVertices p T) ℝ :=
  fun r x => ExplicitRIP.ldlFactor (ExplicitRIP.lexGram p) r (ExplicitRIP.lexEquiv p x.1)
