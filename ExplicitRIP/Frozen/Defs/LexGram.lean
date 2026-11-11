/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.HostGram
public import ExplicitRIP.Frozen.Defs.LexEquiv

/-!
# The rational Gram matrix in lexicographic vertex order

Source: [KM, proof of Theorem 1, footnote 4].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the rational Gram matrix `G = hostGram ℚ p` of the proof of
[KM, Theorem 1], with rows and columns in the lexicographic order of the vertices
`(x, y, z, r)`, as prescribed in [KM, footnote 4]. -/
noncomputable def ExplicitRIP.lexGram (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    Matrix (Fin (p * (p * (p * p)))) (Fin (p * (p * (p * p)))) ℚ :=
  (ExplicitRIP.hostGram ℚ p).submatrix (ExplicitRIP.lexEquiv p).symm (ExplicitRIP.lexEquiv p).symm
