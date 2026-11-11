/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.ContactGraph

/-!
# The host Gram matrix

Source: [KM, proof of Theorem 1, (13), and footnote 4].
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the matrix `G = I - aA + b(J - I - A) = I - μA + νĀ` in the
proof of [KM, Theorem 1], with entries in a field `K` of characteristic zero: `ℚ` for the
exact Cholesky factorization of [KM, footnote 4] and `ℝ` for the frame. Its rational
coefficients are those of [KM, (13)]: `A` is the adjacency matrix of `VO₄⁻(p)`, given by
`ExplicitRIP.contactGraph`, `J` is the all-ones matrix, `a = (p² - p + 1)/m`,
`b = 1/(p² + 1)` and `m = (p - 1)(p² + 1)`. -/
noncomputable def ExplicitRIP.hostGram (K : Type*) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]
    [Fact (p % 4 = 3)] :
    Matrix (ZMod p × ZMod p × ZMod p × ZMod p) (ZMod p × ZMod p × ZMod p × ZMod p) K :=
  open Classical in
  let m : K := ((p : K) - 1) * ((p : K) ^ 2 + 1)
  let a : K := ((p : K) ^ 2 - p + 1) / m
  let b : K := 1 / ((p : K) ^ 2 + 1)
  let A := (ExplicitRIP.contactGraph p).adjMatrix K
  1 - a • A + b • (Matrix.of (fun _ _ => (1 : K)) - 1 - A)
