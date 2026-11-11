/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.HermitianForms.Defs.HermitianGraph

/-!
# The host Gram matrix in Hermitian coordinates

This is the Hermitian-forms model of the host Gram matrix in [KM, proof of Theorem 1], with the
parameters of [KM, (13)]. Reindexing by the sphere map gives the Gram matrix in contact
coordinates. Rational coefficients supply the exact input for [KM, footnote 4], and real
coefficients give the Gram matrix of the host frame.
-/

@[expose] public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the matrix `G = I - aA + b(J - I - A)`, with entries in a field
`K` of characteristic zero (`ℚ` for the exact construction in [KM, footnote 4], `ℝ` for the frame).
Here `A` is the adjacency matrix of the Hermitian forms graph, `J` is the all-ones matrix,
`a = (p² - p + 1)/m`, `b = 1/(p² + 1)` and `m = (p - 1)(p² + 1)`. The coefficients `a` and `b`
are `μ` and `ν` in [KM, (13)]. -/
noncomputable def ExplicitRIP.hermitianHostGram (K : Type*) [Field K] [CharZero K]
    (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    Matrix (ZMod p × ZMod p × ZMod p × ZMod p) (ZMod p × ZMod p × ZMod p × ZMod p) K :=
  open Classical in
  let m : K := ((p : K) - 1) * ((p : K) ^ 2 + 1)
  let a : K := ((p : K) ^ 2 - p + 1) / m
  let b : K := 1 / ((p : K) ^ 2 + 1)
  let A := (ExplicitRIP.hermitianGraph p).adjMatrix K
  1 - a • A + b • (Matrix.of (fun _ _ => (1 : K)) - 1 - A)

/-- The Hermitian host Gram matrix has unit diagonal. -/
theorem ExplicitRIP.HostFrame.hostGram_apply_self (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (i : ZMod p × ZMod p × ZMod p × ZMod p) : hermitianHostGram ℝ p i i = 1 := by
  classical
  simp [hermitianHostGram]
