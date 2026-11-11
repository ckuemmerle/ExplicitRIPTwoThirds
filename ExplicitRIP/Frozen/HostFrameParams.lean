/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.HostGram
import ExplicitRIP.Provider.HostFrameParams

/-!
# [KM, (13)]: the host frame and its parameters

Source: [KM, Section 3, (13), and proof of Theorem 1, (16) and footnote 4].

The asymptotic relations in [KM, (13)] and (16) are taken as `p → ∞` through primes
`p ≡ 3 (mod 4)`.
-/

public section

open scoped Matrix

/-- The host frame of [KM, Section 3, (13)] and the proof of [KM, Theorem 1]. For a prime
`p ≡ 3 (mod 4)`, let `A` be the adjacency matrix of `VO₄⁻(p)`, `m = (p - 1)(p² + 1)`,
`μ = (p² - p + 1)/m`, `ν = 1/(p² + 1)` and `G = I - μA + νĀ = hostGram ℝ p`. The smaller
nontrivial eigenspace of `A`, of eigenvalue `τ = -(p² - p + 1)`, has dimension `m`, and `G`
is `p⁴/m` times the orthogonal projection onto it: `A G = τ G`, `G² = (p⁴/m) G`,
`rank G = m`. The matrix `G` is the Gram matrix of a real unit-norm tight frame
`Φ ∈ ℝ^{m × p⁴}` with `Φᵀ Φ = G` and `Φ Φᵀ = (p⁴/m) I`. As `p → ∞` through primes
`p ≡ 3 (mod 4)`, `m ∼ p³`, `μ ∼ m^{-1/3}` and `ν ∼ m^{-2/3}`, equivalently `μ ∼ 1/p` and
`ν ∼ 1/p²`, as used in [KM, (16)]. -/
theorem ExplicitRIP.host_frame_params :
    (∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      (open Classical in
        (ExplicitRIP.contactGraph p).adjMatrix ℝ * ExplicitRIP.hostGram ℝ p =
          (-((p : ℝ) ^ 2 - p + 1)) • ExplicitRIP.hostGram ℝ p) ∧
      ExplicitRIP.hostGram ℝ p * ExplicitRIP.hostGram ℝ p =
        ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) • ExplicitRIP.hostGram ℝ p ∧
      (ExplicitRIP.hostGram ℝ p).rank = (p - 1) * (p ^ 2 + 1) ∧
      (open Classical in
        Module.finrank ℝ (Module.End.eigenspace
            (Matrix.toLin' ((ExplicitRIP.contactGraph p).adjMatrix ℝ)) (-((p : ℝ) ^ 2 - p + 1))) =
          (p - 1) * (p ^ 2 + 1)) ∧
      ∃ B : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (ZMod p × ZMod p × ZMod p × ZMod p) ℝ,
        Bᵀ * B = ExplicitRIP.hostGram ℝ p ∧ (∀ x, ∑ r, B r x ^ 2 = 1) ∧
        B * Bᵀ = ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) •
          (1 : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (Fin ((p - 1) * (p ^ 2 + 1))) ℝ)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
      let m : ℝ := ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)
      let μ : ℝ := ((p : ℝ) ^ 2 - p + 1) / m
      let ν : ℝ := 1 / ((p : ℝ) ^ 2 + 1)
      |m / (p : ℝ) ^ 3 - 1| ≤ ε ∧
        |μ * m ^ (1 / 3 : ℝ) - 1| ≤ ε ∧ |ν * m ^ (2 / 3 : ℝ) - 1| ≤ ε ∧
        |(p : ℝ) * μ - 1| ≤ ε ∧ |(p : ℝ) ^ 2 * ν - 1| ≤ ε :=
by exact ExplicitRIP.Provider.host_frame_params
