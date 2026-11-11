/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.ContactGraph
import ExplicitRIP.Provider.HostParameters

/-!
# The strongly regular parameters of the host graph

Source: [KM, Section 3, the parameters of VO₄⁻(p) before (13)].

The asymptotic relations are taken as `p → ∞` through primes `p ≡ 3 (mod 4)`.
-/

public section

open scoped Matrix

/-- For a prime `p ≡ 3 (mod 4)`, the elliptic affine polar graph `VO₄⁻(p)` is strongly regular
with parameters `(v, k, λ, μ') = (p⁴, (p - 1)(p² + 1), p - 2, p(p - 1))`, as stated before
[KM, (13)]. As `p → ∞` through primes `p ≡ 3 (mod 4)`, these are `∼ (p⁴, p³, p, p²)`, and
`λ = o(μ')`. -/
theorem ExplicitRIP.host_parameters :
    (∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      open Classical in
        (ExplicitRIP.contactGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
          (p * (p - 1))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
        |(p : ℝ) ^ 4 / (p : ℝ) ^ 4 - 1| ≤ ε ∧
        |(((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) / (p : ℝ) ^ 3 - 1| ≤ ε ∧
        |((p : ℝ) - 2) / (p : ℝ) - 1| ≤ ε ∧
        |((p : ℝ) * ((p : ℝ) - 1)) / (p : ℝ) ^ 2 - 1| ≤ ε ∧
        |((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) - 1))| ≤ ε :=
by exact ExplicitRIP.Provider.host_parameters
