/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.CholeskyMatrix
import ExplicitRIP.Provider.MainTheorem

/-!
# Theorem 1 of [KM]: an explicit restricted isometry family

Source: [KM, Theorem 1 and its proof, (16), and footnotes 4 and 5].

The limits are taken through primes `p ≡ 3 (mod 4)`. The exponent `k = m^{2/3-o(1)}` is
expressed by `k ≤ m^{2/3}` and `log k / log m → 2/3`.
-/

public section

open scoped Matrix

/-- [KM, Theorem 1], for the matrices `Φ_T = choleskyMatrix p T` of its proof. For primes
`p ≡ 3 (mod 4)` take `L = ⌊log p⌋`, `T = {0, …, L - 1}` and `k = ⌊p² / (log p)⁶⌋`. There are
infinitely many such primes, and for all sufficiently large ones `Φ_T`, with `m` rows and `n`
columns, has unit-norm columns and `k ≤ m^{2/3}`. Along these primes `m, n → ∞`, `m / n → 0`,
`δ_k → 0` and `log k / log m → 2/3`, so eventually `k = m^{2/3 - ε_p}` with `0 ≤ ε_p → 0`. -/
theorem ExplicitRIP.main_theorem :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
        let L := ⌊Real.log p⌋₊
        let T : Finset (ZMod p) := (Finset.range L).image fun t : ℕ => (t : ZMod p)
        let k := ⌊(p : ℝ) ^ 2 / Real.log p ^ 6⌋₊
        let m := (ExplicitRIP.ldlPivots (ExplicitRIP.lexGram p)).length
        let n := (ExplicitRIP.selectedVertices p T).card
        (∀ x, ∑ r, ExplicitRIP.choleskyMatrix p T r x ^ 2 = 1) ∧
          1 / ε ≤ (n : ℝ) ∧ 1 / ε ≤ (m : ℝ) ∧ (m : ℝ) / n ≤ ε ∧
          ExplicitRIP.ripConstant (ExplicitRIP.choleskyMatrix p T) k ≤ ε ∧
          (k : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) ∧ |Real.log k / Real.log m - 2 / 3| ≤ ε :=
by exact ExplicitRIP.Provider.main_theorem
