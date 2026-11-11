/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Provider.WelchBound

/-!
# [KM, (3)]: the Welch bound

Source: [KM, Section 1, (3)].
-/

public section

open scoped Matrix

/-- [KM, (3)]. Any `n ≥ 2` unit vectors in `ℂ^m`, the columns of `Φ`, have coherence
`μ ≥ √((n - m)/(m (n - 1)))`. -/
theorem ExplicitRIP.welch_bound :
    ∀ (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → 2 ≤ n →
      Real.sqrt (((n : ℝ) - m) / ((m : ℝ) * ((n : ℝ) - 1))) ≤ ExplicitRIP.coherence Φ :=
by exact ExplicitRIP.Provider.welch_bound
