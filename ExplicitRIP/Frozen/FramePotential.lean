/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
import ExplicitRIP.Provider.FramePotential

/-!
# [KM, (11)]: the frame-potential bound

Source: [KM, proof of Theorem 4, (11)].
-/

public section

open scoped Matrix

/-- [KM, (11)]. For `Φ ∈ 𝕜^{m×n}` with unit-norm columns, `G = Φ^* Φ` and `H = |G - I|`,
`‖H‖_F² = tr(G²) - n ≥ n (n - m)/m`. -/
theorem ExplicitRIP.frame_potential_bound :
    ∀ {𝕜 : Type} [RCLike 𝕜] (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) 𝕜),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
        ∑ i, ∑ j, ‖(Φᴴ *
            Φ - 1 : Matrix (Fin n) (Fin n) 𝕜) i j‖ ^ 2 = RCLike.re (Matrix.trace ((Φᴴ * Φ) * (Φᴴ *
                Φ))) - n ∧
          (n : ℝ) * (n - m) / m ≤ ∑ i, ∑ j, ‖(Φᴴ * Φ - 1 : Matrix (Fin n) (Fin n) 𝕜) i j‖ ^ 2 :=
by exact ExplicitRIP.Provider.frame_potential_bound
