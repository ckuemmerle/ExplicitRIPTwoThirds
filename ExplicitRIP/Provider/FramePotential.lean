/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.LinearAlgebra.FramePotential.Basic
import Mathlib.Tactic.Linarith

/-!
# Proof of [KM, (11)]: the frame-potential bound

Source: [KM, proof of Theorem 4, (11)].

The Gram matrix `G = Φ^* Φ` of unit-norm columns has off-diagonal squared mass
`‖|G - I|‖_F² = tr(G²) - n ≥ n(n-m)/m`.
-/

public section

open scoped Matrix BigOperators

theorem ExplicitRIP.Provider.frame_potential_bound :
    ∀ {𝕜 : Type} [RCLike 𝕜] (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) 𝕜),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
        ∑ i, ∑ j, ‖(Φᴴ *
            Φ - 1 : Matrix (Fin n) (Fin n) 𝕜) i j‖ ^ 2 = RCLike.re (Matrix.trace ((Φᴴ * Φ) * (Φᴴ *
                Φ))) - n ∧
          (n : ℝ) * (n - m) / m ≤ ∑ i, ∑ j, ‖(Φᴴ * Φ - 1 : Matrix (Fin n) (Fin n) 𝕜) i j‖ ^ 2 :=
by
  intro 𝕜 _ m n Φ hunit
  have hdiag (j : Fin n) : (Φᴴ * Φ) j j = 1 := by
    rw [ExplicitRIP.Framepot.conjTranspose_mul_diag, hunit j, RCLike.ofReal_one]
  have hsum := ExplicitRIP.Framepot.sum_norm_sq_sub_one_add_card (Φᴴ * Φ) hdiag
  simp only [Fintype.card_fin] at hsum
  have htrace := ExplicitRIP.Framepot.sum_norm_sq_eq_re_trace_sq (Φᴴ * Φ)
    (Matrix.isHermitian_conjTranspose_mul_self Φ)
  constructor
  · linarith only [hsum, htrace]
  · by_cases hm : m = 0
    · subst m
      simp only [Nat.cast_zero, div_zero]
      exact Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ =>
          sq_nonneg ‖(Φᴴ * Φ - 1 : Matrix (Fin n) (Fin n) 𝕜) i j‖))
    · have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
      have hcs := ExplicitRIP.Framepot.unit_frame_potential_lower m n Φ hunit
      rw [← hsum] at hcs
      apply (div_le_iff₀ hmpos).2
      nlinarith only [hcs]
