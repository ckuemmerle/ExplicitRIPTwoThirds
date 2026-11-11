/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.Cholesky.Factor
public import ExplicitRIP.Contact.HereditaryDensity
public import ExplicitRIP.Contact.Cholesky.Bounds
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
import ExplicitRIP.Provider.GraphTarget

/-!
# The quantitative Cholesky realization

The lexicographic Cholesky factor has the prescribed dimensions and unit columns, realizes the
selected host Gram matrix, and satisfies the unsigned RIP estimate of [KM, (16)]. The
factorization is described in [KM, proof of Theorem 1 and footnote 4].
-/

public section

open scoped Matrix

namespace ExplicitRIP.Contact.Cholesky

theorem final_rip :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] (T : Finset (ZMod p)), 1 ≤ T.card →
      let μ : ℝ := ((p : ℝ) ^ 2 - p + 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))
      let ν : ℝ := 1 / ((p : ℝ) ^ 2 + 1)
      (ExplicitRIP.choleskyMatrix p T)ᵀ * ExplicitRIP.choleskyMatrix p T =
          (ExplicitRIP.hostGram ℝ p).submatrix Subtype.val Subtype.val ∧
      (ExplicitRIP.ldlPivots (ExplicitRIP.lexGram p)).length = (p - 1) * (p ^ 2 + 1) ∧
      (ExplicitRIP.selectedVertices p T).card = T.card * p ^ 3 ∧
      (∀ x, ∑ r, ExplicitRIP.choleskyMatrix p T r x ^ 2 = 1) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ p ^ 2 →
        ExplicitRIP.ripConstant (ExplicitRIP.choleskyMatrix p T) k ≤
            ExplicitRIP.unsignedRIPConstant (ExplicitRIP.choleskyMatrix p T) k ∧
          ExplicitRIP.unsignedRIPConstant (ExplicitRIP.choleskyMatrix p T) k ≤
            C * (μ * T.card * Real.sqrt k * Real.log (2 * k) + k * ν) := by
  classical
  obtain ⟨CG, hCG, hG⟩ := ExplicitRIP.Provider.graph_target
  obtain ⟨CE, hCE, hE⟩ := Contact.Density.hereditary_density
  refine ⟨CG * (CE + 1), mul_pos hCG (by positivity), ?_⟩
  intro p _ _ T _hT μ ν
  refine ⟨choleskyMatrix_gram p T, ldlPivots_lexGram_length p,
    Contact.card_selectedVertices p T, choleskyMatrix_column_norm_sq p T, ?_⟩
  intro k hk hkp
  have hbound := hG (ZMod p × ZMod p × ZMod p × ZMod p) (contactGraph p)
    (Actbar.largeEntry p) (Actbar.smallEntry p) (gram_coeff_nonneg p).1 (gram_coeff_nonneg p).2
    (selectedVertices p T) (Fin (ldlPivots (lexGram p)).length) (choleskyMatrix p T)
    (choleskyMatrix_gram p T) (CE * T.card) k
    (mul_nonneg hCE.le (Nat.cast_nonneg _)) hk
    (fun U hU hUk => hE p T U hU (hUk.trans hkp))
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  have hμ : 0 ≤ μ := (gram_coeff_nonneg p).1
  have hν : 0 ≤ ν := (gram_coeff_nonneg p).2
  have hlog : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  let X := μ * T.card * Real.sqrt k * Real.log (2 * k)
  let Y := (k : ℝ) * ν
  have hX : 0 ≤ X := mul_nonneg
    (mul_nonneg (mul_nonneg hμ (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)) hlog
  have hY : 0 ≤ Y := mul_nonneg (Nat.cast_nonneg _) hν
  calc
    CG * (Actbar.largeEntry p * (CE * T.card) * Real.sqrt k * Real.log (2 * k) +
        Actbar.smallEntry p * ((k : ℝ) - 1)) = CG * (CE * X + Y - ν) := by
      dsimp [X, Y, μ, ν, Actbar.largeEntry, Actbar.smallEntry]
      ring
    _ ≤ CG * ((CE + 1) * (X + Y)) := by
      apply mul_le_mul_of_nonneg_left _ hCG.le
      nlinarith only [hX, hY, hν, mul_nonneg hCE.le hY]
    _ = _ := by dsimp [X, Y]; ring

end ExplicitRIP.Contact.Cholesky
