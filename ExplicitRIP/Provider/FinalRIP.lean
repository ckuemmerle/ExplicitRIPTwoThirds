/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.Cholesky

/-!
# Proof of [KM, (16)]: the selected Cholesky frame

Source: [KM, proof of Theorem 1, (13), (16), and footnotes 4 and 5].

The norm-graph density estimate controls the unsigned Gram error of the selected host frame. For
`L = |T| ≥ 1` and `1 ≤ k ≤ p²`, it gives `δ_k(Φ_T) ≤ Δ_k(Φ_T) ≲ μ L √k log(2k) + k ν`. The Gram
identity, row count `m = (p - 1)(p² + 1)`, column count `n = L p³`, and unit column norms come
from the Cholesky realization of [KM, footnote 4].
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.final_rip :
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
  exact ExplicitRIP.Contact.Cholesky.final_rip
