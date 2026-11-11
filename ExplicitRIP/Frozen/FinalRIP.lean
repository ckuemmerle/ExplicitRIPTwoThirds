/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.CholeskyMatrix
public import ExplicitRIP.Frozen.Defs.HostGram
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
import ExplicitRIP.Provider.FinalRIP

/-!
# [KM, (16)]: restricted isometry of the selected frame

Source: [KM, proof of Theorem 1, (13), (16), and footnotes 4 and 5].
-/

public section

open scoped Matrix

/-- [KM, (16)] and the construction in the proof of [KM, Theorem 1]. There is an absolute
constant `C` such that for every prime `p ≡ 3 (mod 4)` and every `T ⊆ 𝔽_p` with
`L = |T| ≥ 1`, the subframe `Φ_T = choleskyMatrix p T` of the columns indexed by `V'_T` has
Gram matrix `G[V'_T]`, `m = (p - 1)(p² + 1)` rows and `n = L p³` unit-norm columns. For
`1 ≤ k ≤ p²`, `δ_k(Φ_T) ≤ Δ_k(Φ_T) ≤ C (μ L √k log(2k) + k ν)`, with `μ = (p² - p + 1)/m`
and `ν = 1/(p² + 1)` as in [KM, (13)]. The final asymptotic expression
`L√k log(2k)/p + k/p²` in [KM, (16)] uses `μ ∼ 1/p` and `ν ∼ 1/p²`, stated in
`ExplicitRIP.host_frame_params`. -/
theorem ExplicitRIP.final_rip :
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
            C * (μ * T.card * Real.sqrt k * Real.log (2 * k) + k * ν) :=
by exact ExplicitRIP.Provider.final_rip
