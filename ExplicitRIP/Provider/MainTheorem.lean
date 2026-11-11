/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.Cholesky
import ExplicitRIP.Analysis.MainAsymptotics.ScalarBounds

/-!
# Proof of Theorem 1 of [KM]: the restricted isometry family

Source: [KM, Theorem 1 and its proof, (16), and footnotes 4 and 5].

The logarithmic translate count `L = ⌊log p⌋` and sparsity `k = ⌊p² / (log p)⁶⌋` in
[KM, Theorem 1] follow from the final RIP bound and the scalar asymptotic estimates. Along
primes `p ≡ 3 (mod 4)`, the selected Cholesky matrices have unit-norm columns, `m, n → ∞`,
`m/n → 0`, `δ_k → 0`, `k ≤ m^{2/3}`, and `log k / log m → 2/3`.
-/

public section

open scoped Matrix
open ExplicitRIP.MainAsymptotics

theorem ExplicitRIP.Provider.main_theorem :
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
          (k : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) ∧ |Real.log k / Real.log m - 2 / 3| ≤ ε := by
  classical
  obtain ⟨C, hC, hQ⟩ := ExplicitRIP.Contact.Cholesky.final_rip
  refine ⟨primes_three_mod_four_infinite, fun ε hε => ?_⟩
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.1 (eventually_scalar_hyps ε C)
  refine ⟨P, fun p _ _ hPp => ?_⟩
  obtain ⟨hp2, hpε, hpoly, hℓ⟩ := hP p hPp
  obtain ⟨hL1, hLp, hk1, hkp, hn, hm, hmn, hrip, hk23, hlog⟩ :=
    scalar_bounds ε C hε hC p hp2 hpε hpoly hℓ
  intro L T k m n
  have hT : T.card = L := card_initial_segment p L hLp
  obtain ⟨_, hmEq, hnEq, hunit, hrip'⟩ := hQ p T (hT ▸ hL1)
  have hmEq' : m = (p - 1) * (p ^ 2 + 1) := hmEq
  have hnEq' : n = L * p ^ 3 := by rw [← hT]; exact hnEq
  obtain ⟨hdD, hD⟩ := hrip' k hk1 hkp
  rw [hT] at hD
  refine ⟨hunit, ?_, ?_, ?_, le_trans hdD (le_trans hD hrip), ?_, ?_⟩
  · rw [hnEq']; exact hn
  · rw [hmEq']; exact hm
  · rw [hmEq', hnEq']; exact hmn
  · rw [hmEq']; exact hk23
  · rw [hmEq']; exact hlog
