/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Analysis.GraphTarget.Adjacency
import ExplicitRIP.Analysis.GraphTarget.Gram
import ExplicitRIP.Analysis.RealComplex.Basic
import ExplicitRIP.Analysis.UnsignedHybrid.Gram

/-!
# The graph estimate used in the proof of Theorem 1 of [KM]

Source: [KM, proof of Theorem 1, the norm estimates leading to (16)].

This states the graph estimate in a general form. If a selected real frame has Gram matrix
`(I - aA + bĀ)[Γ]`, with `a, b ≥ 0`, and every `U ⊆ Γ` of size at most `k` satisfies
`e(U) ≤ D |U|^{3/2}`, then `δ_k ≤ Δ_k ≲ a D √k log(2k) + b(k - 1)` for `D ≥ 0` and `k ≥ 1`. The
absolute constant comes from the discrete Rayleigh comparison. Support density controls
adjacency, and the maximal degree bound controls the complement.
-/

public section

open scoped Matrix Matrix.Norms.L2Operator
open ExplicitRIP ExplicitRIP.GraphTarget

/-- Hereditary edge density controls the unsigned constant of a two-distance frame. -/
theorem ExplicitRIP.Provider.graph_target :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (a b : ℝ), 0 ≤ a → 0 ≤ b →
      ∀ (Γ : Finset V) (m : Type) [Fintype m] (Φ : Matrix m Γ ℝ),
        Φᵀ * Φ = (1 - a • G.adjMatrix ℝ +
            b • (Matrix.of (fun _ _ => (1 : ℝ)) - 1 - G.adjMatrix ℝ)).submatrix
              (Subtype.val : Γ → V) (Subtype.val : Γ → V) →
        ∀ (D : ℝ) (k : ℕ), 0 ≤ D → 1 ≤ k →
          (∀ U ⊆ Γ, U.card ≤ k →
            (ExplicitRIP.inducedEdgeCount G U : ℝ) ≤ D * (U.card : ℝ) ^ (3 / 2 : ℝ)) →
          ExplicitRIP.ripConstant Φ k ≤ ExplicitRIP.unsignedRIPConstant Φ k ∧
            ExplicitRIP.unsignedRIPConstant Φ k ≤
              C * (a * D * Real.sqrt k * Real.log (2 * k) + b * ((k : ℝ) - 1)) := by
  classical
  obtain ⟨CL, hCL, hLev⟩ := exists_real_lev_constant
  let K : ℝ := CL * 2 ^ ((3 / 2 : ℝ) + 1)
  have hK : 0 ≤ K := mul_nonneg hCL.le (Real.rpow_nonneg (by norm_num) _)
  refine ⟨K + 1, by positivity, ?_⟩
  intro V _ _ G _ a b ha hb Γ m _ Φ hgram D k hD hk hE
  refine ⟨UnsignedHybrid.ripConstant_le_unsignedRIPConstant Φ k, ?_⟩
  have hlog : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  have hX : 0 ≤ a * D * Real.sqrt k * Real.log (2 * k) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha hD) (Real.sqrt_nonneg _)) hlog
  have hY : 0 ≤ b * ((k : ℝ) - 1) :=
    mul_nonneg hb (sub_nonneg.mpr (by exact_mod_cast hk))
  have hbound : 0 ≤ (K + 1) *
      (a * D * Real.sqrt k * Real.log (2 * k) + b * ((k : ℝ) - 1)) :=
    mul_nonneg (by positivity) (add_nonneg hX hY)
  unfold unsignedRIPConstant
  refine Real.iSup_le (fun S => ?_) hbound
  by_cases hS : S.1.Nonempty
  · let Gs := G.comap (fun i : S.1 => i.1.1)
    have hcard : Fintype.card S.1 ≤ k := by simpa only [Fintype.card_coe] using S.2
    have hcardpos : 1 ≤ Fintype.card S.1 := by
      simpa only [Fintype.card_coe] using (Nat.succ_le_iff.mpr hS.card_pos)
    have hA : opNorm (Gs.adjMatrix ℝ) ≤
        K * (D * Real.sqrt k * Real.log (2 * k)) :=
      adjacency_opNorm_le_of_density Gs D CL hD hCL.le (hLev S.1)
        (support_density G Γ D k hE S.1 S.2) k hcardpos hcard
    have hB : opNorm (Gsᶜ.adjMatrix ℝ) ≤ (k : ℝ) - 1 :=
      adjacency_opNorm_le_card_sub_one Gsᶜ k hk hcard
    rw [abs_gram_error_submatrix G a b ha hb Γ Φ hgram S.1]
    calc
      opNorm (a • Gs.adjMatrix ℝ + b • Gsᶜ.adjMatrix ℝ) ≤
          a * opNorm (Gs.adjMatrix ℝ) + b * opNorm (Gsᶜ.adjMatrix ℝ) :=
        Quant.opNorm_add_smul_le a b ha hb _ _
      _ ≤ a * (K * (D * Real.sqrt k * Real.log (2 * k))) + b * ((k : ℝ) - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hA ha) (mul_le_mul_of_nonneg_left hB hb)
      _ = K * (a * D * Real.sqrt k * Real.log (2 * k)) + b * ((k : ℝ) - 1) := by ring
      _ ≤ (K + 1) *
          (a * D * Real.sqrt k * Real.log (2 * k) + b * ((k : ℝ) - 1)) := by
        nlinarith only [hX, mul_nonneg hK hY]
  · have he : S.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hzero : (((Φᴴ * Φ - 1).map fun z => ‖z‖).submatrix
        (Subtype.val : S.1 → Γ) (Subtype.val : S.1 → Γ)) = 0 := by
      ext i j
      exact False.elim (by simpa only [he, Finset.notMem_empty] using i.2)
    rw [hzero]
    change ‖(0 : Matrix S.1 S.1 ℝ)‖ ≤ _
    rw [norm_zero]
    exact hbound
