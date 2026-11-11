/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Frozen.HybridSplitEstimate
import ExplicitRIP.Frozen.LargeEntriesDR
import ExplicitRIP.Frozen.SubgraphDensityDR
import ExplicitRIP.Frozen.AbsoluteRayleigh
import ExplicitRIP.Analysis.DensityRIP.Basic

/-!
# Proof of [KM, (9)]: restricted isometry from hereditary density

Source: [KM, Section 2.2, (9)].

Hereditary density of the large-entry graph bounds the restricted isometry constant. For
unit-norm columns of coherence `μ`, threshold `0 < ν < μ`, and `e(U) ≤ c |U|^β` for every
`|U| ≤ k`, with `c ≥ 0`, `1 ≤ β ≤ 2`, and `k ≥ 1`, the bound is
`δ_k ≲ c k^{max(1/2, β-1)} log(2k) μ + k ν`. The absolute multiplier is eight times that of the
hybrid estimate.
-/

public section

open scoped Matrix
open ExplicitRIP ExplicitRIP.DensityRIP

/-- Hereditary density of the threshold graph controls every permitted Gram restriction. -/
theorem ExplicitRIP.Provider.rip_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Φ : Matrix m n ℂ),
      (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ (ν c β : ℝ) (k : ℕ),
        0 < ν → ν < ExplicitRIP.coherence Φ → 0 ≤ c → 1 ≤ β → β ≤ 2 → 1 ≤ k →
        (∀ U : Finset n, U.card ≤ k →
          (open Classical in
            (ExplicitRIP.inducedEdgeCount
              (SimpleGraph.fromRel fun i j => ν < ‖(Φᴴ * Φ) i j‖) U : ℝ)) ≤
            c * (U.card : ℝ) ^ β) →
        ExplicitRIP.ripConstant Φ k ≤
          C * (c * (k : ℝ) ^ max (1 / 2 : ℝ) (β - 1) * Real.log (2 * k) * ExplicitRIP.coherence Φ +
            k * ν) :=
by
  classical
  obtain ⟨C₁, hC₁, hsplit⟩ := ExplicitRIP.hybrid_split_estimate
  refine ⟨8 * C₁, mul_pos (by norm_num) hC₁, ?_⟩
  intro m n _ _ _ Φ hΦ ν c β k hν hνμ hc hβ₁ hβ₂ hk hdensity
  have hμ : 0 ≤ coherence Φ := (hν.trans hνμ).le
  let e : ℝ := max (1 / 2 : ℝ) (β - 1)
  have he : 0 ≤ e := le_trans (by norm_num) (le_max_left _ _)
  have hkν : 0 ≤ (k : ℝ) * ν := mul_nonneg (Nat.cast_nonneg _) hν.le
  unfold ExplicitRIP.ripConstant
  have : Nonempty {S : Finset n // S.card ≤ k} :=
    ⟨⟨∅, by simp only [Finset.card_empty, Nat.zero_le]⟩⟩
  apply ciSup_le
  rintro ⟨S, hSk⟩
  rw [UnsignedHybrid.principal_gram_error_eq]
  let M : Matrix S S ℂ := (Φᴴ * Φ - 1).submatrix Subtype.val Subtype.val
  let Y : Matrix S S ℂ := Matrix.of fun i j => if ν < ‖M i j‖ then 0 else M i j
  let X : Matrix S S ℂ := Matrix.of fun i j => if ν < ‖M i j‖ then M i j else 0
  let A : Matrix S S ℝ := Matrix.of fun i j => if X i j = 0 then 0 else 1
  let G : SimpleGraph n := SimpleGraph.fromRel fun i j => ν < ‖(Φᴴ * Φ) i j‖
  let Gs : SimpleGraph S := G.comap (Subtype.val : S → n)
  have hA : A = Gs.adjMatrix ℝ := large_support_eq_adjMatrix Φ hΦ ν hν S
  have hdensityS : ∀ U : Finset S,
      (inducedEdgeCount Gs U : ℝ) ≤ c * (U.card : ℝ) ^ β := by
    intro U
    have hUk : (U.map (Function.Embedding.subtype (· ∈ S))).card ≤ k := by
      calc
        _ = U.card := Finset.card_map _
        _ ≤ Fintype.card S := Finset.card_le_univ U
        _ = S.card := Fintype.card_coe S
        _ ≤ k := hSk
    have h := hdensity (U.map (Function.Embedding.subtype (· ∈ S))) hUk
    rw [inducedEdgeCount_comap_subtype G S U]
    simpa only [Finset.card_map] using h
  have hAs : drNorm A ≤ (2 : ℝ) ^ (β + 1) * c * (S.card : ℝ) ^ e := by
    rw [hA]
    simpa only [Fintype.card_coe] using
      ExplicitRIP.subgraph_density_dr_bound S Gs c β hc hβ₁ hβ₂ hdensityS
  have hpowers : (S.card : ℝ) ^ e ≤ (k : ℝ) ^ e :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hSk) he
  have hAbound : drNorm A ≤ 8 * c * (k : ℝ) ^ e :=
    hAs.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (two_rpow_add_one_le_eight β hβ₂) hc)
      hpowers (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (by norm_num) hc))
  have hlarge := ExplicitRIP.large_entries_dr_bound Φ hΦ ν S
  change drNorm (X.map fun z => ‖z‖) ≤
      (⨆ ij : S × S, ‖X ij.1 ij.2‖) * drNorm A ∧
      (⨆ ij : S × S, ‖X ij.1 ij.2‖) ≤ coherence Φ at hlarge
  have hX : drNorm X ≤ coherence Φ * (8 * c * (k : ℝ) ^ e) := by
    calc
      drNorm X ≤ drNorm (X.map fun z => ‖z‖) := ExplicitRIP.drNorm_le_drNorm_abs S X
      _ ≤ (⨆ ij : S × S, ‖X ij.1 ij.2‖) * drNorm A := hlarge.1
      _ ≤ coherence Φ * drNorm A :=
        mul_le_mul_of_nonneg_right hlarge.2 (ExplicitRIP.Flat.drNorm_nonneg A)
      _ ≤ coherence Φ * (8 * c * (k : ℝ) ^ e) := mul_le_mul_of_nonneg_left hAbound hμ
  have hYs : oneToOneNorm Y ≤ (S.card : ℝ) * ν := by
    simpa only [Fintype.card_coe] using oneToOneNorm_small_le M ν hν.le
  have hY : oneToOneNorm Y ≤ (k : ℝ) * ν :=
    hYs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hSk) hν.le)
  have hlogs := log_two_mul_card_bounds hSk hk
  have hlogk : 0 ≤ Real.log (2 * (k : ℝ)) :=
    (log_two_mul_card_bounds (le_refl k) hk).1
  have hlogX : Real.log (2 * (S.card : ℝ)) * drNorm X ≤
      Real.log (2 * (k : ℝ)) * (coherence Φ * (8 * c * (k : ℝ) ^ e)) :=
    mul_le_mul hlogs.2 hX (ExplicitRIP.Flat.drNorm_nonneg X) hlogk
  have hs := hsplit Φ ν S.card S rfl
  change opNorm M ≤ opNorm (M - Y) + opNorm Y ∧
    opNorm (M - Y) + opNorm Y ≤
      C₁ * (Real.log (2 * (S.card : ℝ)) * drNorm (M - Y) + oneToOneNorm Y) at hs
  have hXY : M - Y = X := sub_small_eq_large M ν
  rw [hXY] at hs
  change opNorm M ≤ _
  calc
    opNorm M ≤ C₁ * (Real.log (2 * (S.card : ℝ)) * drNorm X + oneToOneNorm Y) :=
      hs.1.trans hs.2
    _ ≤ C₁ * (Real.log (2 * (k : ℝ)) * (coherence Φ * (8 * c * (k : ℝ) ^ e)) + k * ν) :=
      mul_le_mul_of_nonneg_left (add_le_add hlogX hY) hC₁.le
    _ ≤ 8 * C₁ * (c * (k : ℝ) ^ e * Real.log (2 * k) * coherence Φ + k * ν) := by
      have hslack : 0 ≤ C₁ * ((k : ℝ) * ν) := mul_nonneg hC₁.le hkν
      nlinarith only [hslack]
