/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
public import ExplicitRIP.Frozen.Defs.OneToOneNorm
public import ExplicitRIP.Analysis.FlatRIP.Comparison
public import ExplicitRIP.Analysis.Gershgorin.HermitianBound
public import ExplicitRIP.Analysis.UnsignedHybrid.Gram

/-!
# Threshold restrictions for the density RIP bound

Principal restrictions and small-entry bounds supply the hereditary-density estimate.

Source: [KM, Section 2.2, (9)].
-/

public section

namespace ExplicitRIP.DensityRIP

open scoped Matrix

theorem sub_small_eq_large {ι : Type*} (M : Matrix ι ι ℂ) (τ : ℝ) :
    M - Matrix.of (fun i j => if τ < ‖M i j‖ then 0 else M i j) =
      Matrix.of (fun i j => if τ < ‖M i j‖ then M i j else 0) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp only [sub_zero, sub_self]

/-- Absolute column sums of the small-entry part are at most `card ι * τ`. -/
theorem oneToOneNorm_small_le {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    oneToOneNorm (Matrix.of fun i j => if τ < ‖M i j‖ then 0 else M i j) ≤
      (Fintype.card ι : ℝ) * τ := by
  apply Real.iSup_le ?_ (mul_nonneg (Nat.cast_nonneg _) hτ)
  intro j
  calc
    (∑ i : ι, ‖(Matrix.of fun i j => if τ < ‖M i j‖ then 0 else M i j) i j‖)
        ≤ ∑ _i : ι, τ := by
          apply Finset.sum_le_sum
          intro i _
          dsimp only [Matrix.of_apply]
          split_ifs with h
          · simpa only [norm_zero] using hτ
          · exact le_of_not_gt h
    _ = (Fintype.card ι : ℝ) * τ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The indicator of large Gram-error entries is the induced threshold graph. -/
theorem large_support_eq_adjMatrix {m n : Type*} [Fintype m] [DecidableEq n]
    (Φ : Matrix m n ℂ) (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1)
    (ν : ℝ) (hν : 0 < ν) (S : Finset n)
    [DecidableRel ((SimpleGraph.fromRel fun i j => ν < ‖(Φᴴ * Φ) i j‖).comap
      (Subtype.val : S → n)).Adj] :
    let M : Matrix S S ℂ := (Φᴴ * Φ - 1).submatrix Subtype.val Subtype.val
    Matrix.of (fun i j : S =>
      if (if ν < ‖M i j‖ then M i j else 0) = 0 then (0 : ℝ) else 1) =
      ((SimpleGraph.fromRel fun i j => ν < ‖(Φᴴ * Φ) i j‖).comap
        (Subtype.val : S → n)).adjMatrix ℝ := by
  classical
  dsimp only
  ext i j
  simp only [Matrix.of_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.comap_adj,
    SimpleGraph.fromRel_adj]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.submatrix_apply, Flat.gram_error_diag Φ hΦ, norm_zero,
      not_lt_of_ge hν.le, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
  · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have hnorm : ‖(Φᴴ * Φ) j.val i.val‖ = ‖(Φᴴ * Φ) i.val j.val‖ :=
      Gersh.norm_apply_eq_norm_transpose (Matrix.isHermitian_conjTranspose_mul_self Φ) _ _
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply_ne hval,
      sub_zero, hnorm, or_self, hval, ne_eq, not_false_eq_true, true_and]
    by_cases hlarge : ν < ‖(Φᴴ * Φ) i.val j.val‖
    · have hne : (Φᴴ * Φ) i.val j.val ≠ 0 := norm_pos_iff.mp (hν.trans hlarge)
      simp only [hlarge, ite_true, hne, ite_false]
    · simp only [hlarge, ite_false, ite_true]

/-- Pulling back a graph to a finset preserves induced edge counts under the inclusion. -/
theorem inducedEdgeCount_comap_subtype {n : Type*} [DecidableEq n]
    (G : SimpleGraph n) [DecidableRel G.Adj] (S : Finset n) (U : Finset S) :
    inducedEdgeCount (G.comap (Subtype.val : S → n)) U =
      inducedEdgeCount G (U.map (Function.Embedding.subtype (· ∈ S))) := by
  classical
  unfold inducedEdgeCount
  rw [Finset.sym2_map, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ i j =>
    simp only [Function.comp_apply, SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj,
      Function.Embedding.sym2Map_apply, Sym2.map_mk, Function.Embedding.coe_subtype]

theorem two_rpow_add_one_le_eight (β : ℝ) (hβ : β ≤ 2) :
    (2 : ℝ) ^ (β + 1) ≤ 8 := by
  calc
    (2 : ℝ) ^ (β + 1) ≤ (2 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hβ])
    _ = 8 := by norm_num

theorem log_two_mul_card_bounds {s k : ℕ} (hsk : s ≤ k) (hk : 1 ≤ k) :
    0 ≤ Real.log (2 * (s : ℝ)) ∧
      Real.log (2 * (s : ℝ)) ≤ Real.log (2 * (k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith only [hkR])
  by_cases hs : s = 0
  · simpa only [hs, Nat.cast_zero, mul_zero, Real.log_zero, le_refl, true_and] using hlogk
  · have hsR : (1 : ℝ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
    have hskR : (s : ℝ) ≤ k := by exact_mod_cast hsk
    exact ⟨Real.log_nonneg (by linarith only [hsR]),
      Real.log_le_log (by linarith only [hsR]) (by linarith only [hskR])⟩

end ExplicitRIP.DensityRIP
