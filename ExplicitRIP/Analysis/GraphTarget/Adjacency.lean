/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.OpNorm
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Analysis.RealComplex.Basic
import ExplicitRIP.Frozen.LevDRBound
import ExplicitRIP.Frozen.SubgraphDensityDR

/-!
# Support adjacency norms from hereditary density

These graph restriction and norm estimates implement the adjacency and complement terms in
[KM, proof of Theorem 1, (16)].
-/

public section

open scoped Matrix

namespace ExplicitRIP.GraphTarget

/-- Injective graph pullback preserves the number of induced unordered edges. -/
theorem inducedEdgeCount_comap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : W → V) (hf : Function.Injective f)
    [DecidableRel (G.comap f).Adj] (U : Finset W) :
    inducedEdgeCount (G.comap f) U = inducedEdgeCount G (U.map ⟨f, hf⟩) := by
  unfold inducedEdgeCount
  rw [Finset.sym2_map, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ x y => rfl

/-- Density on the selected vertices transfers to every subset of a support. -/
theorem support_density {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Γ : Finset V) (D : ℝ) (k : ℕ)
    (hE : ∀ U ⊆ Γ, U.card ≤ k →
      (inducedEdgeCount G U : ℝ) ≤ D * (U.card : ℝ) ^ (3 / 2 : ℝ))
    (S : Finset Γ) (hS : S.card ≤ k) (U : Finset S) :
    (inducedEdgeCount (G.comap (fun i : S => i.1.1)) U : ℝ) ≤
      D * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  let f : S → V := fun i => i.1.1
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have hsub : U.map ⟨f, hf⟩ ⊆ Γ := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hz
    exact u.1.2
  have hcard : (U.map ⟨f, hf⟩).card ≤ k := by
    rw [Finset.card_map]
    exact (Finset.card_le_univ U).trans (by simpa only [Fintype.card_coe] using hS)
  have h := hE (U.map ⟨f, hf⟩) hsub hcard
  rw [Finset.card_map, ← inducedEdgeCount_comap _ f hf U] at h
  exact h

/-- Adjacency operator norms are at most the maximal possible degree. -/
theorem adjacency_opNorm_le_card_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V ≤ k) : opNorm (G.adjMatrix ℝ) ≤ (k : ℝ) - 1 := by
  apply (Quant.opNorm_le_oneToOneNorm_of_isSymm _ G.isSymm_adjMatrix).trans
  refine Real.iSup_le (fun j => ?_) (sub_nonneg.mpr (by exact_mod_cast hk))
  have hsum : (∑ i, ‖G.adjMatrix ℝ i j‖) = (G.degree j : ℝ) := by
    calc
      _ = ∑ i, G.adjMatrix ℝ j i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]
        split_ifs <;> norm_num
      _ = _ := by
        simpa only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] using
          (SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (a := (1 : ℝ)) (v := j))
  rw [hsum]
  have hn : G.degree j + 1 ≤ k := (Nat.succ_le_iff.mpr (G.degree_lt_card_verts j)).trans hcard
  have hr : (G.degree j : ℝ) + 1 ≤ k := by exact_mod_cast hn
  linarith only [hr]

/-- The absolute logarithmic comparison holds for real matrices. -/
theorem exists_real_lev_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (M : Matrix V V ℝ),
      opNorm M ≤ C * Real.log (2 * Fintype.card V) * drNorm M := by
  obtain ⟨C, hC, h⟩ := lev_dr_bound
  refine ⟨C, hC, fun V _ _ M => ?_⟩
  exact (UnsignedHybrid.opNorm_real_le_opNorm_complex M).trans
    (by simpa only [UnsignedHybrid.drNorm_map_ofReal] using h V (M.map Complex.ofReal))

/-- Exponent `3/2` density bounds the adjacency norm uniformly over smaller supports. -/
theorem adjacency_opNorm_le_of_density {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D CL : ℝ) (hD : 0 ≤ D) (hCL : 0 ≤ CL)
    (hLev : ∀ M : Matrix V V ℝ,
      opNorm M ≤ CL * Real.log (2 * Fintype.card V) * drNorm M)
    (hE : ∀ U : Finset V,
      (inducedEdgeCount G U : ℝ) ≤ D * (U.card : ℝ) ^ (3 / 2 : ℝ))
    (k : ℕ) (hcardpos : 1 ≤ Fintype.card V) (hcard : Fintype.card V ≤ k) :
    opNorm (G.adjMatrix ℝ) ≤
      (CL * 2 ^ ((3 / 2 : ℝ) + 1)) * (D * Real.sqrt k * Real.log (2 * k)) := by
  have hDR := subgraph_density_dr_bound V G D (3 / 2)
    hD (by norm_num) (by norm_num) hE
  rw [show max (1 / 2 : ℝ) (3 / 2 - 1) = 1 / 2 by norm_num] at hDR
  rw [← Real.sqrt_eq_rpow] at hDR
  have hlogpos : 0 ≤ Real.log (2 * (Fintype.card V : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * Fintype.card V by omega))
  have hlog : Real.log (2 * (Fintype.card V : ℝ)) ≤ Real.log (2 * (k : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num)
  have hsqrt : Real.sqrt (Fintype.card V : ℝ) ≤ Real.sqrt (k : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hcard)
  calc
    opNorm (G.adjMatrix ℝ) ≤
        CL * Real.log (2 * (Fintype.card V : ℝ)) * drNorm (G.adjMatrix ℝ) := hLev _
    _ ≤ CL * Real.log (2 * (Fintype.card V : ℝ)) *
        (2 ^ ((3 / 2 : ℝ) + 1) * D * Real.sqrt (Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left hDR (mul_nonneg hCL hlogpos)
    _ ≤ CL * Real.log (2 * (k : ℝ)) *
        (2 ^ ((3 / 2 : ℝ) + 1) * D * Real.sqrt (k : ℝ)) := by
      gcongr
      exact mul_nonneg hCL (hlogpos.trans hlog)
    _ = _ := by ring

end ExplicitRIP.GraphTarget
