/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Analysis.UnsignedBarrier.Basic
public import ExplicitRIP.Frozen.FramePotential

/-!
# Column energy and star supports

A coordinate-vector test on the central column of a star gives the lower bound for its signed
Gram-error norm.

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.Actbar

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

theorem rip_nonneg (Φ : Matrix I J ℝ) (k : ℕ) : 0 ≤ ripConstant Φ k :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem principal_norm_le (Φ : Matrix I J ℝ) (S : Finset J) (k : ℕ)
    (hS : S.card ≤ k) :
    opNorm ((Φ.submatrix id (Subtype.val : S → J))ᴴ *
      Φ.submatrix id (Subtype.val : S → J) - 1) ≤ ripConstant Φ k := by
  classical
  let f : {S : Finset J // S.card ≤ k} → ℝ := fun S =>
    opNorm ((Φ.submatrix id (Subtype.val : S.1 → J))ᴴ *
      Φ.submatrix id (Subtype.val : S.1 → J) - 1)
  exact le_ciSup (f := f) (Finite.bddAbove_range f) ⟨S, hS⟩

theorem principal_column_energy_le (Φ : Matrix I J ℝ) (S : Finset J) (k : ℕ)
    (hS : S.card ≤ k) (j : S) :
    ∑ i : S, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i.val j.val) ^ 2 ≤ ripConstant Φ k ^ 2 := by
  let A := (Φ.submatrix id (Subtype.val : S → J))ᴴ *
    Φ.submatrix id (Subtype.val : S → J) - (1 : Matrix S S ℝ)
  have he (i : S) : A i j = (Φᴴ * Φ - 1 : Matrix J J ℝ) i.val j.val := by
    simp only [A, Matrix.sub_apply]
    congr 1
    exact (congrArg (fun M : Matrix S S ℝ => M i j)
      (Matrix.submatrix_one (Subtype.val : S → J) Subtype.val_injective)).symm
  have h := Absbar.column_sq_le_opNorm_sq A j
  simp_rw [he] at h
  exact h.trans ((sq_le_sq₀ (norm_nonneg _) (rip_nonneg Φ k)).2
    (principal_norm_le Φ S k hS))

/-- A support containing a center and `t` equal-magnitude entries detects their energy. -/
theorem star_energy_le (Φ : Matrix I J ℝ) (v : J) (N : Finset J) (a : ℝ)
    (hv : v ∉ N) (hN : ∀ i ∈ N, (Φᴴ * Φ - 1 : Matrix J J ℝ) i v = -a)
    (k : ℕ) (hk : 1 ≤ k) :
    ((min (k - 1) N.card : ℕ) : ℝ) * a ^ 2 ≤ ripConstant Φ k ^ 2 := by
  classical
  obtain ⟨T, hTN, hTc⟩ := Finset.exists_subset_card_eq (min_le_right (k - 1) N.card)
  have hvT : v ∉ T := fun h => hv (hTN h)
  let S := insert v T
  have hSc : S.card ≤ k := by
    rw [Finset.card_insert_of_notMem hvT, hTc]
    have := min_le_left (k - 1) N.card
    omega
  have h := principal_column_energy_le Φ S k hSc ⟨v, Finset.mem_insert_self v T⟩
  have hsum : (∑ i : S, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i.val v) ^ 2) =
      ∑ i ∈ S, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2 := by
    exact (Finset.sum_subtype (p := fun i : J => i ∈ S) S (fun _ => Iff.rfl)
      (fun i : J => ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2)).symm
  rw [hsum] at h
  have hT : (∑ i ∈ T, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2) =
      ((min (k - 1) N.card : ℕ) : ℝ) * a ^ 2 := by
    simp only [Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hN i (hTN hi))),
      neg_sq, Finset.sum_const, nsmul_eq_mul, hTc]
  rw [← hT]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert v T)
    (fun i _ _ => sq_nonneg _)).trans h

/-- The finite-dimensional frame bound transported to arbitrary column indices. -/
theorem frame_energy_lower (m : ℕ) (Φ : Matrix (Fin m) J ℝ)
    (hunit : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) :
    (Fintype.card J : ℝ) * (Fintype.card J - m) / m ≤
      ∑ i, ∑ j, ‖(Φᴴ * Φ - 1 : Matrix J J ℝ) i j‖ ^ 2 := by
  classical
  let e := (Fintype.equivFin J).symm
  have hu (j : Fin (Fintype.card J)) : ∑ i, ‖Φ i (e j)‖ ^ 2 = 1 := hunit _
  have h := (ExplicitRIP.frame_potential_bound m (Fintype.card J)
    (Φ.submatrix id e) hu).2
  have he (i j : Fin (Fintype.card J)) :
      ((Φ.submatrix id e)ᴴ * Φ.submatrix id e - 1 :
        Matrix (Fin (Fintype.card J)) (Fin (Fintype.card J)) ℝ) i j =
        (Φᴴ * Φ - 1 : Matrix J J ℝ) (e i) (e j) := by
    simp only [Matrix.sub_apply]
    congr 1
    exact (congrArg (fun M : Matrix (Fin (Fintype.card J)) (Fin (Fintype.card J)) ℝ => M i j)
      (Matrix.submatrix_one e e.injective)).symm
  simp_rw [he] at h
  have hj (i : J) : (∑ j : Fin (Fintype.card J),
      ‖(Φᴴ * Φ - 1 : Matrix J J ℝ) i (e j)‖ ^ 2) =
      ∑ j : J, ‖(Φᴴ * Φ - 1 : Matrix J J ℝ) i j‖ ^ 2 :=
    e.sum_comp (fun j : J => ‖(Φᴴ * Φ - 1 : Matrix J J ℝ) i j‖ ^ 2)
  simp_rw [hj] at h
  rw [e.sum_comp (fun i : J => ∑ j : J, ‖(Φᴴ * Φ - 1 : Matrix J J ℝ) i j‖ ^ 2)] at h
  exact h

/-- Some column has at least the average Gram-error energy. -/
theorem exists_large_column (m : ℕ) (Φ : Matrix (Fin m) J ℝ)
    [Nonempty J] (hm : 0 < m) (hunit : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) :
    ∃ v : J, (Fintype.card J : ℝ) / m - 1 ≤ ∑ i, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2 := by
  have h := frame_energy_lower m Φ hunit
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [Finset.sum_comm] at h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  by_contra! hn
  have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun j _ => hn j)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have heq : (Fintype.card J : ℝ) * (Fintype.card J - m) / m =
      (Fintype.card J : ℝ) * (Fintype.card J / m - 1) := by
    field_simp
  linarith only [h, hlt, heq]

end ExplicitRIP.Actbar
