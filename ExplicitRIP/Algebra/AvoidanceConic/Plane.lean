/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.LinearFactors
public import Mathlib

/-!
# Affine planes and the exclusion of linear factors

An ambient line bound smaller than the field size excludes a linear divisor of
any polynomial whose plane zero set lies in the selected set.
-/

@[expose] public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial Finset
open scoped Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The affine plane map with the given ordered direction vectors. -/
def planeMap (x₀ u w : V) (q : Fin 2 → K) : V := x₀ + q 0 • u + q 1 • w

theorem planeMap_injective (x₀ u w : V) (huw : LinearIndependent K ![u, w]) :
    Function.Injective (planeMap (K := K) x₀ u w) := by
  intro q r h
  apply huw.fintypeLinearCombination_injective
  simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  apply add_left_cancel (a := x₀)
  simpa only [planeMap, add_assoc] using h

theorem plane_direction_ne_zero (u w : V) (huw : LinearIndependent K ![u, w])
    (v : Fin 2 → K) (hv : v ≠ 0) : v 0 • u + v 1 • w ≠ 0 := by
  intro h
  apply hv
  apply huw.fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply, zero_smul, add_zero] using h

theorem planeMap_line (x₀ u w : V) (a v : Fin 2 → K) (t : K) :
    planeMap x₀ u w (fun i => a i + t * v i) =
      planeMap x₀ u w a + t • (v 0 • u + v 1 • w) := by
  simp only [planeMap, add_smul, mul_smul, smul_add]
  abel

open Classical in
theorem field_card_le_of_line_subset [Fintype K] (S : Finset V) (n : ℕ)
    (hline : ∀ a v : V, v ≠ 0 → (S.filter (fun x => ∃ t : K, x = a + t • v)).card ≤ n)
    (a v : V) (hv : v ≠ 0) (hsub : ∀ t : K, a + t • v ∈ S) :
    Fintype.card K ≤ n := by
  have hi : Function.Injective (fun t : K => a + t • v) := by
    intro s t h
    exact smul_left_injective K hv (add_left_cancel h)
  have hs : (univ.image fun t : K => a + t • v) ⊆
      S.filter (fun x => ∃ t : K, x = a + t • v) := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨hsub t, ⟨t, rfl⟩⟩
  have hc := (card_le_card hs).trans (hline a v hv)
  simpa only [card_image_of_injective _ hi, card_univ] using hc

open Classical in
/-- A line bound smaller than the field size rules out a linear polynomial factor. -/
theorem no_linear_dvd_of_line_bound [Fintype K] (S : Finset V) (n : ℕ)
    (hline : ∀ a v : V, v ≠ 0 → (S.filter (fun x => ∃ t : K, x = a + t • v)).card ≤ n)
    (hn : n < Fintype.card K) (x₀ u w : V) (huw : LinearIndependent K ![u, w])
    (P : Bivariate K) (hP : ∀ q : Fin 2 → K, eval q P = 0 → planeMap x₀ u w q ∈ S)
    (L : Bivariate K) (hL : L.totalDegree = 1) : ¬L ∣ P := by
  rintro ⟨A, hA⟩
  obtain ⟨a, v, hv, hzero⟩ := exists_line_of_totalDegree_eq_one L hL
  have hd := plane_direction_ne_zero u w huw v hv
  have hsub (t : K) : planeMap x₀ u w a + t • (v 0 • u + v 1 • w) ∈ S := by
    rw [← planeMap_line]
    apply hP
    rw [hA, map_mul, hzero, zero_mul]
  exact (not_le_of_gt hn) (field_card_le_of_line_subset S n hline
    (planeMap x₀ u w a) (v 0 • u + v 1 • w) hd hsub)

end ExplicitRIP.Avconic

end
