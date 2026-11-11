/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.Moments
public import ExplicitRIP.GuthZahl.Basic
import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Capturing a line through sampled witnesses

The injective rich-point witnesses give distinct roots on the original line.
An outside line therefore has at most the polynomial degree many sampled
witnesses.
-/

public section

namespace ExplicitRIP.GuthZahl.Sampling.DegreeReduction

open Classical in
theorem sampled_witnesses_card_le {K : Type*} [Field K]
    (L : Line K) (m : ℕ) (x : Fin m → Point K) (W : Fin m → Line K)
    (hx : Function.Injective x) (hW : Function.Injective W)
    (hinc : ∀ i, x i ∈ L.1 ∧ x i ∈ (W i).1)
    (f : Poly K) (T : Finset (Line K)) (hf : ∀ M ∈ T, LineOn f M)
    (hout : ¬ LineOn f L) :
    (T ∩ Finset.univ.image W).card ≤ f.totalDegree := by
  let I : Finset (Fin m) := Finset.univ.filter (fun i => W i ∈ T)
  have himage : I.image W = T ∩ Finset.univ.image W := by
    ext M
    simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i, rfl⟩
    · rintro ⟨hM, i, rfl⟩
      exact ⟨i, hM, rfl⟩
  obtain ⟨hfinite, hdegree⟩ := line_hypersurface_bound f L hout
  have hsubset : (↑(I.image x) : Set (Point K)) ⊆
      {a : Point K | a ∈ L.1 ∧ MvPolynomial.eval a f = 0} := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨(hinc i).1, ?_⟩
    exact eval_eq_zero_of_lineOn
      (hf (W i) (Finset.mem_filter.mp hi).2) (hinc i).2
  calc
    _ = (I.image W).card := congrArg Finset.card himage.symm
    _ = I.card := Finset.card_image_of_injective I hW
    _ = (I.image x).card := (Finset.card_image_of_injective I hx).symm
    _ = (↑(I.image x) : Set (Point K)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsubset hfinite
    _ ≤ _ := hdegree

open Classical in
/-- Choose all rich-point witnesses and retain their root-counting property. -/
theorem exists_witness_set {K : Type*} [Field K]
    (Ls : Finset (Line K)) (L : Line K) (hL : L ∈ Ls) :
    ∃ W : Finset (Line K), W ⊆ Ls ∧
      W.card = (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard ∧
      ∀ (f : Poly K) (T : Finset (Line K)), (∀ M ∈ T, LineOn f M) →
        ¬ LineOn f L → (T ∩ W).card ≤ f.totalDegree := by
  let m := (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard
  obtain ⟨x, W, hx, hW, hinc⟩ := rich_point_witnesses Ls L hL m le_rfl
  refine ⟨Finset.univ.image W, ?_, ?_, ?_⟩
  · intro M hM
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hM
    exact (hinc i).1
  · rw [Finset.card_image_of_injective _ hW, Finset.card_univ, Fintype.card_fin]
  · intro f T hf hout
    exact sampled_witnesses_card_le L m x W hx hW
      (fun i => (hinc i).2.2) f T hf hout

end ExplicitRIP.GuthZahl.Sampling.DegreeReduction

end
