/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Basic.Incidence
public import ExplicitRIP.Zahl.Incidence.Counting.Coloring

/-! # Finite means and independent coordinates -/

@[expose] public section

namespace ExplicitRIP.Zahl
namespace Sampling

open scoped BigOperators

/-- Uniform mean with the canonical finite-type structure. -/
noncomputable def uniformMean {α : Type*} [Finite α] (f : α → ℝ) : ℝ :=
  Finset.expect (@Finset.univ α (Fintype.ofFinite α)) f

/-- A fixed normalization for averages whose finite-type instances differ. -/
lemma expect_univ_canonical {α : Type*} [Fintype α] (f : α → ℝ) :
    Finset.expect Finset.univ f = uniformMean f := by
  unfold uniformMean
  apply Finset.expect_congr
  · exact congrArg (fun I : Fintype α => @Finset.univ α I) (Subsingleton.elim _ _)
  · intro _ _
    rfl

lemma expect_univ_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) :
    Finset.expect Finset.univ f =
      Finset.expect Finset.univ (fun a => Finset.expect Finset.univ (fun b => f (a, b))) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

open Classical in
lemma expect_eval {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β] [Nonempty β]
    (i : α) (f : β → ℝ) :
    Finset.expect (Finset.univ : Finset (α → β)) (fun χ => f (χ i)) =
      Finset.expect Finset.univ f := by
  classical
  calc
    _ = Finset.expect Finset.univ (fun p : β × ({j : α // j ≠ i} → β) => f p.1) :=
      Fintype.expect_equiv (Equiv.funSplitAt i β) _ _ (fun _ => rfl)
    _ = _ := by simp only [expect_univ_prod, Fintype.expect_const]

open Classical in
/-- Functions depending on disjoint groups of coordinates have factored finite means. -/
lemma expect_mul_of_disjoint {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β] [Nonempty β]
    (S T : Finset α) (hST : Disjoint S T) (f g : (α → β) → ℝ)
    (hf : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hg : ∀ x y, (∀ i ∈ T, x i = y i) → g x = g y) :
    Finset.expect Finset.univ (fun x => f x * g x) =
      Finset.expect Finset.univ f * Finset.expect Finset.univ g := by
  classical
  let b : β := Classical.choice inferInstance
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ : α => β)
  let f' (u : ↥S → β) := f (e.symm (u, fun _ => b))
  let g' (v : {i : α // i ∉ S} → β) := g (e.symm (fun _ => b, v))
  have hf' (x : α → β) : f x = f' (e x).1 := by
    apply hf
    intro i hi
    simp [e, hi]
  have hg' (x : α → β) : g x = g' (e x).2 := by
    apply hg
    intro i hi
    have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hST h hi
    simp [e, hiS]
  have hF : Finset.expect Finset.univ f = Finset.expect Finset.univ f' := by
    calc
      _ = Finset.expect Finset.univ (fun p => f' p.1) :=
        Fintype.expect_equiv e _ _ hf'
      _ = _ := by simp only [expect_univ_prod, Fintype.expect_const]
  have hG : Finset.expect Finset.univ g = Finset.expect Finset.univ g' := by
    calc
      _ = Finset.expect Finset.univ (fun p => g' p.2) :=
        Fintype.expect_equiv e _ _ hg'
      _ = _ := by simp only [expect_univ_prod, Fintype.expect_const]
  calc
    _ = Finset.expect Finset.univ (fun p => f' p.1 * g' p.2) :=
      Fintype.expect_equiv e _ _ (fun x => by rw [hf' x, hg' x])
    _ = _ := by rw [expect_univ_prod, ← Finset.expect_mul_expect, hF, hG]

open Classical in
lemma expect_pair {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β] [Nonempty β]
    (i j : α) (hij : i ≠ j) (f g : β → ℝ) :
    Finset.expect (Finset.univ : Finset (α → β)) (fun χ => f (χ i) * g (χ j)) =
      Finset.expect Finset.univ f * Finset.expect Finset.univ g := by
  classical
  rw [expect_mul_of_disjoint {i} {j} (by simpa using hij)
    (fun χ => f (χ i)) (fun χ => g (χ j))
    (fun x y h => congrArg f (h i (Finset.mem_singleton_self i)))
    (fun x y h => congrArg g (h j (Finset.mem_singleton_self j))),
    expect_eval, expect_eval]

open Classical in
lemma colorSample_inter_eq {α : Type*} (L W : Finset α) (hWL : W ⊆ L) {k : ℕ}
    (χ : ↥L → Fin k) :
    colorSample L χ ∩ W =
      (W.attach.filter (fun a : ↥W => (χ ⟨a.val, hWL a.property⟩).val = 0)).image Subtype.val := by
  classical
  ext a
  simp only [Finset.mem_inter, mem_colorSample_iff, Finset.mem_image, Finset.mem_filter,
    Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨h, hh⟩, hw⟩
    exact ⟨⟨a, hw⟩, hh, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨hWL b.property, hb⟩, b.property⟩

end Sampling
end ExplicitRIP.Zahl
