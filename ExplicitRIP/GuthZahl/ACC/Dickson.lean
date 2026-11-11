/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Order
import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Compactness.Compact

/-!
# Controlled Dickson sequences

The finite coordinate choices form a compact product. Dickson's lemma covers this
product by open cylinders witnessing an increasing pair. A finite subcover bounds
all controlled bad sequences. This is the finite-branching compactness argument.
-/

public section

namespace ExplicitRIP.GuthZahl.ACC

/-- Finite branching plus Dickson gives a bound on every controlled bad sequence. -/
theorem _root_.ExplicitRIP.GuthZahl.controlled_dickson_bound (N : ℕ) (τ : ℕ → ℕ) :
    ∃ M : ℕ, ∀ m : ℕ, ∀ a : Fin m → (Fin N → ℕ),
      (∀ i, (∑ k, a i k) ≤ τ i.val) →
      (∀ i j, i < j → ¬ a i ≤ a j) → m ≤ M := by
  classical
  let F : ℕ → Type := fun i => Fin N → Fin (τ i + 1)
  let X := ∀ i, F i
  let U : ℕ × ℕ → Set X := fun p =>
    {x | p.1 < p.2 ∧ ∀ k, (x p.1 k).val ≤ (x p.2 k).val}
  have hU : ∀ p, IsOpen (U p) := by
    intro p
    change IsOpen ((fun x : X => (x p.1, x p.2)) ⁻¹'
      {q : F p.1 × F p.2 | p.1 < p.2 ∧ ∀ k, (q.1 k).val ≤ (q.2 k).val})
    exact (isOpen_discrete _).preimage
      ((continuous_apply p.1).prodMk (continuous_apply p.2))
  have hcover : Set.univ ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨i, j, hij, hle⟩ :=
      wellQuasiOrdered_le (fun n => fun k : Fin N => (x n k).val)
    exact Set.mem_iUnion.mpr ⟨(i, j), hij, hle⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨s.sup Prod.snd + 1, ?_⟩
  intro m a ha hbad
  by_contra hbound
  have hm : s.sup Prod.snd + 1 < m := Nat.lt_of_not_ge hbound
  let x : X := fun n k => if hn : n < m then
    ⟨a ⟨n, hn⟩ k, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
        (ha ⟨n, hn⟩))⟩ else 0
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  obtain ⟨hij, hle⟩ := hx
  have hj : p.2 < m := lt_of_le_of_lt (Finset.le_sup hp) (Nat.lt_trans (Nat.lt_succ_self _) hm)
  have hi : p.1 < m := hij.trans hj
  apply hbad ⟨p.1, hi⟩ ⟨p.2, hj⟩ hij
  intro k
  simpa only [x, dite_eq_left hi, dite_eq_left hj] using hle k

end ExplicitRIP.GuthZahl.ACC

end
