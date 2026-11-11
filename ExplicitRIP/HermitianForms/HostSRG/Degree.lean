/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostSRG.Transforms

/-!
# The degree of the Hermitian graph

The degree in the Hermitian-forms model of `VO₄⁻(p)` is obtained directly from the coordinates:
a nonzero first diagonal entry gives `(p-1)p²` choices; a zero entry gives `p-1` choices.
Their sum is the degree `(p - 1)(p² + 1)` in [KM, Section 3].
-/

@[expose] public section

namespace ExplicitRIP.Hfsrg

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem quad_eq_zero_of_fst_eq_zero (x : Vertex p) (ha : x.1 = 0)
    (hx : quad p x = 0) : x.2.1 = 0 ∧ x.2.2.1 = 0 := by
  apply (Rank1.sum_sq_eq_zero_iff p _ _).mp
  dsimp [quad] at hx
  rw [ha] at hx
  linear_combination -hx

omit [Fact (p % 4 = 3)] in
theorem last_eq_of_quad_eq_zero (x : Vertex p) (ha : x.1 ≠ 0)
    (hx : quad p x = 0) : x.2.2.2 = (x.2.1 ^ 2 + x.2.2.1 ^ 2) / x.1 := by
  apply (eq_div_iff ha).mpr
  dsimp [quad] at hx
  linear_combination hx

def rankOneParam :
    (({a : ZMod p // a ≠ 0} × (ZMod p × ZMod p)) ⊕ {c : ZMod p // c ≠ 0}) →
      {x : Vertex p // x ≠ 0 ∧ quad p x = 0}
  | .inl ⟨a, b, c⟩ => ⟨(a.val, b, c, (b ^ 2 + c ^ 2) / a.val), by
      constructor
      · intro h
        exact a.property (congrArg Prod.fst h)
      · dsimp [quad]
        field_simp [a.property]; ring⟩
  | .inr c => ⟨(0, 0, 0, c.val), by
      constructor
      · intro h
        exact c.property (congrArg (fun x : Vertex p => x.2.2.2) h)
      · simp [quad]⟩

theorem rankOneParam_bijective : Function.Bijective (rankOneParam p) := by
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Prod.ext
        · exact Subtype.ext (congrArg Prod.fst hval)
        · exact Prod.ext (congrArg (fun z : Vertex p => z.2.1) hval)
            (congrArg (fun z : Vertex p => z.2.2.1) hval)
      | inr y => exact False.elim (x.1.property (congrArg Prod.fst hval))
    | inr x =>
      cases y with
      | inl y => exact False.elim (y.1.property (congrArg Prod.fst hval).symm)
      | inr y =>
        exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : Vertex p => z.2.2.2) hval))
  · intro x
    by_cases ha : x.val.1 = 0
    · obtain ⟨hb, hc⟩ := quad_eq_zero_of_fst_eq_zero p x.val ha x.property.2
      have hd : x.val.2.2.2 ≠ 0 := by
        intro hd
        exact x.property.1 (Prod.ext ha (Prod.ext hb (Prod.ext hc hd)))
      refine ⟨.inr ⟨x.val.2.2.2, hd⟩, Subtype.ext ?_⟩
      exact Prod.ext ha.symm (Prod.ext hb.symm (Prod.ext hc.symm rfl))
    · refine ⟨.inl (⟨x.val.1, ha⟩, x.val.2.1, x.val.2.2.1), Subtype.ext ?_⟩
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
        (last_eq_of_quad_eq_zero p x.val ha x.property.2).symm))

theorem card_rankOne :
    Nat.card {x : Vertex p // x ≠ 0 ∧ quad p x = 0} = (p - 1) * (p ^ 2 + 1) := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective (rankOneParam p) (rankOneParam_bijective p)),
    Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ZMod.card]
  ring

theorem degree_zero :
    (open Classical in (hermitianGraph p).degree 0 = (p - 1) * (p ^ 2 + 1)) := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
  trans Nat.card {x : Vertex p // x ≠ 0 ∧ quad p x = 0}
  · exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      simp only [SimpleGraph.mem_neighborSet, adj_iff, zero_sub, quad_neg, ne_comm]))
  · exact card_rankOne p

theorem regular :
    (open Classical in (hermitianGraph p).IsRegularOfDegree ((p - 1) * (p ^ 2 + 1))) := by
  classical
  intro x
  have h := (translateIso p x).degree_eq 0
  change (hermitianGraph p).degree (0 + x) = (hermitianGraph p).degree 0 at h
  rw [zero_add] at h
  exact h.trans (degree_zero p)

end ExplicitRIP.Hfsrg
