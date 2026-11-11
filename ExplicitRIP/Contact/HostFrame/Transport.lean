/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.Transport
public import ExplicitRIP.HermitianForms.Anchors.HostFrame

/-!
# The contact graph and its tight frame

Transport the Hermitian-coordinate SRG parameters and tight frame along the sphere equivalence
to the graph `VO₄⁻(p)` in the coordinates of [KM, Section 4.1]. The resulting parameters and frame
are those of [KM, Section 3, (13)].
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace ExplicitRIP.Contact.HostFrame

/-- Strong regularity is invariant under a graph isomorphism. -/
theorem isSRGWith_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {n k l u : ℕ} (h : (open Classical in G.IsSRGWith n k l u)) :
    (open Classical in H.IsSRGWith n k l u) := by
  classical
  have hcommon (v w : V) :
      Fintype.card (H.commonNeighbors (e v) (e w)) =
        Fintype.card (G.commonNeighbors v w) := by
    symm
    apply Fintype.card_congr
    refine e.toEquiv.subtypeEquiv ?_
    intro x
    exact (and_congr e.map_adj_iff e.map_adj_iff).symm
  refine ⟨(Fintype.card_congr e.toEquiv).symm.trans h.card, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    exact (e.degree_eq v).trans (h.regular.degree_eq v)
  · intro x y hxy
    obtain ⟨v, rfl⟩ := e.surjective x
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [hcommon]
    exact h.of_adj v w (e.map_adj_iff.mp hxy)
  · intro x y hne hxy
    obtain ⟨v, rfl⟩ := e.surjective x
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [hcommon]
    exact h.of_not_adj (fun hvw => hne (congrArg e hvw))
      (fun hvw => hxy (e.map_adj_iff.mpr hvw))

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem isSRGWith :
    (open Classical in
      (contactGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
        (p * (p - 1))) :=
  isSRGWith_of_iso (graphIso p) (ExplicitRIP.HostFrame.isSRGWith p)

omit [Fact (p % 4 = 3)] in
theorem dimension_pos : 0 < (p - 1) * (p ^ 2 + 1) :=
  Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt) (by omega)

omit [Fact (p % 4 = 3)] in
theorem scale_pos : 0 < (p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hm : 0 < (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast dimension_pos p
  exact div_pos (pow_pos hp _) hm

theorem hostGram_apply_self (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    hostGram ℝ p x x = 1 := by
  rw [hostGram_eq_submatrix]
  exact ExplicitRIP.HostFrame.hostGram_apply_self p _

/-- Reindexing the columns preserves both Gram identities. -/
theorem exists_tight_frame :
    ∃ B : Matrix (Fin ((p - 1) * (p ^ 2 + 1)))
        (ZMod p × ZMod p × ZMod p × ZMod p) ℝ,
      Bᵀ * B = hostGram ℝ p ∧ (∀ x, ∑ r, B r x ^ 2 = 1) ∧
      B * Bᵀ = ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) •
        (1 : Matrix (Fin ((p - 1) * (p ^ 2 + 1)))
          (Fin ((p - 1) * (p ^ 2 + 1))) ℝ) := by
  classical
  obtain ⟨B, hB, hBB⟩ := (ExplicitRIP.Hermitian.hermitian_graph_frame.1 p).2
  let C := B.submatrix id (sphereMap p).symm
  have hC : Cᵀ * C = hostGram ℝ p := by
    rw [hostGram_eq_submatrix, ← hB]
    exact (Matrix.submatrix_mul Bᵀ B (sphereMap p).symm id (sphereMap p).symm
      Function.bijective_id).symm
  refine ⟨C, hC, ?_, ?_⟩
  · intro x
    have hx := congrArg (fun M => M x x) hC
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two,
      hostGram_apply_self] using hx
  · simpa only [C, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id] using hBB

theorem hostGram_mul_self :
    hostGram ℝ p * hostGram ℝ p =
      ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) • hostGram ℝ p := by
  classical
  obtain ⟨B, hB, _, hBB⟩ := exists_tight_frame p
  rw [← hB]
  calc
    (Bᵀ * B) * (Bᵀ * B) = Bᵀ * (B * Bᵀ) * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem hostGram_rank : (hostGram ℝ p).rank = (p - 1) * (p ^ 2 + 1) := by
  classical
  obtain ⟨B, hB, _, hBB⟩ := exists_tight_frame p
  rw [← hB, Matrix.rank_transpose_mul_self, ← Matrix.rank_self_mul_transpose B, hBB,
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
      (scale_pos p).ne'), Matrix.rank_one, Fintype.card_fin]

end ExplicitRIP.Contact.HostFrame
