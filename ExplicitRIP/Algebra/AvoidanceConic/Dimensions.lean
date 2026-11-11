/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Dimensions of bounded bivariate polynomial spaces

These finite-dimensional quotient bounds supply the algebraic intersection estimate used
for conic avoidance.
-/

@[expose] public section

namespace ExplicitRIP.Avconic
open MvPolynomial

abbrev Bivariate (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2) K
noncomputable abbrev DegreeSpace (K : Type*) [CommSemiring K] (M : ℕ) :=
  restrictTotalDegree (Fin 2) K M

lemma exponent_sum_two (n : Fin 2 →₀ ℕ) :
    n.sum (fun _ e => e) = n 0 + n 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

/-- Monomials of total degree at most `M`, indexed first by total degree and then
by the exponent of the first variable. -/
noncomputable def degreeIndexEquiv (M : ℕ) :
    {n : Fin 2 →₀ ℕ // n.sum (fun _ e => e) ≤ M} ≃
      (Σ t : Fin (M + 1), Fin (t.val + 1)) where
  toFun n := ⟨⟨n.val 0 + n.val 1, by
    have := n.property
    rw [exponent_sum_two] at this
    omega⟩, ⟨n.val 0, by change n.val 0 < n.val 0 + n.val 1 + 1; omega⟩⟩
  invFun t := ⟨Finsupp.equivFunOnFinite.symm ![t.2.val, t.1.val - t.2.val], by
    rw [exponent_sum_two]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have := t.1.isLt
    have := t.2.isLt
    omega⟩
  left_inv n := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv t := by
    obtain ⟨⟨t, ht⟩, ⟨i, hi⟩⟩ := t
    change i < t + 1 at hi
    have hsum : i + (t - i) = t := by omega
    simp only [Fin.isValue, Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val_zero,
      Matrix.cons_val_one, hsum, Sigma.mk.injEq, true_and]
    exact (Fin.heq_ext_iff (by omega)).mpr rfl

lemma degreeIndex_card (M : ℕ) :
    Fintype.card (Σ t : Fin (M + 1), Fin (t.val + 1)) = (M + 2).choose 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1)]
  simpa using Nat.sum_range_add_choose M 1

/-- The exact dimension of the bivariate polynomials of total degree at most `M`. -/
theorem finrank_degreeSpace (K : Type*) [Field K] (M : ℕ) :
    Module.finrank K (DegreeSpace K M) = (M + 2).choose 2 := by
  classical
  let e := degreeIndexEquiv M
  let : Fintype {n : Fin 2 →₀ ℕ // n.sum (fun _ e => e) ≤ M} := Fintype.ofEquiv _ e.symm
  let S : Set (Fin 2 →₀ ℕ) := {n | n.sum (fun _ e => e) ≤ M}
  let : Fintype S := Fintype.ofEquiv _ e.symm
  change Module.finrank K (restrictSupport K S) = _
  rw [Module.finrank_eq_card_basis (basisRestrictSupport K
    {n : Fin 2 →₀ ℕ | n.sum (fun _ e => e) ≤ M})]
  exact (Fintype.card_congr e).trans (degreeIndex_card M)

lemma twice_triangular (n : ℕ) : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

lemma triangular_difference (M a b : ℕ) (hM : a + b ≤ M) :
    (M + 2).choose 2 + (M - (a + b) + 2).choose 2 =
      (M - a + 2).choose 2 + (M - b + 2).choose 2 + a * b := by
  have h1 := twice_triangular M
  have h2 := twice_triangular (M - (a + b))
  have h3 := twice_triangular (M - a)
  have h4 := twice_triangular (M - b)
  have ha : M - a + a = M := by omega
  have hb : M - b + b = M := by omega
  have hab : M - (a + b) + (a + b) = M := by omega
  nlinarith

section Multiples
variable {K : Type*} [Field K]

/-- Multiples of `G` represented by a cofactor of the permitted total degree. -/
noncomputable def multiplesSpace (G : Bivariate K) (M : ℕ) : Submodule K (Bivariate K) :=
  (DegreeSpace K (M - G.totalDegree)).map (LinearMap.mulLeft K G)

lemma mem_multiplesSpace (G P : Bivariate K) (M : ℕ) :
    P ∈ multiplesSpace G M ↔
      ∃ A : Bivariate K, A.totalDegree ≤ M - G.totalDegree ∧ G * A = P := by
  simp [multiplesSpace, Submodule.mem_map, mem_restrictTotalDegree,
    LinearMap.mulLeft_apply]

theorem finrank_multiplesSpace (G : Bivariate K) (hG : G ≠ 0) (M : ℕ) :
    Module.finrank K (multiplesSpace G M) = (M - G.totalDegree + 2).choose 2 := by
  have hi : Function.Injective (LinearMap.mulLeft K G) := by
    intro x y h
    exact mul_left_cancel₀ hG h
  unfold multiplesSpace
  rw [← (Submodule.equivMapOfInjective (LinearMap.mulLeft K G) hi
    (DegreeSpace K (M - G.totalDegree))).finrank_eq]
  exact finrank_degreeSpace K _

lemma multiplesSpace_le_degreeSpace (G : Bivariate K) (M : ℕ)
    (hM : G.totalDegree ≤ M) : multiplesSpace G M ≤ DegreeSpace K M := by
  intro P hP
  obtain ⟨A, hA, rfl⟩ := (mem_multiplesSpace G P M).mp hP
  rw [mem_restrictTotalDegree]
  exact (totalDegree_mul G A).trans (by omega)

/-- Relatively prime bivariate polynomials have exactly the expected intersection
of their spaces of bounded-degree multiples. -/
theorem multiplesSpace_inf (G H : Bivariate K) (hG : G ≠ 0) (hH : H ≠ 0)
    (hrel : IsRelPrime G H) (M : ℕ) (hM : G.totalDegree + H.totalDegree ≤ M) :
    multiplesSpace G M ⊓ multiplesSpace H M = multiplesSpace (G * H) M := by
  ext P
  constructor
  · intro hP
    obtain ⟨A, hA, hAP⟩ := (mem_multiplesSpace G P M).mp hP.1
    obtain ⟨B, hB, hBP⟩ := (mem_multiplesSpace H P M).mp hP.2
    have hdiv : G ∣ H * B := by
      rw [hBP, ← hAP]
      exact dvd_mul_right G A
    obtain ⟨C, hC⟩ := hrel.dvd_of_dvd_mul_left hdiv
    apply (mem_multiplesSpace (G * H) P M).mpr
    refine ⟨C, ?_, ?_⟩
    · by_cases hC0 : C = 0
      · simp [hC0]
      · rw [hC, totalDegree_mul_of_isDomain hG hC0] at hB
        rw [totalDegree_mul_of_isDomain hG hH]
        omega
    · rw [← hBP, hC]
      ring
  · intro hP
    obtain ⟨C, hC, rfl⟩ := (mem_multiplesSpace (G * H) P M).mp hP
    rw [totalDegree_mul_of_isDomain hG hH] at hC
    constructor
    · apply (mem_multiplesSpace G ((G * H) * C) M).mpr
      refine ⟨H * C, ?_, by ring⟩
      exact (totalDegree_mul H C).trans (by omega)
    · apply (mem_multiplesSpace H ((G * H) * C) M).mpr
      refine ⟨G * C, ?_, by ring⟩
      exact (totalDegree_mul G C).trans (by omega)

/-- Exact dimension formula, stated additively to avoid truncated subtraction. -/
theorem finrank_multiplesSpace_sup (G H : Bivariate K) (hG : G ≠ 0) (hH : H ≠ 0)
    (hrel : IsRelPrime G H) (M : ℕ) (hM : G.totalDegree + H.totalDegree ≤ M) :
    Module.finrank K ↥(multiplesSpace G M ⊔ multiplesSpace H M) +
      G.totalDegree * H.totalDegree = (M + 2).choose 2 := by
  let : Module.Finite K (multiplesSpace G M) := by unfold multiplesSpace; infer_instance
  let : Module.Finite K (multiplesSpace H M) := by unfold multiplesSpace; infer_instance
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (multiplesSpace G M) (multiplesSpace H M)
  rw [multiplesSpace_inf G H hG hH hrel M hM,
    finrank_multiplesSpace (G * H) (mul_ne_zero hG hH),
    totalDegree_mul_of_isDomain hG hH,
    finrank_multiplesSpace G hG, finrank_multiplesSpace H hH] at hd
  have ht := triangular_difference M G.totalDegree H.totalDegree hM
  omega

/-- The truncated two-generator ideal, viewed inside the bounded-degree ambient
space rather than the full polynomial ring. -/
noncomputable def boundedIdealSpace (G H : Bivariate K) (M : ℕ) :
    Submodule K (DegreeSpace K M) :=
  (multiplesSpace G M ⊔ multiplesSpace H M).comap (DegreeSpace K M).subtype

lemma finrank_boundedIdealSpace (G H : Bivariate K) (M : ℕ)
    (hM : G.totalDegree + H.totalDegree ≤ M) :
    Module.finrank K (boundedIdealSpace G H M) =
      Module.finrank K ↥(multiplesSpace G M ⊔ multiplesSpace H M) := by
  have hle : multiplesSpace G M ⊔ multiplesSpace H M ≤ DegreeSpace K M :=
    sup_le (multiplesSpace_le_degreeSpace G M (by omega))
      (multiplesSpace_le_degreeSpace H M (by omega))
  have hm : (boundedIdealSpace G H M).map (DegreeSpace K M).subtype =
      multiplesSpace G M ⊔ multiplesSpace H M := by
    unfold boundedIdealSpace
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  have hf := Submodule.finrank_map_subtype_eq (DegreeSpace K M) (boundedIdealSpace G H M)
  rw [hm] at hf
  exact hf.symm

/-- The bounded-degree quotient by two relatively prime polynomials has exact
codimension equal to the product of their total degrees. -/
theorem finrank_quotient_boundedIdealSpace (G H : Bivariate K)
    (hG : G ≠ 0) (hH : H ≠ 0) (hrel : IsRelPrime G H) (M : ℕ)
    (hM : G.totalDegree + H.totalDegree ≤ M) :
    Module.finrank K (↥(DegreeSpace K M) ⧸ boundedIdealSpace G H M) =
      G.totalDegree * H.totalDegree := by
  have hq := (boundedIdealSpace G H M).finrank_quotient_add_finrank
  rw [finrank_degreeSpace, finrank_boundedIdealSpace G H M hM] at hq
  have hd := finrank_multiplesSpace_sup G H hG hH hrel M hM
  omega

/-- A linear map vanishing on all multiples of the generators vanishes on their
truncated ideal inside the bounded-degree ambient space. -/
lemma boundedIdealSpace_le_ker_comp {V : Type*} [AddCommGroup V] [Module K V]
    (G H : Bivariate K) (M : ℕ) (f : Bivariate K →ₗ[K] V)
    (hG : ∀ A, f (G * A) = 0) (hH : ∀ B, f (H * B) = 0) :
    boundedIdealSpace G H M ≤ LinearMap.ker (f.comp (DegreeSpace K M).subtype) := by
  intro P hP
  change P.val ∈ multiplesSpace G M ⊔ multiplesSpace H M at hP
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hP
  obtain ⟨A, _, hA⟩ := (mem_multiplesSpace G a M).mp ha
  obtain ⟨B, _, hB⟩ := (mem_multiplesSpace H b M).mp hb
  change f P.val = 0
  rw [← hab, ← hA, ← hB, map_add, hG A, hH B, add_zero]

/-- A surjective family of linear conditions that vanishes on the two-generator
ideal can have no more coordinates than its codimension. -/
theorem finrank_target_le_degree_product {V : Type*} [AddCommGroup V] [Module K V]
    (G H : Bivariate K) (hG : G ≠ 0) (hH : H ≠ 0) (hrel : IsRelPrime G H)
    (M : ℕ) (hM : G.totalDegree + H.totalDegree ≤ M)
    (f : DegreeSpace K M →ₗ[K] V) (hf : Function.Surjective f)
    (hker : boundedIdealSpace G H M ≤ LinearMap.ker f) :
    Module.finrank K V ≤ G.totalDegree * H.totalDegree := by
  have hq := (boundedIdealSpace G H M).finrank_quotient_add_finrank
  rw [finrank_quotient_boundedIdealSpace G H hG hH hrel M hM] at hq
  have hn := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hn
  have hle := Submodule.finrank_mono hker
  omega

end Multiples
end ExplicitRIP.Avconic
