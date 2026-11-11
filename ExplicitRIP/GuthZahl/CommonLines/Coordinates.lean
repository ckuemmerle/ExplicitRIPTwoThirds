/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.CommonLines.LineBasics

/-!
# Coordinates separating a finite family of lines

The first coordinate functional is chosen from a quadratic one-parameter
family to be nonzero on every line direction. Normalize the parametrizations
with respect to it. A second shear separates the pairs of normalized base
points and directions. Both choices only avoid finitely many polynomial roots.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.CommonLines

open scoped BigOperators

theorem exists_forall_polynomial_eval_ne_zero {K ι : Type*} [Field K] [Infinite K]
    [Finite ι] (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0) :
    ∃ t, ∀ i, (p i).eval t ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  have hprod : ∏ i, p i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hp i
  have hex : ∃ t, (∏ i, p i).eval t ≠ 0 := by
    by_contra! h
    apply hprod
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_zero] using h t
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, fun i => ?_⟩
  rw [Polynomial.eval_prod] at ht
  exact Finset.prod_ne_zero_iff.mp ht i (Finset.mem_univ _)

/-- A one-parameter family of transverse coordinate functionals. -/
def transverseCoord {K : Type*} [Field K] (s : K) : Point K →ₗ[K] K where
  toFun x := x 1 + s * x 0 + s ^ 2 * x 2
  map_add' x y := by dsimp; ring
  map_smul' t x := by dsimp; ring

/-- A shear of the remaining projected coordinate. -/
def separatingCoord {K : Type*} [Field K] (c : K) : Point K →ₗ[K] K where
  toFun x := x 2 + c * x 0
  map_add' x y := by dsimp; ring
  map_smul' t x := by dsimp; ring

/-- The two coordinate functionals extend to an explicit linear equivalence. -/
def shearCoordinates {K : Type*} [Field K] (s c : K) : Point K ≃ₗ[K] Point K where
  toFun x := ![x 0, transverseCoord s x, separatingCoord c x]
  invFun y := ![y 0, y 1 - s * y 0 - s ^ 2 * (y 2 - c * y 0), y 2 - c * y 0]
  left_inv x := by
    ext i
    fin_cases i <;> simp [transverseCoord, separatingCoord]
    ring
  right_inv y := by
    ext i
    fin_cases i <;> simp [transverseCoord, separatingCoord]
    ring
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' t x := by ext i; fin_cases i <;> simp

theorem exists_separating_coordinates {K : Type*} [Field K] [Infinite K]
    (Ls : Finset (Line K)) :
    ∃ e : Point K ≃ₗ[K] Point K, ∃ a v : Ls → Point K,
      (∀ L, a L ∈ L.val.val ∧ v L ∈ L.val.val.direction ∧
        e (a L) 1 = 0 ∧ e (v L) 1 = 1) ∧
      Function.Injective (fun L => (e (a L) 2, e (v L) 2)) := by
  classical
  choose b hb using fun L : Ls => line_nonempty L.val
  choose w hw hw0 using fun L : Ls => exists_line_direction_ne_zero L.val
  let P : Ls → Polynomial K := fun L => Polynomial.C (w L 1) +
    Polynomial.C (w L 0) * Polynomial.X + Polynomial.C (w L 2) * Polynomial.X ^ 2
  have hP : ∀ L, P L ≠ 0 := by
    intro L h
    apply hw0 L
    ext i
    fin_cases i
    · have hi := congrArg (fun p : Polynomial K => p.coeff 1) h
      simpa [P] using hi
    · have hi := congrArg (fun p : Polynomial K => p.coeff 0) h
      simpa [P] using hi
    · have hi := congrArg (fun p : Polynomial K => p.coeff 2) h
      simpa [P] using hi
  obtain ⟨s, hs⟩ := exists_forall_polynomial_eval_ne_zero P hP
  have hs' : ∀ L, transverseCoord s (w L) ≠ 0 := by
    intro L
    have h := hs L
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow] at h
    change w L 1 + s * w L 0 + s ^ 2 * w L 2 ≠ 0
    rwa [mul_comm (w L 0) s, mul_comm (w L 2) (s ^ 2)] at h
  let v : Ls → Point K := fun L => (transverseCoord s (w L))⁻¹ • w L
  let a : Ls → Point K := fun L => b L - transverseCoord s (b L) • v L
  have hv : ∀ L, v L ∈ L.val.val.direction := fun L =>
    L.val.val.direction.smul_mem _ (hw L)
  have hv₁ : ∀ L, transverseCoord s (v L) = 1 := by
    intro L
    simp only [v, map_smul, smul_eq_mul, inv_mul_cancel₀ (hs' L)]
  have hv0 : ∀ L, v L ≠ 0 := by
    intro L h
    have hi := hv₁ L
    rw [h, map_zero] at hi
    exact zero_ne_one hi
  have ha : ∀ L, a L ∈ L.val.val := by
    intro L
    have hm := line_add_smul_mem L.val (hb L) (hv L) (-transverseCoord s (b L))
    simpa only [a, neg_smul, sub_eq_add_neg] using hm
  have ha₁ : ∀ L, transverseCoord s (a L) = 0 := by
    intro L
    simp only [a, map_sub, map_smul, hv₁ L, smul_eq_mul, mul_one, sub_self]
  have hav : ∀ i j : Ls, a i = a j → v i = v j → i = j := by
    intro i j haij hvij
    apply Subtype.ext
    apply line_eq_of_point_of_direction i.val j.val (ha i) _ (hv i) _ (hv0 i)
    · simpa only [haij] using ha j
    · simpa only [hvij] using hv j
  let I := {ij : Ls × Ls // ij.1 ≠ ij.2}
  let d : I → Point K := fun ij =>
    if a ij.val.1 = a ij.val.2 then v ij.val.1 - v ij.val.2 else a ij.val.1 - a ij.val.2
  have hd : ∀ ij, d ij ≠ 0 := by
    intro ij h
    by_cases haij : a ij.val.1 = a ij.val.2
    · have hvij : v ij.val.1 = v ij.val.2 := by
        simpa only [d, ite_eq_left haij, sub_eq_zero] using h
      exact ij.property (hav _ _ haij hvij)
    · exact haij (by simpa only [d, ite_eq_right haij, sub_eq_zero] using h)
  have hd₁ : ∀ ij, transverseCoord s (d ij) = 0 := by
    intro ij
    dsimp only [d]
    split_ifs <;> simp only [map_sub, hv₁, ha₁, sub_self]
  let Q : I → Polynomial K := fun ij =>
    Polynomial.C (d ij 2) + Polynomial.C (d ij 0) * Polynomial.X
  have hQ : ∀ ij, Q ij ≠ 0 := by
    intro ij h
    have h₀ : d ij 0 = 0 := by
      have hi := congrArg (fun p : Polynomial K => p.coeff 1) h
      simpa [Q] using hi
    have h₂ : d ij 2 = 0 := by
      have hi := congrArg (fun p : Polynomial K => p.coeff 0) h
      simpa [Q] using hi
    have h₁ : d ij 1 = 0 := by
      have hi := hd₁ ij
      simpa only [transverseCoord, LinearMap.coe_mk, AddHom.coe_mk, h₀, h₂,
        mul_zero, add_zero] using hi
    apply hd ij
    ext k
    fin_cases k
    · exact h₀
    · exact h₁
    · exact h₂
  obtain ⟨c, hc⟩ := exists_forall_polynomial_eval_ne_zero Q hQ
  have hc' : ∀ ij, separatingCoord c (d ij) ≠ 0 := by
    intro ij
    have h := hc ij
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at h
    change d ij 2 + c * d ij 0 ≠ 0
    rwa [mul_comm (d ij 0) c] at h
  refine ⟨shearCoordinates s c, a, v, ?_, ?_⟩
  · intro L
    exact ⟨ha L, hv L, ha₁ L, hv₁ L⟩
  · intro i j hij
    by_contra hne
    have hm₁ : separatingCoord c (a i) = separatingCoord c (a j) := congrArg Prod.fst hij
    have hm₂ : separatingCoord c (v i) = separatingCoord c (v j) := congrArg Prod.snd hij
    apply hc' ⟨(i, j), hne⟩
    dsimp only [d]
    split_ifs <;> simp only [map_sub, hm₁, hm₂, sub_self]

end ExplicitRIP.GuthZahl.CommonLines
end
