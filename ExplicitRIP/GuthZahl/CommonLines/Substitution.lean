/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Substitution

/-!
# Linear substitutions and degree bounds

Substituting polynomials of degree at most one does not increase total degree.
The linear pullback of a polynomial preserves evaluation and, for an invertible
linear map over an infinite field, preserves nonzeroness and relative primality.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.CommonLines

open scoped BigOperators

/-- Pull a polynomial back along a linear map of the ambient point space. -/
noncomputable def pullback {K : Type*} [Field K]
    (e : Point K →ₗ[K] Point K) : Poly K →+* Poly K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => ∑ j : Fin 3, MvPolynomial.C (e (Pi.single j 1) i) * MvPolynomial.X j)

theorem eval_pullback {K : Type*} [Field K]
    (e : Point K →ₗ[K] Point K) (f : Poly K) (x : Point K) :
    MvPolynomial.eval x (pullback e f) = MvPolynomial.eval (e x) f := by
  change MvPolynomial.eval x (f.eval₂ MvPolynomial.C _) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun u => MvPolynomial.eval u f)
  funext i
  have hx : ∑ j : Fin 3, x j • Pi.single j (1 : K) = x := by
    ext k
    simp [Pi.single_apply]
  have he := congrFun (congrArg e hx) i
  simpa only [Function.comp_apply, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm] using he

theorem totalDegree_pullback_le {K : Type*} [Field K]
    (e : Point K →ₗ[K] Point K) (f : Poly K) :
    (pullback e f).totalDegree ≤ f.totalDegree := by
  change (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (RingHom.id K)) _ f).totalDegree ≤ _
  rw [← Nat.mul_one f.totalDegree]
  apply totalDegree_eval₂_le
  intro i
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem pullback_symm_pullback {K : Type*} [Field K] [Infinite K]
    (e : Point K ≃ₗ[K] Point K) (f : Poly K) :
    pullback e.symm.toLinearMap (pullback e.toLinearMap f) = f := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_pullback, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem pullback_ne_zero {K : Type*} [Field K] [Infinite K]
    (e : Point K ≃ₗ[K] Point K) {f : Poly K} (hf : f ≠ 0) :
    pullback e.toLinearMap f ≠ 0 := by
  intro h
  apply hf
  rw [← pullback_symm_pullback e f, h, map_zero]

theorem totalDegree_pullback {K : Type*} [Field K] [Infinite K]
    (e : Point K ≃ₗ[K] Point K) (f : Poly K) :
    (pullback e.toLinearMap f).totalDegree = f.totalDegree := by
  apply Nat.le_antisymm (totalDegree_pullback_le e.toLinearMap f)
  have h := totalDegree_pullback_le e.symm.toLinearMap (pullback e.toLinearMap f)
  rwa [pullback_symm_pullback] at h

theorem isRelPrime_pullback {K : Type*} [Field K] [Infinite K]
    (e : Point K ≃ₗ[K] Point K) {f g : Poly K} (h : IsRelPrime f g) :
    IsRelPrime (pullback e.toLinearMap f) (pullback e.toLinearMap g) := by
  intro d hd₁ hd₂
  have hd₁' := map_dvd (pullback e.symm.toLinearMap) hd₁
  have hd₂' := map_dvd (pullback e.symm.toLinearMap) hd₂
  rw [pullback_symm_pullback] at hd₁' hd₂'
  have hu := (h hd₁' hd₂').map (pullback e.toLinearMap)
  have hi := pullback_symm_pullback e.symm d
  change pullback e.toLinearMap (pullback e.symm.toLinearMap d) = d at hi
  rwa [hi] at hu

end ExplicitRIP.GuthZahl.CommonLines
end
