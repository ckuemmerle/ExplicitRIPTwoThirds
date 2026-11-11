/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Algebra.NormPolynomial

/-!
# Norm forms of irreducible cubics

For any monic irreducible cubic over a field, the norm of its power-basis coordinates
is homogeneous of degree three and vanishes only at the zero coordinate triple.
-/

@[expose] public section

noncomputable section

namespace ExplicitRIP.NormForm

open Polynomial

variable {K : Type*} [Field K]

/-- The element with the given coordinates in `1, root f, root f ^ 2`. -/
def value (f : Polynomial K) (w : K × K × K) : AdjoinRoot f :=
  AdjoinRoot.of f w.1 + AdjoinRoot.of f w.2.1 * AdjoinRoot.root f +
    AdjoinRoot.of f w.2.2 * AdjoinRoot.root f ^ 2

/-- The degree-at-most-two polynomial representing a coordinate triple. -/
def coordinatePolynomial (w : K × K × K) : Polynomial K :=
  C w.2.2 * X ^ 2 + C w.2.1 * X + C w.1

theorem value_eq_mk (f : Polynomial K) (w : K × K × K) :
    value f w = AdjoinRoot.mk f (coordinatePolynomial w) := by
  simp only [value, coordinatePolynomial, map_add, map_mul, map_pow, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X]
  ring

theorem coordinatePolynomial_eq_zero_iff (w : K × K × K) :
    coordinatePolynomial w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    have h₀ := congrArg (fun q : Polynomial K => q.coeff 0) hw
    have h₁ := congrArg (fun q : Polynomial K => q.coeff 1) hw
    have h₂ := congrArg (fun q : Polynomial K => q.coeff 2) hw
    norm_num only [coordinatePolynomial, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X,
      coeff_C, coeff_zero, ite_true, ite_false, add_zero, zero_add] at h₀ h₁ h₂
    exact Prod.ext h₀ (Prod.ext h₁ h₂)
  · rintro rfl
    simp only [coordinatePolynomial, Prod.fst_zero, Prod.snd_zero, C_0, zero_mul, add_zero]

/-- A nonzero quadratic cannot become zero modulo a monic cubic. -/
theorem value_ne_zero (f : Polynomial K) (hm : f.Monic) (hd : f.natDegree = 3)
    (w : K × K × K) (hw : w ≠ 0) : value f w ≠ 0 := by
  rw [value_eq_mk]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt hm
  · exact fun h => hw ((coordinatePolynomial_eq_zero_iff w).mp h)
  · have hdeg : (coordinatePolynomial w).natDegree ≤ 2 := natDegree_quadratic_le
    rw [hd]
    omega

theorem value_smul (f : Polynomial K) (c : K) (w : K × K × K) :
    value f (c • w) = algebraMap K (AdjoinRoot f) c * value f w := by
  simp only [value, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul,
    AdjoinRoot.algebraMap_eq]
  ring

/-- Scaling and nonvanishing of the cubic norm. -/
theorem norm_form_spec (f : Polynomial K) (hm : f.Monic) (hi : Irreducible f)
    (hd : f.natDegree = 3) :
    (∀ (c : K) (w : K × K × K),
      Algebra.norm K (value f (c • w)) = c ^ 3 * Algebra.norm K (value f w)) ∧
    ∀ w : K × K × K, w ≠ 0 → Algebra.norm K (value f w) ≠ 0 := by
  let : Fact (Irreducible f) := ⟨hi⟩
  let : Module.Free K (AdjoinRoot f) := hm.free_adjoinRoot
  let : Module.Finite K (AdjoinRoot f) := hm.finite_adjoinRoot
  have hdim : Module.finrank K (AdjoinRoot f) = 3 := by
    rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, hd]
  constructor
  · intro c w
    rw [value_smul, map_mul, Algebra.norm_algebraMap, hdim]
  · intro w hw
    exact Algebra.norm_ne_zero_iff.mpr (value_ne_zero f hm hd w hw)

/-- A monic cubic has the specified power basis indexed by `Fin 3`. -/
theorem exists_power_basis (f : Polynomial K) (hm : f.Monic) (hd : f.natDegree = 3) :
    ∃ b : Module.Basis (Fin 3) K (AdjoinRoot f),
      ∀ i : Fin 3, b i = AdjoinRoot.root f ^ (i : ℕ) := by
  refine ⟨(AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hd), ?_⟩
  intro i
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The norm in power-basis coordinates is represented by a homogeneous cubic polynomial. -/
theorem exists_norm_polynomial (f : Polynomial K) (hm : f.Monic) (hd : f.natDegree = 3) :
    ∃ F : MvPolynomial (Fin 3) K,
      F.IsHomogeneous 3 ∧ F.totalDegree = 3 ∧
        ∀ w : K × K × K,
          MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = Algebra.norm K (value f w) := by
  obtain ⟨b, _⟩ := exists_power_basis f hm hd
  let x : Fin 3 → AdjoinRoot f := ![1, AdjoinRoot.root f, AdjoinRoot.root f ^ 2]
  let F := NormPolynomial.normPolynomial b x
  have hev (w : K × K × K) :
      MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = Algebra.norm K (value f w) := by
    simpa only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Algebra.smul_def, mul_one, AdjoinRoot.algebraMap_eq, value] using
      NormPolynomial.eval_normPolynomial b x w
  have hhom : F.IsHomogeneous 3 := NormPolynomial.normPolynomial_isHomogeneous b x
  have hone : MvPolynomial.eval ![1, 0, 0] F = 1 := by
    simpa only [value, map_one, map_zero, zero_mul, add_zero] using hev (1, 0, 0)
  have hne : F ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hone
    exact zero_ne_one hone
  exact ⟨F, hhom, hhom.totalDegree hne, hev⟩

/-- Field, power basis, cubic polynomial, scaling, and nonvanishing for every irreducible cubic. -/
theorem cubic_norm_spec (f : Polynomial K) (hm : f.Monic) (hi : Irreducible f)
    (hd : f.natDegree = 3) :
    IsField (AdjoinRoot f) ∧
      (∃ b : Module.Basis (Fin 3) K (AdjoinRoot f),
        ∀ i : Fin 3, b i = AdjoinRoot.root f ^ (i : ℕ)) ∧
      (∃ F : MvPolynomial (Fin 3) K,
        F.IsHomogeneous 3 ∧ F.totalDegree = 3 ∧
          ∀ w : K × K × K,
            MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = Algebra.norm K (value f w)) ∧
      (∀ (c : K) (w : K × K × K),
        Algebra.norm K (value f (c • w)) = c ^ 3 * Algebra.norm K (value f w)) ∧
      ∀ w : K × K × K, w ≠ 0 → Algebra.norm K (value f w) ≠ 0 := by
  let : Fact (Irreducible f) := ⟨hi⟩
  exact ⟨Field.toIsField _, exists_power_basis f hm hd,
    exists_norm_polynomial f hm hd, norm_form_spec f hm hi hd⟩

end ExplicitRIP.NormForm

end

end
