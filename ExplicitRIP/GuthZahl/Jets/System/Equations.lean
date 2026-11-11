/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.System.Minors

/-!
# Integer equations for two jet directions

Six coordinates record two directions, and three further coordinates multiply
their minors. The final equation says that this linear combination is one.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl
namespace JetSystem


/-- Coordinates of the first direction in the nine-variable witness. -/
def firstDirectionIndex (i : Fin 3) : Fin 9 := i.castAdd 6

/-- Coordinates of the second direction in the nine-variable witness. -/
def secondDirectionIndex (i : Fin 3) : Fin 9 := (i.castAdd 3).natAdd 3

/-- Coordinates of the three minor multipliers. -/
def multiplierIndex (i : Fin 3) : Fin 9 := (i.natAdd 3).natAdd 3

/-- The degree-`j` directional coefficient as a polynomial over the integers. -/
noncomputable def directionPolynomial (r : ℕ) (d : Fin 3 → Fin 9) (j : ℕ) :
    MvPolynomial (JetIndex r ⊕ Fin 9) ℤ :=
  ∑ a : JetIndex r, if (∑ i, (a.val i).val) = j then
    MvPolynomial.X (Sum.inl a) *
      ∏ i : Fin 3, MvPolynomial.X (Sum.inr (d i)) ^ (a.val i).val else 0

/-- The linear combination of the three minors, minus one. -/
noncomputable def independencePolynomial (r : ℕ) :
    MvPolynomial (JetIndex r ⊕ Fin 9) ℤ :=
  (∑ i : Fin 3, MvPolynomial.X (Sum.inr (multiplierIndex i)) *
    directionMinors
      (fun j => MvPolynomial.X (Sum.inr (firstDirectionIndex j)))
      (fun j => MvPolynomial.X (Sum.inr (secondDirectionIndex j))) i) - 1

theorem eval_directionPolynomial {r : ℕ} {K : Type*} [Field K]
    (J : JetIndex r → K) (y : Fin 9 → K) (d : Fin 3 → Fin 9) (j : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim J y)
      (directionPolynomial r d j) = jetDirectionCoefficient J (fun i => y (d i)) j := by
  unfold directionPolynomial jetDirectionCoefficient
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Sum.elim_inl,
      Sum.elim_inr, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_pow]
  · exact MvPolynomial.eval₂_zero _ _

theorem eval_directionMinors {r : ℕ} {K : Type*} [Field K]
    (J : JetIndex r → K) (y : Fin 9 → K) (i : Fin 3) :
    MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim J y)
      (directionMinors
        (fun j => MvPolynomial.X (Sum.inr (firstDirectionIndex j)))
        (fun j => MvPolynomial.X (Sum.inr (secondDirectionIndex j))) i) =
      directionMinors (fun j => y (firstDirectionIndex j))
        (fun j => y (secondDirectionIndex j)) i := by
  fin_cases i <;> simp [directionMinors]

theorem eval_independencePolynomial {r : ℕ} {K : Type*} [Field K]
    (J : JetIndex r → K) (y : Fin 9 → K) :
    MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim J y)
      (independencePolynomial r) =
      (∑ i : Fin 3, y (multiplierIndex i) *
        directionMinors (fun j => y (firstDirectionIndex j))
          (fun j => y (secondDirectionIndex j)) i) - 1 := by
  simp only [independencePolynomial, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    Sum.elim_inr, eval_directionMinors, MvPolynomial.eval₂_one]

/-- Two blocks of directional coefficients followed by the minor equation. -/
noncomputable def equations (r : ℕ) (i : Fin (2 * (r + 1) + 1)) :
    MvPolynomial (JetIndex r ⊕ Fin 9) ℤ :=
  if i.val < r + 1 then directionPolynomial r firstDirectionIndex i.val
  else if i.val < 2 * (r + 1) then
    directionPolynomial r secondDirectionIndex (i.val - (r + 1))
  else independencePolynomial r

theorem equations_first (r : ℕ) (j : Fin (r + 1)) :
    equations r ⟨j.val, by omega⟩ = directionPolynomial r firstDirectionIndex j.val := by
  simp only [equations, j.isLt, ite_true]

theorem equations_second (r : ℕ) (j : Fin (r + 1)) :
    equations r ⟨r + 1 + j.val, by omega⟩ =
      directionPolynomial r secondDirectionIndex j.val := by
  have hfirst : ¬ r + 1 + j.val < r + 1 := by omega
  have hsecond : r + 1 + j.val < 2 * (r + 1) := by omega
  simp only [equations, hfirst, ite_false, hsecond, ite_true,
    Nat.add_sub_cancel_left]

theorem equations_last (r : ℕ) :
    equations r ⟨2 * (r + 1), by omega⟩ = independencePolynomial r := by
  have hfirst : ¬ 2 * (r + 1) < r + 1 := by omega
  simp only [equations, hfirst, ite_false, lt_self_iff_false]

end JetSystem
end ExplicitRIP.GuthZahl

end
