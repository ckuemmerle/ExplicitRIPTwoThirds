/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Guth–Zahl line route: definitions for the components branch

A finite family of lines is partitioned according to whether a line lies on
exactly one irreducible factor or on several factors.

* `uniqueFactorLines`
* `multipleFactorLines`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

open Classical in
noncomputable def uniqueFactorLines {K : Type*} [Field K] {m : ℕ}
    (Ls : Finset (Line K)) (F : Fin m → Poly K) (i : Fin m) : Finset (Line K) :=
  Ls.filter (fun L => LineOn (F i) L ∧ ∀ j, j ≠ i → ¬ LineOn (F j) L)

open Classical in
noncomputable def multipleFactorLines {K : Type*} [Field K] {m : ℕ}
    (Ls : Finset (Line K)) (F : Fin m → Poly K) : Finset (Line K) :=
  Ls.filter (fun L => ∃ i j, i ≠ j ∧ LineOn (F i) L ∧ LineOn (F j) L)

end ExplicitRIP.GuthZahl

end
