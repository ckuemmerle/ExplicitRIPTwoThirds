/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Raw
public import ExplicitRIP.Relative.GuthZahl.Boundary

/-!
# The Guth–Zahl structure theorem for Heisenberg lines

The positive-characteristic bound for chart lines supplies the premise of
`ExplicitRIP.Relative.GuthZahl.guthZahl_heisenberg_structure`. Its descent argument
then gives the structure theorem for Heisenberg lines.
-/

public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
/-- Guth–Zahl's structure theorem for the Heisenberg lines over `𝔽_p[i]`, `p ≡ 3 (mod 4)`. -/
theorem guthZahl_heisenberg_structure :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
        ∀ L : Finset (Zahl.HLine (ZMod p)),
          (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 →
          ∀ A : ℝ, C * Real.sqrt (L.card : ℝ) ≤ A →
            (Zahl.richCount (Zahl.chartImage L) 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
              (∃ normal : Point (Zahl.QuadraticExtension (ZMod p)), normal ≠ 0 ∧
                ∃ offset : Zahl.QuadraticExtension (ZMod p),
                  A ≤ (((Zahl.chartImage L).filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
              ∃ Q : Zahl.SplitQuadric (Zahl.QuadraticExtension (ZMod p)),
                A ≤ (((Zahl.chartImage L).filter (Zahl.quadricContains Q)).card : ℝ) :=
  ExplicitRIP.Relative.GuthZahl.guthZahl_heisenberg_structure
    guthZahl_algebraicallyClosed_charSquare_structure

end ExplicitRIP.GuthZahl

end
