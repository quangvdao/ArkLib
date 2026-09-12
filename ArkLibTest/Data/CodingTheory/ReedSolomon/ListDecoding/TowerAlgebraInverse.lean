/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Materialize

/-!
# Executable tower-inversion regressions

These examples exercise the actual multiplication-matrix solver.  In particular the final example
uses `U^2 + 1` over `ℚ`, whose base modulus has no rational root; the algorithm therefore cannot be
secretly relying on enumeration of geometric points.
-/

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly

private abbrev Base := CPolynomial ℚ
private abbrev Nested := CPolynomial Base

private def U : Base := CPolynomial.X
private def V : Nested := CPolynomial.X
private def liftBase (p : Base) : Nested := CPolynomial.C p

private def splitBase : Base := U * (U - 1)
private def extensionOnlyBase : Base := U ^ 2 + 1

/-- A scalar unit is inverted constructively in the full nested quotient. -/
example : inverseRepresentative? extensionOnlyBase V (2 : Nested) = some (1 / 2 : Nested) := by
  decide +kernel

/-- A genuine zero divisor on the two-component base is rejected explicitly. -/
example : inverseRepresentative? splitBase V (liftBase U) = none := by
  decide +kernel

/-- The solver handles a unit whose values differ on the two base components. -/
example :
    inverseRepresentative? splitBase V (liftBase (U + 1)) =
      some (liftBase (1 - CPolynomial.C (1 / 2 : ℚ) * U)) := by
  decide +kernel

/-- An extension-only base modulus is handled without extracting either quadratic root. -/
example :
    inverseRepresentative? extensionOnlyBase V (liftBase U) = some (liftBase (-U)) := by
  decide +kernel

/-- Materialization preserves slot order and reduces numerator times the computed inverse. -/
example :
    let r : TowerRepresentation (F := ℚ) :=
      { modulus := extensionOnlyBase, fiber := V, coefficients := [] }
    Option.map TowerRepresentation.coefficients
      (materializeCoefficients? r (liftBase U) [1, liftBase U]) =
        some [liftBase (-U), 1] := by
  decide +kernel

end ReedSolomon.ListDecoding.TowerAlgebra
