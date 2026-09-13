/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulayCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time checks for dense Macaulay basis, row, and degree theorems. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay

namespace RojasDenseMacaulayCorrectnessTests

abbrev F := ZMod 7

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

example : (weakCompositions 3 2).length = 6 := by decide

example : (basis twoRoots).Nodup := basis_nodup twoRoots

example (i : Fin (basis twoRoots).length) :
    rowEquation? (equationDegree twoRoots) (basis twoRoots)[i] ≠ none :=
  rowEquation?_basis_ne_none twoRoots i

example (i j : Fin (basis twoRoots).length) :
    matrix twoRoots i j =
      rowEntry (rowMultiplier
        (equationDegree twoRoots (basisRowEquation twoRoots i))
        (basisRowEquation twoRoots i) (basis twoRoots)[i])
        (basis twoRoots)[j]
        (homogeneousTerms twoRoots (basisRowEquation twoRoots i)) :=
  matrix_apply twoRoots i j

example (i j : Fin (basis twoRoots).length) :
    (fromCMvPolynomial (matrix twoRoots i j)).totalDegree ≤ 1 :=
  matrix_entry_totalDegree_le_one twoRoots i j

example : (characteristic twoRoots).totalDegree ≤ (basis twoRoots).length :=
  characteristic_totalDegree_le_matrixSize twoRoots

#print axioms mem_weakCompositions_iff_totalDegree
#print axioms weakCompositions_nodup
#print axioms rowEquation?_basis_ne_none
#print axioms rowEquation?_eq_some_least
#print axioms rowEquation?_basis_eq_some
#print axioms matrix_apply_of_rowEquation?_eq_some
#print axioms matrix_apply
#print axioms matrix_entry_totalDegree_le_one
#print axioms characteristic_totalDegree_le_matrixSize
#print axioms characteristic_parameterDegree_le_matrixSize

end RojasDenseMacaulayCorrectnessTests
