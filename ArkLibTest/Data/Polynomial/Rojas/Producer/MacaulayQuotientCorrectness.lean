/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotientCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Compile-time checks for dense Macaulay quotient degree bounds. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayQuotientCorrectnessTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

example : (extraneousFactor twoRoots).totalDegree ≤
    (extraneousIndices twoRoots).length :=
  extraneousFactor_totalDegree_le_minorSize twoRoots

example {quotient : Parameters 2 F}
    (hquotient : macaulayQuotient? twoRoots = some quotient) :
    quotient.totalDegree ≤ (basis twoRoots).length :=
  macaulayQuotient_totalDegree_le_matrixSize hquotient

#print axioms extraneousFactor_totalDegree_le_minorSize
#print axioms extraneousFactor_parameterDegree_le_minorSize
#print axioms macaulayQuotient_totalDegree_le_matrixSize
#print axioms macaulayQuotient_parameterDegree_le_matrixSize

end RojasMacaulayQuotientCorrectnessTests
