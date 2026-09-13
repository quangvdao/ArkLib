/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoundedGCD.ComponentRemoval
import Mathlib.Algebra.Field.ZMod

open CPoly CPoly.CMvPolynomial CompPoly
open CPoly.CMvPolynomial.BoundedGCD.ComponentRemoval

namespace ComponentRemovalTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Execute common-factor removal on two meeting components and check root coverage at every
separant-regular point of the finite affine plane. -/
def run : IO Unit := do
  let x : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 0
  let y : CMvPolynomial 2 (ZMod 5) := CMvPolynomial.X 1
  let discarded := y + x + 1
  let regular := y + 1
  let support := discarded * regular
  let separant := discarded * (y + 2)
  let some data := run? support separant
    | throw (IO.userError "common-factor removal rejected the meeting-component fixture")
  unless data.leftQuotient * data.divisor == support do
    throw (IO.userError "component removal did not reconstruct the support")
  unless data.rightQuotient * data.divisor == separant do
    throw (IO.userError "discarded component does not divide the separant")
  for u in [0, 1, 2, 3, 4] do
    for v in [0, 1, 2, 3, 4] do
      let point : Fin 2 → ZMod 5 := ![u, v]
      if separant.eval point != 0 then
        unless (data.leftQuotient.eval point == 0) == (support.eval point == 0) do
          throw (IO.userError "regular-root coverage failed at a separant-regular point")

#print axioms discarded_ne_zero
#print axioms reconstruction
#print axioms discarded_separant_identity
#print axioms regular_ne_zero
#print axioms regular_totalDegree_le
#print axioms eval₂_regular_iff

end ComponentRemovalTests
