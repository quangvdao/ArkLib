/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.MvPolynomial.TaylorReconstruction.WeightedMonicReduction

/-! Unequal coefficient weights, repeated monic reduction, and the unit modulus. -/

namespace WeightedMonicReductionTests
open CPoly CPoly.CMvPolynomial CPoly.TaylorReconstruction CompPoly

example (p h : CPolynomial (CMvPolynomial 2 ℚ)) (hh : h.monic)
    (hw : WeightedDegreeLE h h.natDegree) (L : ℕ) (hp : WeightedDegreeLE p L) :
    (fromCMvPolynomial (flattenLast (p.modByMonic h))).totalDegree ≤ L :=
  totalDegree_flattenLast_le _ (weightedDegreeLE_modByMonic p h hh hw hp)

/-- Execute successive cancellation and check the resulting parameter/final degree balance. -/
def run : IO Unit := do
  let t : CMvPolynomial 1 ℤ := X 0
  let z : CPolynomial (CMvPolynomial 1 ℤ) := CPolynomial.X
  let h := z ^ 2 + CPolynomial.C t * z + CPolynomial.C (t ^ 2 + 1)
  let p := z ^ 4
  let expected := CPolynomial.C (t ^ 3 + 2 * t) * z + CPolynomial.C (t ^ 2 + 1)
  let rem := p.modByMonic h
  unless h.monic && rem == expected && (flattenLast rem).totalDegree == 4 do
    throw (IO.userError "weighted monic remainder did not preserve the exact boundary degree")
  unless (p.modByMonic (1 : CPolynomial (CMvPolynomial 1 ℤ))) == 0 do
    throw (IO.userError "unit modulus did not reduce to zero")
  let constantParams : CPolynomial (CMvPolynomial 0 ℤ) := CPolynomial.X ^ 3 + 4
  unless (constantParams.modByMonic (CPolynomial.X + 1)) == 3 do
    throw (IO.userError "zero-parameter monic reduction failed")

end WeightedMonicReductionTests
