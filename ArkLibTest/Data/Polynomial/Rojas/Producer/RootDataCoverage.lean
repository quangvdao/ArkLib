/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.RootDataCoverage
import Mathlib.Algebra.Field.ZMod

/-! Theorem and runtime checks for input-derived safe-map common-root data. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas
open ArkLib.Rojas.Producer
open ArkLib.UnivariateRepresentation

namespace RojasRootDataCoverageTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

example {perturbation : CMvPolynomial 3 F}
    (hcoverage : FactorizationCoverage.CoversNonsingularAffineRoots twoRoots perturbation)
    (point : Fin 2 → F)
    (hpoint : FactorizationCoverage.IsNonsingularAffineRoot twoRoots point)
    (ε : F)
    (hsafe : SafeSubresultantMap.IsSafe 7 2 2 1
      (candidateFromParameter perturbation 1 ε)) :
    (SubresultantMap.produce 7 2 1
      (candidateFromParameter perturbation 1 ε)).RepresentsPoint
        (RingHom.id F)
        (geometricProjection (RingHom.id F) (momentCurve ε) point) point := by
  have hchar : ringChar F = 7 := ringChar.eq F 7
  have hshift : IsRojasShiftParameter (1 : F) := by
    rw [IsRojasShiftParameter, if_neg (by omega)]
  exact RootDataCoverage.produce_representsPoint_of_coverage
    (p := 7) (expectedDegree := 2) hcoverage point hpoint 1 ε
      hshift (by norm_num) hsafe

/-- Execute the whole safe producer and inspect every root equation used by the new bridge, not
only the final recovered coordinates. -/
def run : IO Unit := do
  let parameters : List F := [0, 1, 2, 3, 4, 5, 6]
  match SafeMacaulayMap.run 7 twoRoots 1 2 parameters with
  | .error error =>
      throw (IO.userError s!"root-data producer found no safe specialization: {repr error}")
  | .ok output =>
      let ε := output.candidate.parameter
      let roots : List (Fin 2 → F) := [![-1, -1], ![1, 1]]
      for point in roots do
        let theta := geometricProjection (RingHom.id F) (momentCurve ε) point
        unless output.map.modulus.eval theta == 0 do
          throw (IO.userError "root-data producer lost the base modulus root")
        for i in ([0, 1] : List (Fin 2)) do
          let minus := SubresultantMap.minusPolynomial 7 2 output.candidate i
          let plus := SubresultantMap.plusPolynomial 7 2 output.candidate i
          let minusAtRoot := minus.eval (theta + point i)
          let plusAtRoot := plus.eval (theta - point i)
          unless minusAtRoot == 0 && plusAtRoot == 0 do
            throw (IO.userError "root-data producer lost a shifted common root")
        let denominator := output.map.denominator.eval theta
        unless denominator != 0 do
          throw (IO.userError "root-data producer returned a vanishing denominator")
        for i in ([0, 1] : List (Fin 2)) do
          unless (output.map.numerators[i.val]?.getD 0).eval theta / denominator == point i do
            throw (IO.userError "root-data producer recovered the wrong coordinate")
  IO.println "Rojas root-data coverage: base, shifted and coordinate checks passed"

#print axioms RootDataCoverage.isRojasShiftParameter_ne_zero
#print axioms RootDataCoverage.rootData_candidateFromParameter
#print axioms RootDataCoverage.produce_representsPoint_of_coverage
#print axioms RootDataCoverage.run_eq_ok_representsCoveredPoint

end RojasRootDataCoverageTests

def rojasRootDataCoverageStandaloneMain : IO Unit :=
  RojasRootDataCoverageTests.run
