/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalRecovery

/-! Acceptance checks for recovery from a fully universal descended component. -/

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalRecoveryTests

open CompPoly CPolynomial CPoly FullSquarefreeDecomposition.Driver
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer
open ArkLib.FiniteField.ExplicitConstruction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev Base := ZMod 5
private abbrev modulus : CPolynomial Base := X

private instance : Fact modulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, modulus, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

private instance : Fact (Irreducible modulus.toPoly) := ⟨by
  rw [modulus, CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

private abbrev F := Carrier modulus
private def M : MulContext F := MulContext.naive
private def D : ModContext F := ModContext.naive

/-- This chart represents `P(X)=X`.  Both received positions agree identically modulo its sole
fiber component `V`, so descent marks both residual labels universal. -/
private def chart : ChartData F 1 2 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1
    separant := 1
    denominator := 1
    numerators := fun j => if j.val = 0 then 0 else 1 }

private def domain : Fin 2 ↪ F where
  toFun := ![0, 1]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private def received (i : Fin 2) : F := domain i

private def prepared : Prepared F 2 :=
  prepare chart (indexedReceived domain received)

private def candidates : List (TowerRepresentation (F := F)) :=
  firstOrderNormCandidatesWithRecovery 5 modulus M D 2 chart domain received

/-- The actual descent detects the fully universal block and the combined producer emits the
constant tower for the wanted linear polynomial. -/
def run : IO Unit := do
  unless prepared.blocks.map (fun block => block.component.universal.length) == [2] do
    throw <| IO.userError "fixture did not produce one fully universal component"
  unless needsUniversalRecovery (A := 2) chart domain received do
    throw <| IO.userError "fully universal component did not activate interpolation"
  let wantedCoefficients : List (CPolynomial (CPolynomial F)) :=
    [CPolynomial.C (CPolynomial.C 1), CPolynomial.C (CPolynomial.C 0)]
  unless candidates.any fun candidate =>
      candidate.modulus == CPolynomial.X &&
        candidate.fiber == CPolynomial.X &&
        candidate.coefficients == wantedCoefficients do
    throw <| IO.userError "combined producer omitted the interpolated wanted polynomial"

#check produceComputedBlock_point_complete_of_universal_lt
#check constantTower_wellFormed
#check mem_universalRecoveryCandidates_of_agreement
#check universalRecoveryCandidates_wellFormed
#check needsUniversalRecovery_eq_true_of_block
#check firstOrderNormCandidatesWithRecovery_complete_of_universal_block
#check firstOrderNormCandidatesWithRecovery_complete_of_block
#check firstOrderNormCandidatesWithRecovery_wellFormed

#print axioms produceComputedBlock_point_complete_of_universal_lt
#print axioms mem_universalRecoveryCandidates_of_agreement
#print axioms firstOrderNormCandidatesWithRecovery_complete_of_block
#print axioms firstOrderNormCandidatesWithRecovery_wellFormed

end ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalRecoveryTests
