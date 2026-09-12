/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Producer

/-! End-to-end execution of component descent, decomposition, and candidate generation. -/

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.ProducerTests

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

/-- The single fiber `V=0` and two identical nonuniversal residuals `U` produce the repeated norm
root `U²`; threshold two must retain precisely `U=0`. -/
private def chart : ChartData F 1 1 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1
    separant := 1
    denominator := 1
    numerators := fun _ => CMvPolynomial.X 0 }

private def received : List (F × F) := [(0, 0), (0, 0)]
private def M : MulContext F := MulContext.naive
private def D : ModContext F := ModContext.naive
private def prepared : Prepared F 1 := prepare chart received
private def candidates : List (TowerRepresentation (F := F)) :=
  firstOrderNormCandidates 5 modulus M D 2 chart received

/-- This explicitly observes successful decomposition of the computed block before checking the
candidate emitted by the public producer.  It also rejects the wrong projected point `U=1`. -/
def run : IO Unit := do
  let some block := prepared.blocks[0]?
    | throw <| IO.userError "component preparation returned no block"
  unless block.normProduct.coeff 0 == 0 && block.normProduct.coeff 1 == 0 &&
      block.normProduct.coeff 2 != 0 do
    throw <| IO.userError "computed block did not preserve the repeated norm root"
  let .ok decomposition := decomposeComputedBlock 5 modulus M D block prepared.agreements
    | throw <| IO.userError "actual supplied-field decomposition rejected the computed norm"
  let support := thresholdProduct M 2 decomposition
  unless support.eval 0 == 0 && support.eval 1 != 0 do
    throw <| IO.userError "actual multiplicity threshold accepted the wrong projected point"
  unless candidates.length == 1 do
    throw <| IO.userError "public producer did not consume the successful decomposition"
  unless candidates.all fun candidate =>
      candidate.modulus.eval 0 == 0 && candidate.modulus.eval 1 != 0 &&
        candidate.coefficients.length == 1 do
    throw <| IO.userError "materialized candidate has the wrong support or coefficient count"

#print axioms evalNested_bivariatePolynomial
#print axioms componentEvalAt_eq_evalNested
#print axioms evalNested_pow
#print axioms exists_preparedBlock_of_equation_root
#print axioms preparedBlock_natDegree_le_equation
#print axioms threshold_le_card_nonuniversalPositions
#print axioms produceComputedBlock_point_complete
#print axioms firstOrderNormCandidates_point_complete_of_decompose
#print axioms firstOrderNormCandidates_wellFormed

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ProducerTests
