/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectivePublicDecoder
import ArkLibTest.Data.FiniteField.ExplicitConstruction.EffectiveFrobeniusCoordinates

/-! Data-only generic public decoding over supplied cyclic coordinates and a relative quotient. -/

namespace EffectivePublicDecoderTests

open CompPoly Polynomial CompPoly.GuruswamiSudan
open ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.ListDecoding
open ReedSolomon.ListDecoding.ZerothOrderDecoder
open EffectivePublicDecoder

private abbrev F := EffectiveRelativeQuotientTests.F4
private def field := EffectiveFrobeniusCoordinatesTests.binaryCoordinates.effectiveField

private def domain : Fin 3 ↪ F where
  toFun i := field.index.equivFin ⟨i.val, by change i.val < 4; omega⟩
  inj' := by
    intro i j h
    have h' := field.index.equivFin.injective h
    apply Fin.ext
    simpa using congrArg Fin.val h'

private def received (i : Fin 3) : F := domain i ^ 2 + 1

private def params : GSInterpParams where
  messageDegree := 3
  multiplicity := 1
  weightedDegreeBound := 2

private def boundedParams : GSInterpParams where
  messageDegree := 2
  multiplicity := 1
  weightedDegreeBound := 2

private theorem valid : Valid field domain received 3 3 params := by
  constructor
  · omega
  · omega
  · change 0 < 1
    omega
  · rfl
  · change 2 < 1 * 3
    omega
  · unfold HasInterpolationDimensionSlack HasInterpolationDimensionSlackOnBasis
    simp only [interpolationConstraints, OrdinaryInterpolation.receivedPoints, params,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, tsub_zero,
      add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl,
      List.foldl_push_eq_append, bind_pure_comp, map_pure, Nat.reduceAdd,
      Nat.add_one_sub_one, Order.lt_one_iff, Nat.div_self, List.range'_one,
      List.foldl_cons, List.map_cons, List.map_nil, Array.append_singleton,
      List.foldl_nil, Array.forIn_pure_yield_eq_foldl, Array.size_ofFn,
      Array.foldl_push_eq_append, Array.map_ofFn, Array.empty_append, bind_pure,
      Id.run_pure, interpolationMonomials, CBivariate.monomialsWeightedDegreeLE,
      one_mul, yWeight, CBivariate.monomialGrid, List.size_toArray]
    decide
  · change 3 ≤ 4
    decide

/-- The valid fixture cannot take frequency or bounded-subset decoding. -/
example : ¬(3 < boundedThreshold params) := by decide

/-- No regular equation or graph-coverage proof is needed to invoke public exactness. -/
example : ∃ output, run? field domain received 3 3 params = some output ∧
    ExactOutput domain received 3 3 output :=
  run?_exists_exact field domain received 3 3 params valid

example : run? field domain received 3 3 params ≠ none :=
  run?_ne_none field domain received 3 3 params valid

private def selectedCenter? {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    [DecidableEq K] (base : EffectiveField p K) {n : ℕ} (points : Fin n ↪ K) (word : Fin n → K)
    (parameters : GSInterpParams) : Option (ℕ × SuppliedCenters.Branch) :=
  match OrdinaryInterpolation.run (OrdinaryInterpolation.receivedPoints points word) parameters with
  | none => none
  | some interpolant =>
      match EffectiveAdapter.normalize base (CBivariate.toOrdinaryCMv interpolant) with
      | .normalized data =>
          let count := data.obstruction.natDegree + 1
          some (count, (EffectiveCenters.run base count).branch)
      | _ => none

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- The second fixture supplies an actual degree-two quotient over F4. -/
private def relativeField :=
  effectiveRelativeQuotient field EffectiveRelativeQuotientTests.quadraticModulus

private theorem relative_cardinality : relativeField.index.cardinality = 16 := by
  change 4 ^ EffectiveRelativeQuotientTests.quadraticModulus.natDegree = 16
  rw [EffectiveRelativeQuotientTests.quadraticModulus_degree]
  decide

private def relativeDomain : Fin 3 ↪ Carrier EffectiveRelativeQuotientTests.quadraticModulus where
  toFun i := relativeField.index.equivFin ⟨i.val, by rw [relative_cardinality]; omega⟩
  inj' := by
    intro i j h
    have h' := relativeField.index.equivFin.injective h
    apply Fin.ext
    simpa using congrArg Fin.val h'

/-- Execute preliminary branches and inspect the computed normalization/center path before
checking nonempty symbolic recovery over both supplied presentations. -/
def run : IO Unit := do
  check "frequency branch changed" <|
    run? field domain (fun _ => (1 : F)) 1 2 params == some [[1]]
  check "impossible agreement failed to return successful empty output" <|
    run? field domain received 3 4 params == some []
  check "bounded subset branch failed" <|
    (run? field domain received 2 2 boundedParams).isSome
  check "F4 did not reach regular normalization and base center transport" <|
    selectedCenter? field domain received params == some (1, .base)
  check "supplied cyclic-coordinate F4 decoding missed the quadratic message" <|
    run? field domain received 3 3 params == some [[1, 0, 1]]
  let relativeReceived := fun i => relativeDomain i ^ 2 + 1
  check "relative quotient did not reach regular normalization and center transport" <|
    selectedCenter? relativeField relativeDomain relativeReceived params == some (1, .base)
  check "relative quotient public decoding missed the quadratic message" <|
    run? relativeField relativeDomain relativeReceived 3 3 params == some [[1, 0, 1]]
  let invalidParams : GSInterpParams := ⟨3, 1, 0⟩
  check "interpolation failure was confused with successful empty output" <|
    run? field domain received 3 3 invalidParams == none

#print axioms normalized_capacity
#print axioms run?_ok_exact
#print axioms run?_exists_exact
#print axioms run?_ne_none

end EffectivePublicDecoderTests

def effectivePublicDecoderMain : IO Unit := EffectivePublicDecoderTests.run
