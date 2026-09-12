/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-! Public order-zero decoder checks over the supplied binary extension F4. -/

namespace PublicDecoderTests

open CompPoly Polynomial
open CompPoly.GuruswamiSudan
open ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.ListDecoding
open ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder

private abbrev modulus := PolynomialBasisFrobeniusTests.Binary.modulus
private abbrev F := Carrier modulus

private def domain : Fin 3 ↪ F where
  toFun i := suppliedIndex 2 modulus ⟨i.val, by
    rw [PolynomialBasisFrobeniusTests.Binary.modulus_degree]
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' := congrArg (fun a => ((suppliedIndex 2 modulus).symm a).val) h
    simpa using h'

/-- A quadratic message over F4 forces `n > p` and `k > p` while meeting the large-branch
threshold exactly. -/
private def received (i : Fin 3) : F := domain i ^ 2 + 1

private def params : GSInterpParams where
  messageDegree := 3
  multiplicity := 1
  weightedDegreeBound := 2

private def boundedParams : GSInterpParams where
  messageDegree := 2
  multiplicity := 1
  weightedDegreeBound := 2

private theorem valid : Valid 2 modulus domain received 3 3 params := by
  constructor
  · omega
  · omega
  · change 0 < 1
    omega
  · rfl
  · change 2 < 1 * 3
    omega
  · unfold HasInterpolationDimensionSlack HasInterpolationDimensionSlackOnBasis
    simp only [interpolationConstraints, points, OrdinaryInterpolation.receivedPoints, params,
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
  · rw [PolynomialBasisFrobeniusTests.Binary.modulus_degree]
    decide

/-- The F4 canary reaches interpolation, normalization, and supplied-center transport rather than
frequency or bounded fallback.  Dedicated transport tests force both quadratic-center branches. -/
example : ¬(3 < boundedThreshold params) := by decide

/-- The actual public binary-extension call succeeds with the full exact-output contract. -/
example : ∃ output, run? 2 modulus domain received 3 3 params = some output ∧
    ExactOutput domain received 3 3 output :=
  run?_exists_exact 2 modulus domain received 3 3 params valid

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)

/-- Execute the preliminary branches and a genuine large characteristic-two symbolic path. -/
def run : IO Unit := do
  check "supplied comparator did not follow polynomial-basis order" <|
    compareField 2 modulus (domain 0) (domain 1) == .lt
  check "k=1 did not run the frequency decoder first" <|
    run? 2 modulus domain (fun _ => (1 : F)) 1 2 params == some [[1]]
  check "agreement above the block length did not return the exact empty list" <|
    run? 2 modulus domain received 3 4 params == some []
  check "bounded-length input did not use the total subset decoder" <|
    (run? 2 modulus domain received 2 2 boundedParams).isSome
  match run? 2 modulus domain received 3 3 params with
  | none => throw (IO.userError "large F4 public zeroth decoder failed")
  | some output =>
      check "large F4 public decoder missed the quadratic message" <|
        output.contains [1, 0, 1]

#print axioms normalized_capacity
#print axioms run?_ok_exact
#print axioms run?_exists_exact

end PublicDecoderTests
