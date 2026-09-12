/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-! Public order-zero decoder checks over supplied binary and odd-characteristic fields. -/

namespace PublicDecoderTests

open CompPoly Polynomial
open CompPoly.GuruswamiSudan
open ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.ListDecoding
open ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder

private abbrev modulus := PolynomialBasisFrobeniusTests.Binary.modulus
private abbrev F := Carrier modulus

private def selectedCenter? (p : ℕ) [Fact p.Prime]
    (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    {n : ℕ} (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (params : GSInterpParams) : Option (ℕ × SuppliedCenters.Branch) :=
  match OrdinaryInterpolation.run (points p f domain received) params with
  | none => none
  | some interpolant =>
      match normalize p f (CBivariate.toOrdinaryCMv interpolant) with
      | .normalized data =>
          let count := data.obstruction.natDegree + 1
          some (count, (SuppliedCenters.suppliedRun p f count).branch)
      | _ => none

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

namespace NearCapacity

/-- `X³ + X + 1` supplies F8 for the characteristic-two near-capacity diagnostic. -/
private abbrev binaryModulus : CPolynomial (ZMod 2) :=
  CPolynomial.X ^ 3 + CPolynomial.X + CPolynomial.C 1

private instance : Fact binaryModulus.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [binaryModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  convert Polynomial.monic_X_pow_add (n := 3)
    (p := Polynomial.X + Polynomial.C (1 : ZMod 2))
    (by rw [Polynomial.degree_X_add_C]; decide) using 1
  ring⟩

private theorem binaryModulus_degree : binaryModulus.natDegree = 3 := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [binaryModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.natDegree_cubic (R := ZMod 2)
    (a := 1) (b := 0) (c := 1) (d := 1) one_ne_zero)

private theorem binaryModulus_irreducible : Irreducible binaryModulus.toPoly := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hroot := (Polynomial.mem_roots' (p := binaryModulus.toPoly)).mp hx
    have heval : x ^ 3 + x + 1 = 0 := by
      simpa [binaryModulus, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.IsRoot] using hroot.2
    have hxval : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    have hxlt := x.val_lt
    interval_cases h : x.val
    all_goals rw [hxval] at heval
    case «0» => exact (show (0 : ZMod 2) ^ 3 + 0 + 1 ≠ 0 by decide) heval
    case «1» => exact (show (1 : ZMod 2) ^ 3 + 1 + 1 ≠ 0 by decide) heval
  · rw [← CPolynomial.natDegree_toPoly, binaryModulus_degree]
    decide
  · rw [← CPolynomial.natDegree_toPoly, binaryModulus_degree]

private instance : Fact (Irreducible binaryModulus.toPoly) :=
  ⟨binaryModulus_irreducible⟩

private abbrev oddModulus :=
  ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus

private def binaryDomain : Fin 7 ↪ Carrier binaryModulus where
  toFun i := suppliedIndex 2 binaryModulus ⟨i.val, by
    rw [binaryModulus_degree]
    omega⟩
  inj' := by
    intro i j h
    have h' := (suppliedIndex 2 binaryModulus).injective h
    apply Fin.ext
    simpa using congrArg Fin.val h'

private def oddDomain : Fin 7 ↪ Carrier oddModulus where
  toFun i := suppliedIndex 3 oddModulus ⟨i.val, by
    rw [ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree]
    omega⟩
  inj' := by
    intro i j h
    have h' := (suppliedIndex 3 oddModulus).injective h
    apply Fin.ext
    simpa using congrArg Fin.val h'

/-- Four zero symbols retain the zero message; the last three symbols maximize the observed
normalized obstruction count in exhaustive F8/F9 searches of this parameter family. -/
private def received {K : Type*} [Field K] (domain : Fin 7 → K) (i : Fin 7) : K :=
  if i.val < 4 then 0 else if i.val = 4 then domain 1 else
    if i.val = 5 then domain 1 else domain 2

private def params : GSInterpParams where
  messageDegree := 2
  multiplicity := 1
  weightedDegreeBound := 3

end NearCapacity

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
  check "large F4 path did not select its asserted base center" <|
    selectedCenter? 2 modulus domain received params == some (1, .base)
  match run? 2 modulus domain received 3 3 params with
  | none => throw (IO.userError "large F4 public zeroth decoder failed")
  | some output =>
      check "large F4 public decoder missed the quadratic message" <|
        output.contains [1, 0, 1]
  check "F8 near-capacity normalization changed count or center branch" <|
    selectedCenter? 2 NearCapacity.binaryModulus NearCapacity.binaryDomain
      (NearCapacity.received NearCapacity.binaryDomain) NearCapacity.params == some (7, .base)
  match run? 2 NearCapacity.binaryModulus NearCapacity.binaryDomain
      (NearCapacity.received NearCapacity.binaryDomain) 2 4 NearCapacity.params with
  | none => throw (IO.userError "F8 near-capacity public decoder failed")
  | some output =>
      check "F8 near-capacity public decoder missed the zero message" <|
        output.contains [0, 0]
  check "F9 near-capacity normalization changed count or center branch" <|
    selectedCenter? 3 NearCapacity.oddModulus NearCapacity.oddDomain
      (NearCapacity.received NearCapacity.oddDomain) NearCapacity.params == some (7, .base)
  match run? 3 NearCapacity.oddModulus NearCapacity.oddDomain
      (NearCapacity.received NearCapacity.oddDomain) 2 4 NearCapacity.params with
  | none => throw (IO.userError "F9 near-capacity public decoder failed")
  | some output =>
      check "F9 near-capacity public decoder missed the zero message" <|
        output.contains [0, 0]

#print axioms normalized_capacity
#print axioms run?_ok_exact
#print axioms run?_exists_exact

end PublicDecoderTests
