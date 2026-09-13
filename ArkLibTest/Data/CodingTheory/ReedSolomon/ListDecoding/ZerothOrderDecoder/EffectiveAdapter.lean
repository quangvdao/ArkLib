/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

namespace ZerothEffectiveAdapterTests

open CompPoly ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
open Polynomial.FunctionFieldAlgorithms

/-- Runtime canary: touching preparation is a test failure. -/
private unsafe def forbiddenPreparationImpl {p : ℕ} {K : Type} [Field K]
    [BEq K] [LawfulBEq K] (F : EffectiveField p K) (_ : Unit) : InverseFrobeniusData p K :=
  letI : Inhabited (InverseFrobeniusData p K) := ⟨F.prepareInverseFrobenius ()⟩
  panic! "normalization forced forbidden Frobenius preparation"

@[implemented_by forbiddenPreparationImpl]
private def forbiddenPreparation {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) (_ : Unit) : InverseFrobeniusData p K :=
  F.prepareInverseFrobenius ()

/-- The same consumer executes non-prime-field inseparable normalization in either characteristic. -/
def check {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) (theta : K) : IO Unit := do
  let _ : DecidableEq K := instDecidableEqOfLawfulBEq
  let domain : Fin 1 ↪ K := ⟨fun _ => theta, fun _ _ _ => Subsingleton.elim _ _⟩
  unless run? F (RingHom.id K) domain (fun _ => theta) 1 1 none == some [[theta]] do
    throw (IO.userError "effective constant branch required normalization")
  let lazyField : EffectiveField p K := { F with prepareInverseFrobenius := forbiddenPreparation F }
  match normalize lazyField 0 with
  | .zeroInput => pure ()
  | _ => throw (IO.userError "zero normalization failed")
  unless run? lazyField (RingHom.id K) domain (fun _ => theta) 1 1 none == some [[theta]] do
    throw (IO.userError "constant dispatch touched preparation")
  let x : CBivariate K := CPolynomial.C CPolynomial.X
  let y : CBivariate K := CPolynomial.X
  let slope : CBivariate K := CPolynomial.C (CPolynomial.C theta)
  let graph := y - slope * x
  match normalize lazyField (CBivariate.toOrdinaryCMv graph) with
  | .normalized data =>
    unless data.regular == graph do
      throw (IO.userError "separable normalization changed its graph")
  | _ => throw (IO.userError "separable normalization failed")
  match normalize F (CBivariate.toOrdinaryCMv (graph ^ p)) with
  | .normalized data =>
    unless data.support == graph && data.regular == graph && data.obstruction == 1 do
      throw (IO.userError "effective normalization lost its graph")
  | _ => throw (IO.userError "effective inseparable normalization did not succeed")
  unless compareField F theta theta == .eq do
    throw (IO.userError "effective comparison violated reflexivity")

/-- Explicit runtime entrypoint for both F4 and F9. -/
def run : IO Unit := do
  check (effectivePolynomialBasis 2 PolynomialBasisFrobeniusTests.Binary.modulus)
    (canonical PolynomialBasisFrobeniusTests.Binary.modulus CPolynomial.X)
  check (effectivePolynomialBasis 3
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus)
    (canonical ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus CPolynomial.X)

#print axioms normalize_correct
#print axioms normalize_noFailure
#print axioms compareField_polynomialBasis

end ZerothEffectiveAdapterTests
