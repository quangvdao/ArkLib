/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-!
# Effective-field zeroth-order adapter tests
-/

namespace ZerothEffectiveAdapterTests

open CompPoly ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
open Polynomial.FunctionFieldAlgorithms

/-- Test-only runtime instrumentation; each actual preparation increments the local counter. -/
@[never_extract, noinline, nospecialize]
private unsafe def countedPreparationImpl {p : ℕ} {K : Type} [Field K]
    [BEq K] [LawfulBEq K] (counter : IO.Ref Nat) (F : EffectiveField p K)
    (_ : Unit) : InverseFrobeniusData p K :=
  unsafeBaseIO do
    counter.modify (· + 1)
    return F.prepareInverseFrobenius ()

/-- Keep runtime instrumentation behind a separate field-construction boundary. -/
@[never_extract, noinline, nospecialize]
private unsafe def countedFieldImpl {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (counter : IO.Ref Nat) (F : EffectiveField p K) : EffectiveField p K :=
  { F with prepareInverseFrobenius := countedPreparationImpl counter F }

/-- The logical field is unchanged; only runtime preparation is observed. -/
@[implemented_by countedFieldImpl, never_extract, noinline, nospecialize]
private def countedField {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (_counter : IO.Ref Nat) (F : EffectiveField p K) : EffectiveField p K := F

/-- Counter regressions throw an IO error, independently of stderr or panic settings. -/
private def checkPreparationCount (counter : IO.Ref Nat) (expected : Nat) (branch : String) :
    IO Unit := do
  let actual ← counter.get
  unless actual == expected do
    throw (IO.userError s!"{branch}: expected {expected} Frobenius preparations, observed {actual}")

/-- The same consumer executes non-prime-field normalization in either characteristic.
An injectable normalizer also permits negative checks of the preparation-count assertions. -/
def check {p : ℕ} {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (F : EffectiveField p K) (theta : K)
    (normalizeProgram : EffectiveField p K → CPoly.CMvPolynomial 2 K →
      OrdinaryNormalization.Result K := normalize) : IO Unit := do
  let _ : DecidableEq K := instDecidableEqOfLawfulBEq
  let domain : Fin 1 ↪ K := ⟨fun _ => theta, fun _ _ _ => Subsingleton.elim _ _⟩
  unless run? F (RingHom.id K) domain (fun _ => theta) 1 1 none == some [[theta]] do
    throw (IO.userError "effective constant branch required normalization")
  let counter ← IO.mkRef 0
  let lazyField := countedField counter F
  match normalizeProgram lazyField 0 with
  | .zeroInput => pure ()
  | _ => throw (IO.userError "zero normalization failed")
  checkPreparationCount counter 0 "zero input"
  unless run? lazyField (RingHom.id K) domain (fun _ => theta) 1 1 none == some [[theta]] do
    throw (IO.userError "constant dispatch touched preparation")
  checkPreparationCount counter 0 "constant dispatch"
  let x : CBivariate K := CPolynomial.C CPolynomial.X
  let y : CBivariate K := CPolynomial.X
  let slope : CBivariate K := CPolynomial.C (CPolynomial.C theta)
  let graph := y - slope * x
  match normalizeProgram lazyField (CBivariate.toOrdinaryCMv graph) with
  | .normalized data =>
    unless data.regular == graph do
      throw (IO.userError "separable normalization changed its graph")
  | _ => throw (IO.userError "separable normalization failed")
  checkPreparationCount counter 0 "separable input"
  match normalizeProgram lazyField (CBivariate.toOrdinaryCMv (graph ^ p)) with
  | .normalized data =>
    unless data.support == graph && data.regular == graph && data.obstruction == 1 do
      throw (IO.userError "effective normalization lost its graph")
  | _ => throw (IO.userError "effective inseparable normalization did not succeed")
  checkPreparationCount counter 1 "inseparable input"
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
