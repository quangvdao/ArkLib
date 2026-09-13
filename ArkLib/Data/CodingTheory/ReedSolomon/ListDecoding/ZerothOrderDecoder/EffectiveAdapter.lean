/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder
public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectivePolynomialBasis

/-! # Effective-field boundary for ordinary decoding

Ordering and normalization require only the operational field package. The checked
regular-fiber consumer already works over arbitrary fields. Quadratic center transport
in `PublicDecoder` remains a separate polynomial-basis-specific integration obligation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter

open CompPoly Polynomial ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms OrdinaryNormalizationCorrectness

variable {p : ℕ} {K : Type*} [Field K] [BEq K] [LawfulBEq K]

/-- Deterministic rank reads one coordinate index; it does not enumerate the field. -/
def rank (F : EffectiveField p K) (a : K) : ℕ := (F.elementIndex a).val

/-- The supplied coordinate order, independent of Frobenius preparation. -/
def compareField (F : EffectiveField p K) (a b : K) : Ordering :=
  compare (rank F a) (rank F b)

instance (F : EffectiveField p K) : Std.TransCmp (compareField F) where
  eq_swap := by
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := compare) (a := rank F a) (b := rank F b)
  isLE_trans := by
    intro a b c hab hbc
    exact Std.TransCmp.isLE_trans (cmp := compare) hab hbc

instance (F : EffectiveField p K) : Std.LawfulEqCmp (compareField F) where
  eq_of_compare := by
    intro a b hab
    have hi : F.elementIndex a = F.elementIndex b :=
      Fin.ext (Std.LawfulEqCmp.eq_of_compare (cmp := compare) hab)
    simpa using congrArg F.unindex hi

/-- Preparation is forced only when a joint-root coefficient needs inverse Frobenius.
The runtime memoizes this thunk, sharing preparation across all radical calls. -/
def normalize (F : EffectiveField p K) (Q : CPoly.CMvPolynomial 2 K) :
    OrdinaryNormalization.Result K := by
  let _ : Fact p.Prime := ⟨F.prime⟩
  let _ := F.characteristic
  let prepared : Thunk (InverseFrobeniusData p K) := ⟨F.prepareInverseFrobenius⟩
  exact OrdinaryNormalization.runCertified p (fun a => prepared.get.inverseFrobenius a) Q
    (fun _ => prepared.get.inverseFrobenius_pow)

/-- Delaying and memoizing preparation preserves the ordinary algorithm's result. -/
theorem normalize_eq_run (F : EffectiveField p K) (Q : CPoly.CMvPolynomial 2 K) :
    normalize F Q = OrdinaryNormalization.run p
      (F.prepareInverseFrobenius ()).inverseFrobenius Q := rfl

/-- The generic boundary retains the complete ordinary-normalization contract. -/
theorem normalize_correct (F : EffectiveField p K) (Q : CPoly.CMvPolynomial 2 K) :
    CorrectOutcome Q (normalize F Q) := by
  let _ : Fact p.Prime := ⟨F.prime⟩
  let _ := F.characteristic
  exact runCertified_correct p (F.prepareInverseFrobenius ()).inverseFrobenius Q
    (fun _ => (F.prepareInverseFrobenius ()).inverseFrobenius_pow)

/-- No supplied effective field can expose an arithmetic failure at this boundary. -/
theorem normalize_noFailure (F : EffectiveField p K) (Q : CPoly.CMvPolynomial 2 K)
    (reason : OrdinaryNormalization.Failure) :
    normalize F Q ≠ .arithmeticFailure reason :=
  (normalize_correct F Q).not_arithmeticFailure reason

/-- Generic dispatch reuses the characteristic-free checked consumer and constant decoder. -/
def run? [DecidableEq K] {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (F : EffectiveField p K) {n : ℕ} (base : K →+* E) (domain : Fin n ↪ K)
    (received : Fin n → K) (k A : ℕ) (input : Option (SuppliedAdapter.CheckedInput E)) :=
  SuppliedAdapter.run? (compareField F) base domain received k A input

@[simp] theorem run?_one [DecidableEq K] {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (F : EffectiveField p K) {n : ℕ} (base : K →+* E) (domain : Fin n ↪ K)
    (received : Fin n → K) (A : ℕ) (input : Option (SuppliedAdapter.CheckedInput E)) :
    run? F base domain received 1 A input =
      some (ConstantDecoder.run (compareField F) A received) :=
  SuppliedAdapter.run?_one _ _ _ _ _ _

/-- Polynomial-basis clients retain exactly their existing deterministic comparison. -/
theorem compareField_polynomialBasis (p : ℕ) [Fact p.Prime]
    (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)] :
    compareField (effectivePolynomialBasis p f) = PublicDecoder.compareField p f := rfl

/-- The generic normalization executes the same result as the polynomial-basis public path. -/
theorem normalize_polynomialBasis (p : ℕ) [Fact p.Prime]
    (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (Q : CPoly.CMvPolynomial 2 (Carrier f)) :
    normalize (effectivePolynomialBasis p f) Q = PublicDecoder.normalize p f Q := by
  have hi : ((effectivePolynomialBasis p f).prepareInverseFrobenius ()).inverseFrobenius =
      (boundedInverseFrobeniusCertificate p f p le_rfl).inverse := by
    funext a
    rw [effectivePolynomialBasis_inverseFrobenius, boundedInverseFrobeniusCertificate_inverse]
  unfold normalize PublicDecoder.normalize OrdinaryNormalization.runCertified
  dsimp only [Thunk.get]
  rw [hi]

end ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
