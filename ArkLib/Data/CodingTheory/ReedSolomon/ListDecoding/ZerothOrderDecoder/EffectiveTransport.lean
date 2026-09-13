/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport
public import ArkLib.Data.FiniteField.ExplicitConstruction.EffectiveCenters

/-!
# Regular zeroth-order transport over an effective supplied field

The computed base, odd-quadratic, and binary-quadratic center branches feed the checked
regular-fiber decoder directly. Quadratic arithmetic uses relative quotients over the
supplied field; recovery returns coefficients in that original field. No conversion to
an absolute polynomial basis or caller-supplied center list is needed.

This is the regular-equation transport layer, not the interpolation/normalization public
facade. Its exactness theorem still requires the normalized regular-data and graph-coverage
certificates. Insufficient quadratic capacity remains an explicit low-level failure.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveTransport

open CompPoly Polynomial ArkLib.FiniteField.ExplicitConstruction
open SuppliedTransport

variable {p : ℕ} {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- Compute sufficient centers in the supplied field or its selected relative quadratic,
then lift and recover messages over the original supplied field. -/
def run? (field : EffectiveField p K) {n : ℕ} (T : CBivariate K)
    (obstruction : CPolynomial K) (domain : Fin n ↪ K) (received : Fin n → K)
    (k A : ℕ) : Option (List (List K)) :=
  let count := obstruction.natDegree + 1
  match EffectiveCenters.run field count with
  | .base capacity =>
      runOver (RingHom.id K) T obstruction (field.elementPrefix count capacity)
        domain received k A
  | .oddQuadratic data =>
      runOver (EffectiveCenters.oddEmbedding data) T obstruction
        (EffectiveCenters.oddPrefix field data) domain received k A
  | .binaryQuadratic characteristic _ data =>
      let _ : CharP K 2 := characteristic
      runOver (EffectiveCenters.binaryEmbedding data) T obstruction
        (EffectiveCenters.binaryPrefix field data) domain received k A
  | .insufficientCapacity _ _ => none

/-- The actual center dispatcher and regular-fiber computation succeed with exact base-field
output whenever the normalized equation has coverage and the requested prefix fits. -/
theorem run?_exact (field : EffectiveField p K) {n : ℕ} (T : CBivariate K)
    (obstruction : CPolynomial K) (facts : RegularData T obstruction)
    (hcapacity : obstruction.natDegree + 1 ≤ field.index.cardinality ^ 2)
    (domain : Fin n ↪ K) (received : Fin n → K) (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : K[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, run? field T obstruction domain received k A = some output ∧
      ExactOutput domain received k A output := by
  have hcenters := (EffectiveCenters.run_hasCenters_iff field
    (obstruction.natDegree + 1)).2 hcapacity
  generalize hresult : EffectiveCenters.run field (obstruction.natDegree + 1) = result
    at hcenters ⊢
  cases result with
  | base capacity =>
      rw [run?, hresult]
      apply runOver_exact (RingHom.id K) T obstruction facts
      · exact field.prefix_nodup _ _
      · exact field.prefix_length _ _
      · exact hAk
      · exact hsolutions
  | oddQuadratic data =>
      rw [run?, hresult]
      apply runOver_exact (EffectiveCenters.oddEmbedding data) T obstruction facts
      · exact EffectiveCenters.oddPrefix_nodup field data
      · exact EffectiveCenters.oddPrefix_length field data
      · exact hAk
      · exact hsolutions
  | binaryQuadratic characteristic cardinality_eq data =>
      rw [run?, hresult]
      let _ : CharP K 2 := characteristic
      apply runOver_exact (EffectiveCenters.binaryEmbedding data) T obstruction facts
      · exact EffectiveCenters.binaryPrefix_nodup field data
      · exact EffectiveCenters.binaryPrefix_length field data
      · exact hAk
      · exact hsolutions
  | insufficientCapacity _ _ => exact False.elim (hcenters rfl)

end ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveTransport
