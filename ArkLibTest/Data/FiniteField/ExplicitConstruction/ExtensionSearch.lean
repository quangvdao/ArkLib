/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.ExtensionSearch
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Frobenius
import ArkLibTest.Data.FiniteField.ExplicitConstruction.ArtinSchreierCenters

/-! Proof and runtime checks for deterministic least-degree extension construction. -/

namespace ExtensionSearchTests

open ArkLib.FiniteField.ExplicitConstruction CompPoly CompPoly.CPolynomial

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev f4 := ArtinSchreierCenterTests.Fixtures.f4
private abbrev F4 := Carrier f4

private def f4Equiv : Fin 4 ≃ F4 :=
  (finCongr (by
    rw [ArtinSchreierCenterTests.Fixtures.f4_degree]
    decide)).trans (suppliedIndex 2 f4)

/-- The current field is supplied by its actual polynomial-basis coordinates. -/
private def f4Index : FiniteIndex F4 where
  cardinality := 4
  one_lt_cardinality := by decide
  decode := f4Equiv
  encode := f4Equiv.symm
  decode_encode := f4Equiv.apply_symm_apply
  encode_decode := f4Equiv.symm_apply_apply

example : (ArkLib.FiniteField.ExplicitConstruction.run f4Index 4).branch = .base :=
  (run_base_iff f4Index 4).mpr (by decide)

example : (ArkLib.FiniteField.ExplicitConstruction.run f4Index 5).branch = .extension :=
  (run_extension_iff f4Index 5).mpr (by decide)

example : (ArkLib.FiniteField.ExplicitConstruction.run f4Index 5).branch ≠ .searchFailure :=
  run_searchFailure_ne f4Index 5

/-- Exercise base return, F4-to-F16 construction, exact power boundaries,
the q^d+1 degree jump, quotient arithmetic, and recursive index reuse. -/
def run : IO Unit := do
  match ArkLib.FiniteField.ExplicitConstruction.run f4Index 4 with
  | .base capacity =>
      let values := baseCenters f4Index 4 capacity
      unless values.length == 4 && decide values.Nodup do
        throw <| IO.userError "F4 exact base-capacity prefix failed"
  | _ => throw <| IO.userError "F4 exact base capacity did not return the base field"
  match h5 : ArkLib.FiniteField.ExplicitConstruction.run f4Index 5 with
  | .extension data =>
      have payload := run_extension_payload f4Index 5 data h5
      let extensionIndex := data.finiteIndex f4Index payload.2.1
      let values := extensionIndex.values
      unless data.degree == 2 && extensionIndex.cardinality == 16 &&
          values.length == 16 && decide values.Nodup do
        throw <| IO.userError "F4 request 5 did not construct an indexed field of size 16"
      unless irreducibleTest f4Index data.modulus &&
          firstIrreducible? f4Index data.degree == some data.modulus &&
          (searchTrace f4Index data.degree).all (fun p => !(irreducibleTest f4Index p)) do
        throw <| IO.userError "returned modulus lost deterministic search provenance"
      unless (data.centers f4Index payload.2.1).length == 5 &&
          decide (data.centers f4Index payload.2.1).Nodup do
        throw <| IO.userError "F16 requested prefix has wrong length or duplicates"
      unless values.all (fun a => a == 0 || a * a⁻¹ == 1) do
        throw <| IO.userError "a nonzero element of the constructed F16 failed inversion"
      unless values.all (fun a => (a ^ 2)⁻¹ == a⁻¹ ^ 2) do
        throw <| IO.userError "constructed F16 inverse did not commute with squaring"
      unless values.all (fun a => a == 0 || a ^ 2 * a⁻¹ ^ 2 == 1) do
        throw <| IO.userError "constructed F16 inverse-square identity failed"
      unless values.all (fun a => data.inverseSquare f4Index a ^ 2 == a) do
        throw <| IO.userError "computed inverse-square callback failed on constructed F16"
      let c := data.embedding (f4Index.decode ⟨1, by decide⟩)
      let squareInput : CPolynomial data.FieldType := X ^ 2 + C (c ^ 2)
      let contracted :=
        CPolynomial.FullSquarefreeDecomposition.contractWith 2
          (data.inverseSquare f4Index) squareInput
      unless contracted ^ 2 == squareInput do
        throw <| IO.userError "constructed inverse-square failed in squarefree contraction"
      unless (ArkLib.FiniteField.ExplicitConstruction.run extensionIndex 16).branch == .base do
        throw <| IO.userError "a constructed extension could not be reused as a base field"
      unless (ArkLib.FiniteField.ExplicitConstruction.run extensionIndex 17).branch == .extension do
        throw <| IO.userError "recursive constructed-field extension did not execute"
  | _ => throw <| IO.userError "F4 request 5 did not construct an extension"
  match h16 : ArkLib.FiniteField.ExplicitConstruction.run f4Index 16 with
  | .extension data =>
      have payload := run_extension_payload f4Index 16 data h16
      let extensionIndex := data.finiteIndex f4Index payload.2.1
      unless data.degree == 2 && extensionIndex.cardinality == 16 &&
          (data.centers f4Index payload.2.1).length == 16 do
        throw <| IO.userError "exact q^2 capacity did not retain degree two"
  | _ => throw <| IO.userError "exact q^2 capacity was not constructed"
  match h17 : ArkLib.FiniteField.ExplicitConstruction.run f4Index 17 with
  | .extension data =>
      have payload := run_extension_payload f4Index 17 data h17
      let extensionIndex := data.finiteIndex f4Index payload.2.1
      unless data.degree == 3 && extensionIndex.cardinality == 64 &&
          (data.centers f4Index payload.2.1).length == 17 do
        throw <| IO.userError "q^2+1 boundary did not select degree three and size 64"
  | _ => throw <| IO.userError "q^2+1 request was not constructed"

#print axioms irreducibleTest_eq_true_iff
#print axioms firstIrreducible?_ne_none
#print axioms SearchResult.embedding_injective
#print axioms SearchResult.cardinality
#print axioms SearchResult.finrank
#print axioms SearchResult.inverseSquare_sq
#print axioms run_extension_payload

end ExtensionSearchTests
