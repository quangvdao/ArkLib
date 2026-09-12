/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.ArtinSchreierCenters

/-! Runtime checks for supplied binary fields and their Artin--Schreier extensions. -/

namespace ArtinSchreierCenterTests

open ArkLib.FiniteField.ExplicitConstruction CompPoly CompPoly.CPolynomial
  ArkLib.PolynomialQuotient

namespace Fixtures

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Degree-one `F₂` presentation; its supplied generator is zero. -/
abbrev f2 : CPolynomial (ZMod 2) := X

instance : Fact f2.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X⟩

instance : Fact (Irreducible f2.toPoly) := ⟨by
  rw [CPolynomial.X_toPoly]
  exact Polynomial.irreducible_X⟩

/-- Supplied polynomial-basis `F₄ = F₂[t]/(t²+t+1)`. -/
abbrev f4 : CPolynomial (ZMod 2) := X ^ 2 + X + C 1

instance : Fact f4.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [f4, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  simpa using (Polynomial.isMonicOfDegree_add_add_two (1 : ZMod 2) 1).monic⟩

theorem f4_degree : f4.natDegree = 2 := by
  rw [CPolynomial.natDegree_toPoly]
  obtain ⟨hdegree, _⟩ := Polynomial.isMonicOfDegree_add_add_two (1 : ZMod 2) 1
  rw [map_one, one_mul] at hdegree
  simpa only [f4, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.C_1] using hdegree

theorem f4_irreducible : Irreducible f4.toPoly := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [← CPolynomial.natDegree_toPoly, f4_degree]
    decide
  · intro x hx
    have heval : x ^ 2 + x + 1 = 0 := by
      simpa [f4, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
        CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.IsRoot] using hx
    have hxval : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    have hxlt := x.val_lt
    interval_cases h : x.val
    all_goals rw [hxval] at heval
    case «0» => exact (show (0 : ZMod 2) ^ 2 + 0 + 1 ≠ 0 by decide) heval
    case «1» => exact (show (1 : ZMod 2) ^ 2 + 1 + 1 ≠ 0 by decide) heval

instance : Fact (Irreducible f4.toPoly) := ⟨f4_irreducible⟩

end Fixtures

open ArtinSchreierCenters

example : Fixtures.f2.natDegree = 1 := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]
  exact Polynomial.natDegree_X

example : Nat.card (Carrier Fixtures.f4) = 4 := by
  rw [suppliedCardinality 2 Fixtures.f4, Fixtures.f4_degree]
  decide

example : ringChar (Carrier Fixtures.f4) = 2 := suppliedCharacteristic 2 Fixtures.f4

example (data : QuadraticData (Carrier Fixtures.f4) 4 5 2) :
    Nat.card data.FieldType = 16 := by
  have index : Fin 4 ≃ Carrier Fixtures.f4 := by
    simpa [Fixtures.f4_degree] using suppliedIndex 2 Fixtures.f4
  rw [data.cardinality index]
  decide

example (data : QuadraticData (Carrier Fixtures.f4) 4 5 2) :
    ringChar data.FieldType = 2 := ringChar.eq _ 2

/-- Execute supplied `F₂` and `F₄` base, quadratic, and capacity boundaries. -/
def run : IO Unit := do
  let f2 := Fixtures.f2
  have hdegree2 : f2.natDegree = 1 := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]
    exact Polynomial.natDegree_X
  let index2 := suppliedIndex 2 f2
  unless (canonical f2 X : Carrier f2) == 0 do
    throw (IO.userError "degree-one supplied F2 generator is not zero")
  unless (suppliedRun f2 2).branch == .base do
    throw (IO.userError "supplied F2 exact base capacity failed")
  match suppliedRun f2 3 with
  | .quadratic data =>
      unless data.parameter == (1 : Carrier f2) do
        throw (IO.userError "supplied F2 scan did not select trace-one one")
      unless traceOne? 1 (traceIndex index2 (by rw [hdegree2])) == some data.parameter do
        throw (IO.userError "supplied F2 parameter lost bounded-scan provenance")
      unless absoluteTrace 1 data.parameter == 1 do
        throw (IO.userError "supplied F2 parameter does not have trace one")
      unless (List.finRange 2).all (fun i =>
          let x := index2 ((finCongr (by rw [hdegree2]; decide)).symm i)
          x ^ 2 != data.parameter + x) do
        throw (IO.userError "Artin-Schreier polynomial unexpectedly has an F2 root")
      let w : data.FieldType := ⟨0, 1⟩
      unless decide (w ^ 2 = data.embedding data.parameter + w ∧
          (w + 1) * (w + 1)⁻¹ = 1) do
        throw (IO.userError "supplied F4 field relation or inversion failed")
      let values := data.centers index2
      unless values.length == 3 && decide values.Nodup do
        throw (IO.userError "supplied F2-to-F4 prefix failed")
  | _ => throw (IO.userError "supplied F2 quadratic branch was not constructed")
  match suppliedRun f2 4 with
  | .quadratic data =>
      unless (data.centers index2).length == 4 && decide (data.centers index2).Nodup do
        throw (IO.userError "supplied F2-to-F4 exact quadratic capacity failed")
  | _ => throw (IO.userError "supplied F2 exact quadratic capacity was rejected")
  unless (suppliedRun f2 5).branch == .insufficientCapacity do
    throw (IO.userError "supplied F2 quadratic capacity plus one was accepted")
  let f4 := Fixtures.f4
  let index4 := suppliedIndex 2 f4
  unless (suppliedRun f4 4).branch == .base do
    throw (IO.userError "supplied F4 exact base capacity failed")
  match suppliedRun f4 5 with
  | .quadratic data =>
      unless data.parameter.val.coeff 0 == 0 && data.parameter.val.coeff 1 == 1 do
        throw (IO.userError "supplied F4 scan did not select its first trace-one coordinate")
      unless traceOne? 2 (traceIndex index4 (by rw [Fixtures.f4_degree])) ==
          some data.parameter do
        throw (IO.userError "supplied F4 parameter lost bounded-scan provenance")
      unless absoluteTrace 2 data.parameter == 1 do
        throw (IO.userError "supplied F4 parameter does not have trace one")
      unless (List.finRange 4).all (fun i =>
          let x := index4 ((finCongr (by rw [Fixtures.f4_degree]; decide)).symm i)
          x ^ 2 != data.parameter + x) do
        throw (IO.userError "Artin-Schreier polynomial unexpectedly has an F4 root")
      let w : data.FieldType := ⟨0, 1⟩
      unless decide (w ^ 2 = data.embedding data.parameter + w ∧
          data.embedding 1 + data.embedding 1 = 0 ∧
          (w + 1) * (w + 1)⁻¹ = 1) do
        throw (IO.userError "supplied F16 field relation, embedding, or inversion failed")
      let values := data.centers index4
      unless values.length == 5 && decide values.Nodup do
        throw (IO.userError "supplied F4-to-F16 prefix failed")
      unless (values[4]?).map QuadraticAlgebra.re == some (0 : Carrier f4) &&
          (values[4]?).map QuadraticAlgebra.im == some (1 : Carrier f4) do
        throw (IO.userError "pair-coordinate prefix did not cross supplied F4")
  | _ => throw (IO.userError "supplied F4 quadratic branch was not constructed")
  match suppliedRun f4 16 with
  | .quadratic data =>
      unless (data.centers index4).length == 16 && decide (data.centers index4).Nodup do
        throw (IO.userError "supplied F4-to-F16 exact quadratic capacity failed")
  | _ => throw (IO.userError "supplied F4 exact quadratic capacity was rejected")
  unless (suppliedRun f4 17).branch == .insufficientCapacity do
    throw (IO.userError "supplied F4 quadratic capacity plus one was accepted")

#print axioms ArtinSchreierCenters.exists_absoluteTrace_one
#print axioms ArtinSchreierCenters.traceOne?_ne_none
#print axioms ArtinSchreierCenters.no_artinSchreier_root
#print axioms ArtinSchreierCenters.QuadraticData.modulus_irreducible
#print axioms ArtinSchreierCenters.QuadraticData.cardinality
#print axioms ArtinSchreierCenters.run_parameter

end ArtinSchreierCenterTests
