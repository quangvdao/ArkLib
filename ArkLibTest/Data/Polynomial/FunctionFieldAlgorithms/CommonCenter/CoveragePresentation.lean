/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.CoveragePresentation
import Mathlib.Algebra.Field.ZMod

/-! Finite algebra coverage from base-field enumeration and actual coordinate presentations. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity
open CoveragePresentation

private def base : FieldEnumeration (ZMod 2) := ⟨[0, 1], by decide⟩
private def table : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0
private def presentation : AlgebraPresentation (A := Fin 2 → ZMod 2) table where
  decode := LinearEquiv.refl _ _
  map_multiply := by decide +kernel
private def c : Fin 1 → Coordinates (ZMod 2) 2 := ![![1, 0]]
private def b : Fin 1 → Fin 1 → Coordinates (ZMod 2) 2 := ![![![0, 1]]]

-- No enumeration or equality instance for an abstract represented algebra is requested.
example {K A : Type*} [Field K] [DecidableEq K] [CommRing A] [Algebra K A]
    {d m n : ℕ} {t : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) t) (E : FieldEnumeration K)
    (denominators : Fin m → Coordinates K d) (products : Fin m → Fin n → Coordinates K d)
    (h : Ideal.span (Set.range (CoverageSearch.generators
      (P.decode ∘ denominators) (fun l i => P.decode (products l i)))) = ⊤) :
    (CoveragePresentation.run P E denominators products).isCovered = true :=
  (run_covered_iff_span P E denominators products).mpr h

-- Extract actual coordinate coefficients from execution, with no supplied weights.
example : ∃ constant derivative,
    coordinateValue table c b constant derivative = presentation.decode.symm 1 := by
  apply (run_covered_iff_coordinates presentation base c b).mp
  decide +kernel

-- A reduced algebra can still have a proper coverage ideal.
example : ∀ constant derivative,
    coordinateValue table c (fun _ : Fin 1 => fun _ : Fin 1 => 0) constant derivative ≠
      presentation.decode.symm 1 := by
  apply (run_absent_iff_coordinates presentation base c _).mp
  decide +kernel

#print axioms enumeration
#print axioms decode_coordinateValue
#print axioms run_covered_iff_coordinates
#print axioms run_covered_iff_span
#print axioms run_absent_iff_coordinates

/-- Execute coverage over a nonfield reduced algebra enumerated from its base field. -/
def commonCenterCoveragePresentationStandaloneMain : IO Unit := do
  unless (enumeration presentation base).values.length == 4 do
    throw (IO.userError "coordinate enumeration omitted algebra elements")
  match CoveragePresentation.run presentation base c b with
  | .covered weights _ =>
    unless decide (coverageValue (presentation.decode ∘ c)
        (fun l i => presentation.decode (b l i))
        (CoverageSearch.constantWeights weights) (CoverageSearch.derivativeWeights weights) = 1) do
      throw (IO.userError "presented coverage certificate was incorrect")
  | .absent _ => throw (IO.userError "complementary factors did not cover")
  unless !(CoveragePresentation.run presentation base c
      (fun _ : Fin 1 => fun _ : Fin 1 => 0)).isCovered do
    throw (IO.userError "proper reduced ideal falsely covered")
  unless !(CoveragePresentation.run presentation base (Fin.elim0 : Fin 0 → _)
      (Fin.elim0 : Fin 0 → Fin 1 → _)).isCovered do
    throw (IO.userError "empty family falsely covered a nonzero algebra")
  IO.println "Presented finite algebra coverage tests passed"
