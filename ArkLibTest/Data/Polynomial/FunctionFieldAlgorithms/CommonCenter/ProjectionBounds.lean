/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.ProjectionGrid
import Mathlib.Algebra.Field.ZMod

/-!
# Projection degree and bounded-grid clients

The downstream examples consume the computed-output bounds and the explicitly conditional
geometric interface. Runtime fixtures include a cusp and a separable degree-two equation
in characteristic two, whose derivative degree drops to zero.
-/

open CompPoly CPoly Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection
open Polynomial.FunctionFieldAlgorithms

/-- Actual search output gives both appendix degree bounds and the finite-lattice threshold. -/
example {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (Q : CMvPolynomial 2 K) (c : Candidate K) (B : ℕ)
    (h : search B Q = some c) (hB : (fromCMvPolynomial Q).totalDegree ≤ B) :
    c.equation.natDegree ≤ B ∧
      c.discriminant.natDegree ≤ (2 * c.equation.natDegree - 1) * B ∧
      c.equation.natDegree * c.discriminant.natDegree < 2 * (B + 1) ^ 3 := by
  have hc := (search_sound B Q c h).1
  exact ⟨(hc.degree_bounds B hB).1, (hc.degree_bounds B hB).2,
    hc.lattice_dimension_lt B hB⟩

/-- Conditional grid client states the geometric control as an explicit input. -/
example {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (p B : ℕ) [CharP K p] (hp : 2 * B < p) (Q : CMvPolynomial 2 K)
    (control : BadSlopeControl B Q) : (search B Q).isSome :=
  (search_success_iff B Q).mpr (hasPassingSlope_of_control p B hp Q control)

/-- Monic regular inputs succeed without geometric control or a characteristic bound. -/
example {K : Type*} [Field K] [BEq K] [LawfulBEq K] (h : CBivariate K)
    (hm : (CBivariate.toPoly h).Monic) (hd : 0 < h.natDegree)
    (hc : IsCoprime
      (RegularCenterObstruction.functionFieldPolynomial h)
      (RegularCenterObstruction.functionFieldPolynomial h).derivative) :
    (search 0 (CBivariate.toOrdinaryCMv h)).isSome :=
  (search_success_iff 0 _).mpr (hasPassingSlope_of_monic 0 h hm hd hc)

/-- The coordinate substitution preserves total degree even before any checker succeeds. -/
example (Q : CMvPolynomial 2 ℚ) :
    (fromCMvPolynomial (shearHom 5 Q)).totalDegree = (fromCMvPolynomial Q).totalDegree :=
  shear_totalDegree 5 Q

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private def y : CMvPolynomial 2 F := CMvPolynomial.X 0
private def z : CMvPolynomial 2 F := CMvPolynomial.X 1

/-- Verify degrees and actual denominators rather than only successful option tags. -/
def main : IO Unit := do
  let some cusp := trySlope (K := F) 0 (z ^ 2 - y ^ 3)
    | throw (IO.userError "cusp trial failed")
  unless cusp.equation.natDegree == 2 && cusp.discriminant.natDegree == 3 do
    throw (IO.userError "cusp degree fixture failed")
  let y₂ : CMvPolynomial 2 (ZMod 2) := CMvPolynomial.X 0
  let z₂ : CMvPolynomial 2 (ZMod 2) := CMvPolynomial.X 1
  let some dropped := trySlope (K := ZMod 2) 0 (z₂ ^ 2 + z₂ - y₂)
    | throw (IO.userError "separable derivative-drop trial failed")
  unless dropped.equation.natDegree == 2 && dropped.equation.derivative.natDegree == 0 &&
      dropped.discriminant == 1 do
    throw (IO.userError "padded resultant degree-drop fixture failed")
  unless (search 3 ((z - y) ^ 7)).isNone do
    throw (IO.userError "inseparable repeated input incorrectly accepted")
  let bad : CPolynomial (ZMod 3) := CPolynomial.X ^ 3 - CPolynomial.X
  unless bad != 0 && bad.natDegree == 3 &&
      (List.range 5).all (fun i : ℕ => bad.eval (i : ZMod 3) == 0) do
    throw (IO.userError "small-characteristic grid-collision fixture failed")
  IO.println "projection degree, derivative-drop, and grid-collision fixtures: passed"

#print axioms shear_totalDegree
#print axioms Sound.degree_bounds
#print axioms Sound.lattice_dimension_lt
#print axioms trySlope_isSome_iff
#print axioms hasPassingSlope_of_monic
#print axioms exists_grid_nonroot
#print axioms hasPassingSlope_of_control
