/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ChartContract
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Materialize

/-!
# Materializing the actual chart payload on a weak tower

The executed denominator is the stored chart denominator, not a substituted separant power.
All `k` numerators are materialized in their original order. The source tower may have nilpotents.
Success follows from an explicit quotient-unit premise. The `DenominatorUnits` adapter discharges
that premise from `DenominatorRegular` on localized weak towers. This module makes no agreement
or candidate-coverage claim.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.MaterializeChart

open CompPoly TowerRepresentation TowerAlgebra
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] [DecidableEq E] {k : ℕ}

/-- Elimination inverts the actual denominator and reduces every actual chart numerator. -/
def run (chart : ChartData E 1 k) (r : TowerRepresentation (F := E)) :
    Option (TowerRepresentation (F := E)) :=
  materializeCoefficients? r (chartPolynomials chart).denominator
    (List.ofFn (chartPolynomials chart).numerators)

/-- Successful execution records its checked inverse and the exact coefficient construction. -/
theorem run_provenance (chart : ChartData E 1 k) (r out : TowerRepresentation (F := E))
    (hout : run chart r = some out) :
    ∃ inverse, inverseElimination? r.modulus r.fiber (chartPolynomials chart).denominator =
        some inverse ∧
      out = withMaterializedCoefficients r inverse
        (List.ofFn (chartPolynomials chart).numerators) := by
  unfold run materializeCoefficients? at hout
  split at hout
  · contradiction
  · rename_i inverse hinverse
    exact ⟨inverse, hinverse, (Option.some.inj hout).symm⟩

/-- Quotient unitness, without fiber squarefreeness, guarantees successful elimination. -/
theorem run_exists (chart : ChartData E 1 k) (r : TowerRepresentation (F := E))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (hunit : IsTowerUnit r.modulus r.fiber (chartPolynomials chart).denominator) :
    ∃ out, run chart r = some out := by
  obtain ⟨inverse, hi⟩ := inverseElimination?_exists_of_isTowerUnit
    hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hunit
  exact ⟨withMaterializedCoefficients r inverse (List.ofFn (chartPolynomials chart).numerators),
    by simp [run, materializeCoefficients?, hi]⟩

/-- Materialization preserves the parameter algebra and creates exactly `k` canonical slots. -/
theorem run_shape (chart : ChartData E 1 k) (r out : TowerRepresentation (F := E))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (hout : run chart r = some out) :
    out.modulus = r.modulus ∧ out.fiber = r.fiber ∧ out.NonreducedWellFormed k := by
  obtain ⟨inverse, _, rfl⟩ := run_provenance chart r out hout
  refine ⟨rfl, rfl, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, ?_, ?_⟩
  · simp [withMaterializedCoefficients]
  · intro coefficient hc
    simp only [withMaterializedCoefficients, List.mem_map] at hc
    obtain ⟨numerator, _, rfl⟩ := hc
    exact elementReduced_reduceElement hr.1 hr.2.2.2.1 hr.2.2.2.2.1 _

private theorem eval_inverse (r : TowerRepresentation (F := E))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (denominator inverse : CPolynomial (CPolynomial E))
    (hi : inverseElimination? r.modulus r.fiber denominator = some inverse)
    {K : Type} [Field K] (phi : E →+* K) (u v : K) (hp : r.Point phi u v) :
    evalNested denominator phi u v * evalNested inverse phi u v = 1 := by
  have he := congrArg (fun a => evalNested a phi u v)
    (inverseElimination?_sound _ _ _ _ hi).1
  rw [evalNested_reduceElement phi u v hr.1 hp.1 hr.2.2.2.1 hp.2,
    evalNested_reduceElement phi u v hr.1 hp.1 hr.2.2.2.1 hp.2,
    evalNested_mul, evalNested_one] at he
  exact he

/-- Every specialized slot is its chart numerator divided by the actual denominator. -/
theorem run_specialize (chart : ChartData E 1 k) (r out : TowerRepresentation (F := E))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (hout : run chart r = some out)
    {K : Type} [Field K] (phi : E →+* K) (u v : K) (hp : r.Point phi u v) :
    out.specialize phi u v = Polynomial.JetHornerMachine.coefficientPolynomial
      ((List.ofFn (chartPolynomials chart).numerators).map fun numerator =>
        evalNested numerator phi u v /
          evalNested (chartPolynomials chart).denominator phi u v) := by
  obtain ⟨inverse, hi, rfl⟩ := run_provenance chart r out hout
  have he := eval_inverse r hr _ inverse hi phi u v hp
  have hd : evalNested (chartPolynomials chart).denominator phi u v ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  apply congrArg Polynomial.JetHornerMachine.coefficientPolynomial
  simp only [withMaterializedCoefficients, List.map_map]
  apply List.map_congr_left
  intro numerator _
  simp only [Function.comp_apply]
  rw [evalNested_reduceElement phi u v hr.1 hp.1 hr.2.2.2.1 hp.2, evalNested_mul]
  apply (eq_div_iff hd).2
  calc
    (evalNested numerator phi u v * evalNested inverse phi u v) *
        evalNested (chartPolynomials chart).denominator phi u v =
      evalNested numerator phi u v *
        (evalNested (chartPolynomials chart).denominator phi u v *
          evalNested inverse phi u v) := by ring
    _ = evalNested numerator phi u v := by rw [he, mul_one]

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.MaterializeChart
