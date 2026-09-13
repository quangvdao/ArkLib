/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.LowestCoefficientCoverage
public import ArkLib.Data.Polynomial.Rojas.SpecializationCorrectness

/-!
# Input-derived affine-root coverage for the Rojas producer

This file states the geometric guarantee of the executable dense producer
without supplying a root list or a factorization oracle.  Every nonsingular
affine root of the input system is isolated and its affine hyperplane divides
the computed lowest coefficient.  Other components and other factors are
allowed to remain.

This is deliberately weaker than `PerturbationFactorization`: divisibility by
all known root hyperplanes does not say that they exhaust the factors of the
Macaulay determinant multiple.  An exact toric-resultant/extraneous-factor
theorem is needed for that stronger equality.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.FactorizationCoverage

open CPoly CPoly.CMvPolynomial
open MvPolynomial
open ArkLib.Rojas
open DenseMacaulay ResultantSemantics AffineDeformation HyperplaneFactor
open LowestCoefficientCoverage

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable section

/-- An intrinsic, input-only description of a nonsingular affine root. -/
def IsNonsingularAffineRoot {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F) : Prop :=
  IsCommonAffineRoot (RingHom.id F) point system ∧
    (jacobian system point).det ≠ 0

/-- A perturbation covers every nonsingular affine root of the input system.
The universal quantifier avoids a supplied solution list or root oracle. -/
def CoversNonsingularAffineRoots {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (perturbation : CMvPolynomial (n + 1) F) : Prop :=
  ∀ point, IsNonsingularAffineRoot system point →
    affineLinearForm point ∣ fromCMvPolynomial perturbation

omit [BEq F] [LawfulBEq F] in
/-- Nonsingularity supplies an actual basic-open isolation certificate, even
when unrelated positive-dimensional components are present. -/
theorem IsNonsingularAffineRoot.hasIsolatingPolynomial {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {point : Fin n → F}
    (hpoint : IsNonsingularAffineRoot system point) :
    HasIsolatingPolynomial (fun i ↦ fromCMvPolynomial (system i)) point := by
  apply hasIsolatingPolynomial_of_jacobian_det_ne_zero
  · intro i
    simpa [CPoly.eval₂_equiv] using hpoint.1 i
  · exact hpoint.2

/-- The actual executable lowest coefficient covers all nonsingular affine
roots.  The only data are the input system and a successful `run`. -/
theorem run_coversNonsingularAffineRoots {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (output : Output n (F := F))
    (hrun : run system = .ok output) :
    CoversNonsingularAffineRoots system output.perturbation := by
  intro point hpoint
  exact affineLinearForm_dvd_run_perturbation system point
    hpoint.1 hpoint.2 output hrun

/-- Specializing a covered affine hyperplane gives its expected univariate
linear factor. -/
theorem eval₂Hom_affineLinearForm {n : ℕ} (point u : Fin n → F) :
    MvPolynomial.eval₂Hom CompPoly.CPolynomial.CHom (perturbationAssignment u)
        (affineLinearForm point) =
      CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (geometricProjection (RingHom.id F) u point) := by
  rw [affineLinearForm_eq]
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, CompPoly.CPolynomial.CHom_apply,
    perturbationAssignment, Fin.cases_zero, Fin.cases_succ]
  calc
    _ = CompPoly.CPolynomial.X +
        CompPoly.CPolynomial.C (∑ x, point x * u x) := by
      congr 1
      have hsum := map_sum CompPoly.CPolynomial.CHom
        (fun x ↦ point x * u x) Finset.univ
      calc
        _ = ∑ x, CompPoly.CPolynomial.C (point x * u x) := by
          apply Finset.sum_congr rfl
          intro x _
          simpa only [CompPoly.CPolynomial.CHom_apply] using
            (map_mul CompPoly.CPolynomial.CHom (point x) (u x)).symm
        _ = _ := by
          simpa only [CompPoly.CPolynomial.CHom_apply] using hsum.symm
    _ = CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (-∑ x, u x * point x) := by
      have hswap : (∑ x, point x * u x) = ∑ x, u x * point x := by
        apply Finset.sum_congr rfl
        intro x _
        exact mul_comm _ _
      have hneg := map_neg CompPoly.CPolynomial.CHom (∑ x, u x * point x)
      rw [hswap]
      rw [show CompPoly.CPolynomial.C (-∑ x, u x * point x) =
          -CompPoly.CPolynomial.C (∑ x, u x * point x) by
        simpa only [CompPoly.CPolynomial.CHom_apply] using hneg]
      rw [sub_neg_eq_add]

/-- Every covered root remains visible as a linear factor after any executable
parameter specialization. -/
theorem specializedLinearFactor_dvd_of_coverage {n : ℕ}
    {system : Fin n → CMvPolynomial n F}
    {perturbation : CMvPolynomial (n + 1) F}
    (hcoverage : CoversNonsingularAffineRoots system perturbation)
    (point u : Fin n → F) (hpoint : IsNonsingularAffineRoot system point) :
    CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (geometricProjection (RingHom.id F) u point) ∣
      specializePerturbation perturbation u := by
  have hdiv := map_dvd
    (MvPolynomial.eval₂Hom CompPoly.CPolynomial.CHom (perturbationAssignment u))
    (hcoverage point hpoint)
  rw [eval₂Hom_affineLinearForm] at hdiv
  simpa [specializePerturbation, CPoly.eval₂_equiv] using hdiv

/-- A successful producer run therefore exposes every nonsingular root in
every univariate specialization used by the downstream decoder. -/
theorem run_specializedLinearFactor_dvd {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (output : Output n (F := F))
    (hrun : run system = .ok output) (point u : Fin n → F)
    (hpoint : IsNonsingularAffineRoot system point) :
    CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (geometricProjection (RingHom.id F) u point) ∣
      specializePerturbation output.perturbation u :=
  specializedLinearFactor_dvd_of_coverage
    (run_coversNonsingularAffineRoots system output hrun) point u hpoint

end

end ArkLib.Rojas.Producer.FactorizationCoverage
