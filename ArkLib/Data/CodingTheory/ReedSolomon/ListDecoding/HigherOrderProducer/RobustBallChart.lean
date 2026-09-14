/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallCoverage

/-!
# Robust-ball capture for actual chart differentials

Tangent labels are actual agreement differentials restricted to the kernel of the actual chart
normal. The fixed-gap hypothesis yields a spanning selection in the field-independent family;
dual nondegeneracy makes its actual square Jacobian injective. No stored separant identity is used.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallChart

open CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.HiddenDerivative.SquareSystems
open DirectJacobian DirectAffine RobustBallEnumeration RobustBallCoverage

universe u v w

section LinearAlgebra

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {n r : ℕ}

/-- A spanning family of actual coordinate functionals separates vectors. -/
theorem selectedCoordinateMap_injective_of_span (pool : V →ₗ[F] (Fin n → F))
    (selected : Finset (Fin n)) (hcard : selected.card = r)
    (hspan : Submodule.span F (coordinateFunctional pool ''
      (↑selected : Set (Fin n))) = ⊤) :
    Function.Injective (selectedCoordinateMap pool (rowSubsetEmbedding selected hcard)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply (Module.forall_dual_apply_eq_zero_iff F x).mp
  intro φ
  have hφ : φ ∈ Submodule.span F (coordinateFunctional pool ''
      (↑selected : Set (Fin n))) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun f _ ↦ f x = 0) ?_ ?_ ?_ ?_ hφ
  · rintro f ⟨i, hi, rfl⟩
    have hirange : i ∈ Set.range (selected.orderEmbOfFin hcard) := by
      rwa [Finset.range_orderEmbOfFin]
    obtain ⟨j, rfl⟩ := hirange
    exact congrFun hx j
  · rfl
  · intro f g _ _ hf hg
    simp [hf, hg]
  · intro a f _ hf
    simp [hf]

/-- Injectivity on the normal kernel gives injectivity after adjoining the normal row. -/
theorem normalSelectedMap_injective_of_tangent (normal : V →ₗ[F] F)
    (pool : V →ₗ[F] (Fin n → F)) (selected : Fin r → Fin n)
    (htangent : Function.Injective
      (selectedCoordinateMap (pool.comp normal.ker.subtype) selected)) :
    Function.Injective (normalSelectedMap normal pool selected) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hnormal : normal x = 0 := congrArg Prod.fst hx
  let tangent : normal.ker := ⟨x, hnormal⟩
  have hzero : selectedCoordinateMap (pool.comp normal.ker.subtype) selected tangent = 0 := by
    ext j
    exact congrFun (congrArg Prod.snd hx) j
  have ht : tangent = 0 := htangent (by simpa using hzero)
  exact congrArg Subtype.val ht

/-- A nonzero normal in dimension `r+1` has an `r`-dimensional tangent dual. -/
theorem tangentDual_finrank [FiniteDimensional F V] (normal : V →ₗ[F] F)
    (hdim : Module.finrank F V = r + 1) (hnormal : normal ≠ 0) :
    Module.finrank F (Module.Dual F normal.ker) = r := by
  rw [Subspace.dual_finrank_eq]
  have hrange : LinearMap.range normal = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hnormal)
  have h := normal.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self, hdim] at h
  omega

end LinearAlgebra

variable {E : Type u} {L : Type v} [Field E] [BEq E] [LawfulBEq E] [Field L]
variable {n r k : ℕ}

/-- The executed formal differential of the chart equation. -/
def chartNormal (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L) :
    (Fin (r + 1) → L) →ₗ[L] L :=
  evaluatedDifferential base point chart.equation

/-- The pool consists of executed differentials of actual agreement polynomials. -/
def chartAgreementPool (chart : ChartData E r k) (domain received : Fin n → E)
    (base : E →+* L) (point : Fin (r + 1) → L) :
    (Fin (r + 1) → L) →ₗ[L] (Fin n → L) :=
  LinearMap.pi fun i ↦ evaluatedDifferential base point
    (chartAgreementRows chart domain received i)

/-- Actual agreement coordinate functionals restricted to the actual chart tangent space. -/
def tangentAgreementLabels (chart : ChartData E r k) (domain received : Fin n → E)
    (base : E →+* L) (point : Fin (r + 1) → L) :
    Fin n → Module.Dual L (chartNormal chart base point).ker :=
  coordinateFunctional ((chartAgreementPool chart domain received base point).comp
    (chartNormal chart base point).ker.subtype)

@[simp] theorem tangentAgreementLabels_apply (chart : ChartData E r k)
    (domain received : Fin n → E) (base : E →+* L) (point : Fin (r + 1) → L)
    (i : Fin n) (direction : (chartNormal chart base point).ker) :
    tangentAgreementLabels chart domain received base point i direction =
      evaluatedDifferential base point (chart.agreement (domain i) (received i)) direction.val :=
  rfl

/-- The actual chart tangent dual has the selected cardinality. -/
theorem chartTangentDual_finrank (chart : ChartData E r k) (base : E →+* L)
    (point : Fin (r + 1) → L) (hnormal : chartNormal chart base point ≠ 0) :
    Module.finrank L (Module.Dual L (chartNormal chart base point).ker) = r :=
  tangentDual_finrank _ (by simp) hnormal

/-- Spanning selected tangent labels give an injective executed square Jacobian. -/
theorem selectedChartSystem_jacobian_injective_of_span (chart : ChartData E r k)
    (domain received : Fin n → E) (base : E →+* L) (point : Fin (r + 1) → L)
    (selected : Finset (Fin n)) (hcard : selected.card = r)
    (hspan : Submodule.span L (tangentAgreementLabels chart domain received base point ''
      (↑selected : Set (Fin n))) = ⊤) :
    Function.Injective (evaluatedJacobianMap base point
      (selectedChartSystem chart domain received selected hcard)) := by
  have htangent := selectedCoordinateMap_injective_of_span
    ((chartAgreementPool chart domain received base point).comp
      (chartNormal chart base point).ker.subtype) selected hcard hspan
  have hinj := normalSelectedMap_injective_of_tangent
    (chartNormal chart base point) (chartAgreementPool chart domain received base point)
    (rowSubsetEmbedding selected hcard) htangent
  intro x y hxy
  apply hinj
  apply Prod.ext
  · exact congrFun hxy 0
  · funext j
    exact congrFun hxy j.succ

/-- The fixed gap on agreeing actual tangent labels supplies a robust full-span selection. -/
theorem exists_robust_tangent_selection (chart : ChartData E r k)
    (domain received : Fin n → E) (base : E →+* L) (point : Fin (r + 1) → L)
    (agreeing : Finset (Fin n)) (hn : 0 < n) (epsilon : Gap)
    (hnormal : chartNormal chart base point ≠ 0)
    (hgap : ∀ W : Submodule L (Module.Dual L (chartNormal chart base point).ker), W ≠ ⊤ →
      epsilon.val * n ≤
        (agreeingOutside
          (tangentAgreementLabels chart domain received base point) agreeing W).card) :
    ∃ S : Finset (Fin n), S ∈ robustSelections n hn r epsilon ∧ S ⊆ agreeing ∧
      S.card = r ∧ Submodule.span L
        (tangentAgreementLabels chart domain received base point '' (↑S : Set (Fin n))) = ⊤ :=
  exists_robustSelection_span_eq_top_of_finrank _ agreeing hn r
    (chartTangentDual_finrank chart base point hnormal) epsilon hgap

/-- Execute the robust index family as actual square chart systems. -/
def robustChartSystems [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) (epsilon : Gap) :
    Finset (Fin (r + 1) → CMvPolynomial (r + 1) E) :=
  (robustSelections n hn r epsilon).attach.image fun S ↦
    selectedChartSystem chart domain received S.val
      (robustSelections_card_eq hn r epsilon S.property)

/-- Membership exposes precisely the selected index set that the executable family used. -/
theorem mem_robustChartSystems [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) (epsilon : Gap)
    (system : Fin (r + 1) → CMvPolynomial (r + 1) E) :
    system ∈ robustChartSystems chart domain received hn epsilon ↔
      ∃ (S : Finset (Fin n)) (hS : S ∈ robustSelections n hn r epsilon),
        selectedChartSystem chart domain received S (robustSelections_card_eq hn r epsilon hS) =
          system := by
  simp [robustChartSystems]

/-- A robust selected index set materializes in the robust executable system family. -/
theorem selectedChartSystem_mem_robust [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) (epsilon : Gap)
    (S : Finset (Fin n)) (hcard : S.card = r)
    (hS : S ∈ robustSelections n hn r epsilon) :
    selectedChartSystem chart domain received S hcard ∈
      robustChartSystems chart domain received hn epsilon :=
  (mem_robustChartSystems chart domain received hn epsilon _).mpr ⟨S, hS, rfl⟩

/-- Select between the exhaustive and fixed-gap robust executable branches. -/
inductive SelectionMode where
  | allSubsets
  | robust (epsilon : Gap)

/-- Both branches materialize actual chart equations and actual agreement polynomials. -/
def chartSystems [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) :
    SelectionMode → Finset (Fin (r + 1) → CMvPolynomial (r + 1) E)
  | .allSubsets => directChartSystems chart domain received
  | .robust epsilon => robustChartSystems chart domain received hn epsilon

@[simp] theorem chartSystems_allSubsets [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) :
    chartSystems chart domain received hn .allSubsets = directChartSystems chart domain received :=
  rfl

@[simp] theorem chartSystems_robust [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (hn : 0 < n) (epsilon : Gap) :
    chartSystems chart domain received hn (.robust epsilon) =
      robustChartSystems chart domain received hn epsilon := rfl

/-- A robust selected actual common zero has a nonzero Jacobian and an isolation witness.
The equation, nonzero actual normal, fixed gap, and actual agreement zeros stay explicit. -/
theorem exists_robust_selectedChartSystem_capture [DecidableEq E] (chart : ChartData E r k)
    (domain received : Fin n → E) (base : E →+* L) (point : Fin (r + 1) → L)
    (agreeing : Finset (Fin n)) (hn : 0 < n) (epsilon : Gap)
    (hequation : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hnormal : chartNormal chart base point ≠ 0)
    (hagree : ∀ i ∈ agreeing,
      CMvPolynomial.eval₂ base point (chart.agreement (domain i) (received i)) = 0)
    (hgap : ∀ W : Submodule L (Module.Dual L (chartNormal chart base point).ker), W ≠ ⊤ →
      epsilon.val * n ≤
        (agreeingOutside
          (tangentAgreementLabels chart domain received base point) agreeing W).card) :
    ∃ (S : Finset (Fin n)) (hcard : S.card = r),
      S ∈ robustSelections n hn r epsilon ∧ S ⊆ agreeing ∧
      let system := selectedChartSystem chart domain received S hcard
      system ∈ robustChartSystems chart domain received hn epsilon ∧
        system ∈ chartSystems chart domain received hn (.robust epsilon) ∧
        system ∈ directChartSystems chart domain received ∧
        (∀ row, CMvPolynomial.eval₂ base point (system row) = 0) ∧
        (evaluatedJacobian base point system).det ≠ 0 ∧
        MvPolynomial.HasIsolatingPolynomial.{w, v}
          (ArkLib.Rojas.AffineSolver.mappedSystem base system) point := by
  obtain ⟨S, hS, hsub, hcard, hspan⟩ := exists_robust_tangent_selection
    chart domain received base point agreeing hn epsilon hnormal hgap
  have hmem := selectedChartSystem_mem_robust chart domain received hn epsilon S hcard hS
  refine ⟨S, hcard, hS, hsub, hmem, hmem, ?_⟩
  exact selectedChartSystem_capture chart domain received S hcard base point hequation
    (fun i hi ↦ hagree i (hsub hi))
    (selectedChartSystem_jacobian_injective_of_span chart domain received base point S hcard hspan)

end ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallChart
