/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.VaryingOrder
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.SingularRecursion

/-!
# Semantic correctness and complete traversal of concrete separant stages

`Coverage` executes partial derivatives on stored `CMvPolynomial` equations. This file proves
that its highest-active-variable scan and every stored derivative agree with the semantic
differential-polynomial operations. Below the characteristic, the semantic jet-degree measure
strictly decreases at every emitted stage and bounds the length of the concrete scan.

The final coverage theorem uses that measure as fuel. Every bounded polynomial solution of a
nonzero input equation reaches an actual emitted stage where the equation vanishes and its
separant specialization does not. Thus singular solutions continue to later stages, while a
nonzero terminal equation cannot retain a bounded solution. No stage or terminal condition is
supplied by the caller.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CPoly PolynomialDifferential

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

private theorem finToJetVariable_eq_finSuccEquiv (r : ℕ) :
    finToJetVariable r = ⇑(_root_.finSuccEquiv (r + 1)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem finToJetVariable_injective (r : ℕ) :
    Function.Injective (finToJetVariable r) := by
  rw [finToJetVariable_eq_finSuccEquiv]
  exact (_root_.finSuccEquiv (r + 1)).injective

private theorem rename_eq_of_eq_on_vars {R σ τ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (f g : σ → τ) (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.rename f p = MvPolynomial.rename g p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp_rw [map_sum, MvPolynomial.rename_monomial]
  apply Finset.sum_congr rfl
  intro u hu
  congr 2
  exact Finsupp.mapDomain_congr fun i hi =>
    h i (MvPolynomial.support_subset_vars_of_mem_support hu hi)

/-- A concrete stored derivative in `Y_j` is exactly the semantic separant in `Y_j`. -/
theorem semanticEquation_partialDerivative {r : ℕ}
    (equation : CMvPolynomial (r + 2) E) (j : Fin (r + 1)) :
    semanticEquation (CMvPolynomial.partialDerivative j.succ equation) =
      separant (semanticEquation equation) j := by
  unfold semanticEquation separant
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative]
  symm
  exact MvPolynomial.pderiv_rename (finToJetVariable_injective r) j.succ _

/-- The concrete-to-semantic coordinate change reflects the zero polynomial. -/
theorem semanticEquation_eq_zero_iff {r : ℕ} (equation : CMvPolynomial (r + 2) E) :
    semanticEquation equation = 0 ↔ equation = 0 := by
  unfold semanticEquation
  rw [MvPolynomial.rename_eq_zero_iff_of_injective _ (finToJetVariable_injective r)]
  constructor
  · intro h
    apply CPoly.fromCMvPolynomial_injective
    simpa using h
  · rintro rfl
    simp

/-- Below the characteristic, a literal nonzero concrete derivative is equivalent to semantic
dependence on the corresponding jet variable. -/
theorem concreteDerivative_ne_zero_iff_dependsOnJet {r : ℕ}
    (equation : CMvPolynomial (r + 2) E) (j : Fin (r + 1))
    (hchar : jetDegree (semanticEquation equation) j < ringChar E) :
    CMvPolynomial.partialDerivative j.succ equation ≠ 0 ↔
      DependsOnJet (semanticEquation equation) j := by
  constructor
  · intro hder
    have hsemantic : separant (semanticEquation equation) j ≠ 0 := by
      rw [← semanticEquation_partialDerivative]
      intro hz
      exact hder ((semanticEquation_eq_zero_iff _).mp hz)
    rw [DependsOnJet]
    apply Nat.pos_of_ne_zero
    intro hdegree
    apply hsemantic
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    simpa [jetDegree] using hdegree
  · intro hdep
    have hsep := separant_ne_zero_of_dependsOnJet_of_lt_ringChar
      _ _ hdep hchar
    intro hzero
    apply hsep
    rw [← semanticEquation_partialDerivative]
    exact (semanticEquation_eq_zero_iff _).mpr hzero

variable [DecidableEq E]

/-- Under the inherited characteristic contract, concrete termination is exactly semantic
independence of all jet variables. -/
theorem highestConcreteActive?_eq_none_iff {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    highestConcreteActive? equation = none ↔
      highestActiveJet (semanticEquation equation) = none := by
  rw [highestConcreteActive?, List.find?_eq_none, highestActiveJet_eq_none_iff]
  simp only [List.mem_reverse, List.mem_finRange, forall_const, bne_iff_ne]
  constructor
  · intro h j hdep
    exact h j ((concreteDerivative_ne_zero_iff_dependsOnJet equation j (hchar.2 j)).mpr hdep)
  · intro h j
    by_contra hder
    exact h j ((concreteDerivative_ne_zero_iff_dependsOnJet equation j (hchar.2 j)).mp hder)

/-- If the semantic highest active jet is `s`, the descending concrete scan returns that exact
stored coordinate. -/
theorem highestConcreteActive?_eq_some_of_highestActiveJet_eq_some {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation))
    (s : Fin (r + 1)) (hs : highestActiveJet (semanticEquation equation) = some s) :
    highestConcreteActive? equation = some s := by
  rw [highestConcreteActive?, List.find?_eq_some_iff_getElem]
  have hhighest := isHighestActiveJet_of_highestActiveJet_eq_some hs
  refine ⟨by simpa only [bne_iff_ne] using
      (concreteDerivative_ne_zero_iff_dependsOnJet equation s (hchar.2 s)).mpr hhighest.1,
    r - s.val, ?_, ?_, ?_⟩
  · simp
  · apply Fin.ext
    rw [List.getElem_reverse, List.getElem_finRange]
    simp
    omega
  · intro q hq
    have hqbound : q < (List.finRange (r + 1)).reverse.length := by
      simp
      omega
    let t := (List.finRange (r + 1)).reverse[q]
    have htval : t.val = r - q := by
      dsimp [t]
      rw [List.getElem_reverse, List.getElem_finRange]
      simp
    have hst : s < t := by
      apply Fin.lt_def.mpr
      rw [htval]
      omega
    have hnotdep := hhighest.2 t hst
    have hzero : CMvPolynomial.partialDerivative t.succ equation = 0 := by
      by_contra hne
      exact hnotdep
        ((concreteDerivative_ne_zero_iff_dependsOnJet equation t (hchar.2 t)).mp hne)
    change (!(CMvPolynomial.partialDerivative t.succ equation != 0)) = true
    simp [hzero]

/-- The executable descending scan and the semantic maximum select the same active jet. -/
theorem highestConcreteActive?_eq_highestActiveJet {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    highestConcreteActive? equation = highestActiveJet (semanticEquation equation) := by
  cases hs : highestActiveJet (semanticEquation equation) with
  | none => exact (highestConcreteActive?_eq_none_iff equation hchar).mpr hs
  | some s =>
      exact highestConcreteActive?_eq_some_of_highestActiveJet_eq_some equation hchar s hs

omit [DecidableEq E] in
/-- The executable prefix equation exactly represents any stage whose recorded active jet is its
semantic highest active jet. -/
theorem VaryingOrder.prefixEquation_represents {r : ℕ} (stage : ConcreteStage E r)
    (hs : highestActiveJet (semanticEquation stage.equation) = some stage.activeJet) :
    VaryingOrder.Represents stage (VaryingOrder.prefixEquation stage) := by
  unfold VaryingOrder.Represents VaryingOrder.prefixEquation semanticEquation
  rw [CPoly.fromCMvPolynomial_rename, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename]
  apply rename_eq_of_eq_on_vars
  intro i hi
  simp only [Function.comp_apply]
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
      simp only [finToJetVariable]
      have hdegree : MvPolynomial.degreeOf j.succ
          (CPoly.fromCMvPolynomial stage.equation) ≠ 0 :=
        MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi
      have hdep : DependsOnJet (semanticEquation stage.equation) j := by
        rw [DependsOnJet, jetDegree, semanticEquation]
        change 0 < MvPolynomial.degreeOf (finToJetVariable r j.succ)
          (MvPolynomial.rename (finToJetVariable r)
            (CPoly.fromCMvPolynomial stage.equation))
        rw [MvPolynomial.degreeOf_rename_of_injective (finToJetVariable_injective r)]
        exact Nat.pos_of_ne_zero hdegree
      have hjle : j ≤ stage.activeJet := le_of_not_gt fun hj =>
        (isHighestActiveJet_of_highestActiveJet_eq_some hs).2 j hj hdep
      have hj : j.val ≤ stage.activeJet.val := Fin.le_def.mp hjle
      simp only [VaryingOrder.prefixIndex]
      rw [dif_pos (by change j.val + 1 < stage.activeJet.val + 2; omega)]
      apply congrArg some
      apply Fin.ext
      rfl

omit [DecidableEq E] in
/-- Every concrete stage's literal successor denotes its semantic separant. -/
theorem ConcreteStage.semantic_successor {r : ℕ} (stage : ConcreteStage E r) :
    semanticEquation
        (CMvPolynomial.partialDerivative stage.activeJet.succ stage.equation) =
      separant (semanticEquation stage.equation) stage.activeJet :=
  semanticEquation_partialDerivative stage.equation stage.activeJet

/-- Every emitted stage inherits the characteristic contract and records its exact semantic
highest active jet. -/
theorem mem_enumerateStagesFrom_semantic_contract {r D index fuel : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation))
    (stage : ConcreteStage E r) (hstage : stage ∈ enumerateStagesFrom index fuel equation) :
    IsBelowCharacteristic D (semanticEquation stage.equation) ∧
      highestActiveJet (semanticEquation stage.equation) = some stage.activeJet := by
  induction fuel generalizing index equation stage with
  | zero => simp [enumerateStagesFrom] at hstage
  | succ fuel ih =>
      simp only [enumerateStagesFrom] at hstage
      cases hc : highestConcreteActive? equation with
      | none => simp [hc] at hstage
      | some j =>
          simp only [hc, List.mem_cons] at hstage
          rcases hstage with rfl | hstage
          · exact ⟨hchar,
              (highestConcreteActive?_eq_highestActiveJet equation hchar).symm.trans hc⟩
          · have hnextChar : IsBelowCharacteristic D
                (semanticEquation (CMvPolynomial.partialDerivative j.succ equation)) := by
              rw [semanticEquation_partialDerivative]
              exact isBelowCharacteristic_separant _ _ hchar
            exact ih (index := index + 1)
              (equation := CMvPolynomial.partialDerivative j.succ equation)
              (stage := stage) hnextChar hstage

/-- `prefixEquation` is exact on every concrete stage emitted from an equation satisfying the
characteristic contract. -/
theorem VaryingOrder.prefixEquation_exactOn_enumerateStages {r D fuel : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    VaryingOrder.EquationProducer.ExactOn (VaryingOrder.prefixEquation (E := E))
      (enumerateStages fuel equation) := by
  intro stage hstage
  apply VaryingOrder.prefixEquation_represents
  exact (mem_enumerateStagesFrom_semantic_contract equation hchar stage hstage).2

/-- In particular, the canonical sufficient-fuel stage family needs no caller-supplied equation
producer exactness certificate. -/
theorem VaryingOrder.prefixEquation_exactOn_canonicalStages {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    VaryingOrder.EquationProducer.ExactOn (VaryingOrder.prefixEquation (E := E))
      (enumerateStages (jetDegreeMeasure (semanticEquation equation)) equation) :=
  VaryingOrder.prefixEquation_exactOn_enumerateStages equation hchar

/-- An emitted derivative strictly decreases the semantic sum of individual jet degrees. -/
theorem jetDegreeMeasure_semantic_partialDerivative_lt {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E) (j : Fin (r + 1))
    (hj : highestConcreteActive? equation = some j)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    jetDegreeMeasure
        (semanticEquation (CMvPolynomial.partialDerivative j.succ equation)) <
      jetDegreeMeasure (semanticEquation equation) := by
  rw [semanticEquation_partialDerivative]
  apply jetDegreeMeasure_separant_lt
  · exact (isHighestActiveJet_of_highestActiveJet_eq_some
      ((highestConcreteActive?_eq_highestActiveJet equation hchar).symm.trans hj)).1
  · exact hchar.2 j

/-- The concrete scan length is bounded by the initial semantic jet-degree measure, independently
of the requested fuel. -/
theorem length_enumerateStagesFrom_le_jetDegreeMeasure {r D : ℕ} (index fuel : ℕ)
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    (enumerateStagesFrom index fuel equation).length ≤
      jetDegreeMeasure (semanticEquation equation) := by
  induction fuel generalizing index equation with
  | zero => simp [enumerateStagesFrom]
  | succ fuel ih =>
      simp only [enumerateStagesFrom]
      cases hc : highestConcreteActive? equation with
      | none => simp
      | some j =>
          simp only [List.length_cons]
          have hsemantic := semanticEquation_partialDerivative equation j
          have hnextChar : IsBelowCharacteristic D
              (semanticEquation (CMvPolynomial.partialDerivative j.succ equation)) := by
            rw [hsemantic]
            exact isBelowCharacteristic_separant _ _ hchar
          have hrec := ih (index + 1)
            (CMvPolynomial.partialDerivative j.succ equation) hnextChar
          have hlt := jetDegreeMeasure_semantic_partialDerivative_lt equation j hc hchar
          omega

/-- The same semantic measure bounds the public scan from index zero. -/
theorem length_enumerateStages_le_jetDegreeMeasure {r D fuel : ℕ}
    (equation : CMvPolynomial (r + 2) E)
    (hchar : IsBelowCharacteristic D (semanticEquation equation)) :
    (enumerateStages fuel equation).length ≤ jetDegreeMeasure (semanticEquation equation) :=
  length_enumerateStagesFrom_le_jetDegreeMeasure 0 fuel equation hchar

/-- Any fuel at least the semantic jet-degree measure makes the concrete scan reach a regular
stage for every bounded solution. The returned witness is an actual emitted stage, carries its
actual active order, and has both the vanishing stage equation and nonvanishing separant
specialization. -/
theorem exists_regular_stage_in_enumerateStagesFrom {r D index fuel : ℕ}
    (equation : CMvPolynomial (r + 2) E) (hQ : semanticEquation equation ≠ 0)
    (hchar : IsBelowCharacteristic D (semanticEquation equation))
    (P : Polynomial E) (hdegree : P ∈ Polynomial.degreeLT E (D + 1))
    (hsolution : differentialSpecialization (semanticEquation equation) P = 0)
    (hfuel : jetDegreeMeasure (semanticEquation equation) ≤ fuel) :
    ∃ stage ∈ enumerateStagesFrom index fuel equation,
      differentialSpecialization (semanticEquation stage.equation) P = 0 ∧
      differentialSpecialization
        (separant (semanticEquation stage.equation) stage.activeJet) P ≠ 0 ∧
      highestActiveJet (semanticEquation stage.equation) = some stage.activeJet := by
  cases fuel with
  | zero =>
      have hm : jetDegreeMeasure (semanticEquation equation) = 0 := by omega
      cases hs : highestActiveJet (semanticEquation equation) with
      | none =>
          exact (hQ (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none
            (semanticEquation equation) hs ⟨⟨P, hdegree⟩, hsolution⟩)).elim
      | some j =>
          have hc : highestConcreteActive? equation = some j :=
            highestConcreteActive?_eq_some_of_highestActiveJet_eq_some equation hchar j hs
          have hlt := jetDegreeMeasure_semantic_partialDerivative_lt equation j hc hchar
          omega
  | succ fuel =>
      cases hs : highestActiveJet (semanticEquation equation) with
      | none =>
          exact (hQ (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none
            (semanticEquation equation) hs ⟨⟨P, hdegree⟩, hsolution⟩)).elim
      | some j =>
          have hc : highestConcreteActive? equation = some j :=
            highestConcreteActive?_eq_some_of_highestActiveJet_eq_some equation hchar j hs
          rw [enumerateStagesFrom, hc]
          by_cases hregular : differentialSpecialization
              (separant (semanticEquation equation) j) P ≠ 0
          · exact ⟨⟨index, equation, j⟩, List.mem_cons_self, hsolution, hregular, hs⟩
          · have hsingular : differentialSpecialization
                (separant (semanticEquation equation) j) P = 0 :=
              Classical.not_not.mp hregular
            let nextEquation := CMvPolynomial.partialDerivative j.succ equation
            have hnextSemantic : semanticEquation nextEquation =
                separant (semanticEquation equation) j :=
              semanticEquation_partialDerivative equation j
            have hnextQ : semanticEquation nextEquation ≠ 0 := by
              rw [hnextSemantic]
              exact separant_ne_zero_of_highestActiveJet_eq_some _ _ hs (hchar.2 j)
            have hnextChar : IsBelowCharacteristic D (semanticEquation nextEquation) := by
              rw [hnextSemantic]
              exact isBelowCharacteristic_separant _ _ hchar
            have hnextSolution : differentialSpecialization
                (semanticEquation nextEquation) P = 0 := by
              rw [hnextSemantic]
              exact hsingular
            have hnextFuel : jetDegreeMeasure (semanticEquation nextEquation) ≤ fuel := by
              change jetDegreeMeasure
                (semanticEquation (CMvPolynomial.partialDerivative j.succ equation)) ≤ fuel
              have hlt :=
                jetDegreeMeasure_semantic_partialDerivative_lt equation j hc hchar
              omega
            obtain ⟨stage, hstage, hsolve, hsep, hhighest⟩ :=
              exists_regular_stage_in_enumerateStagesFrom nextEquation hnextQ hnextChar
                P hdegree hnextSolution hnextFuel
            exact ⟨stage, List.mem_cons_of_mem _ hstage, hsolve, hsep, hhighest⟩
termination_by fuel

/-- Canonical sufficient-fuel traversal: every bounded solution reaches a regular concrete stage
using exactly the input equation's semantic jet-degree measure as fuel. -/
theorem enumerateStages_regular_coverage {r D : ℕ}
    (equation : CMvPolynomial (r + 2) E) (hQ : semanticEquation equation ≠ 0)
    (hchar : IsBelowCharacteristic D (semanticEquation equation))
    (P : BoundedSolution (semanticEquation equation) D) :
    ∃ stage ∈ enumerateStages (jetDegreeMeasure (semanticEquation equation)) equation,
      differentialSpecialization (semanticEquation stage.equation) P.polynomial = 0 ∧
      differentialSpecialization
        (separant (semanticEquation stage.equation) stage.activeJet) P.polynomial ≠ 0 ∧
      highestActiveJet (semanticEquation stage.equation) = some stage.activeJet :=
  exists_regular_stage_in_enumerateStagesFrom equation hQ hchar P.polynomial P.1.2
    P.equation le_rfl

end ReedSolomon.HiddenDerivative.FastTaylor
