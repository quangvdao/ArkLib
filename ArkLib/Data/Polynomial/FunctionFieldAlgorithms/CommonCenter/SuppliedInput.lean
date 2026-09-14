/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryTail
public import ArkLib.Data.MvPolynomial.BoundedGCD.FunctionFieldBridge

/-!
# Supplied first-order equations over the stored function field

The executable substitution sends the supplied coordinates `[X,Y,Z]` to the stored
function-field coefficient `X`, inner message variable `Y`, and outer derivative variable `Z`.
The final nested representation reuses the ordinary bivariate conversion.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.SuppliedInput

open CompPoly CPolynomial CPoly
open BivariateReducedSupport

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- Executable embedding of scalar coefficients into the stored function field. -/
def constantHom : F →+* StoredField.Carrier F where
  toFun a := StoredField.ofPolynomial (CPolynomial.C a)
  map_zero' := by apply StoredField.value_injective; simp [CPolynomial.toPoly_zero]
  map_one' := by apply StoredField.value_injective; simp [CPolynomial.C_toPoly]
  map_add' a b := by apply StoredField.value_injective; simp [CPolynomial.C_toPoly]
  map_mul' a b := by apply StoredField.value_injective; simp [CPolynomial.C_toPoly]

/-- The challenge variable remains symbolic in the coefficient field. -/
def challenge : StoredField.Carrier F := StoredField.ofPolynomial CPolynomial.X

/-- Substitute the challenge variable into coefficients, keeping both state variables. -/
def stateHom : CMvPolynomial 3 F →+* CMvPolynomial 2 (StoredField.Carrier F) :=
  CMvPolynomial.eval₂Hom (CPoly.TaylorReconstruction.coefficientConstant.comp constantHom)
    ![CMvPolynomial.C challenge, CMvPolynomial.X 0, CMvPolynomial.X 1]

/-- Convert an actual supplied first-order interpolant to the generic state preparation input. -/
def equationHom : CMvPolynomial 3 F →+* CBivariate (StoredField.Carrier F) :=
  fromOrdinaryHom.comp stateHom

/-- Actual converted equation with message state inner and derivative state outer. -/
def equation (Q : CMvPolynomial 3 F) : CBivariate (StoredField.Carrier F) := equationHom Q

/-- Scalar embedding into the semantic nested polynomial ring. -/
noncomputable def scalarHom : F →+* (Polynomial (StoredField.Carrier F))[X] :=
  (Polynomial.C.comp Polynomial.C).comp constantHom

/-- Semantic challenge, message, and derivative-state coordinates. -/
noncomputable def stateVariables : Fin 3 → (Polynomial (StoredField.Carrier F))[X] :=
  ![Polynomial.C (Polynomial.C challenge), Polynomial.C Polynomial.X, Polynomial.X]

private theorem storedEquiv_apply (Q : CMvPolynomial 2 (StoredField.Carrier F)) :
    CPoly.polyRingEquiv Q = fromCMvPolynomial Q := rfl

/-- Full polynomial semantics of the executable supplied-input conversion. -/
theorem equation_toPoly (Q : CMvPolynomial 3 F) :
    CBivariate.toPoly (equation Q) =
      MvPolynomial.eval₂ scalarHom stateVariables (fromCMvPolynomial Q) := by
  classical
  let h := CBivariate.toPolyRingHom (R := StoredField.Carrier F)
  rw [equation, equationHom, RingHom.comp_apply]
  change h (fromOrdinaryCMv (stateHom Q)) = _
  rw [fromOrdinaryCMv, CPoly.eval₂_equiv]
  rw [MvPolynomial.eval₂_comp_left]
  rw [stateHom, CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv]
  change ((MvPolynomial.eval₂Hom (h.comp (CHom.comp CHom))
    (fun i => h (![CPolynomial.C CPolynomial.X, CPolynomial.X] i))).comp
    CPoly.polyRingEquiv.toRingHom) _ = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [h, scalarHom, constantHom, CPoly.TaylorReconstruction.coefficientConstant,
      storedEquiv_apply,
      CMvPolynomial.fromCMvPolynomial_C, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;>
      simp [h, stateVariables, storedEquiv_apply,
      CMvPolynomial.fromCMvPolynomial_C, CMvPolynomial.fromCMvPolynomial_X,
        CBivariate.toPolyRingHom, CBivariate.ringEquiv,
        CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- Evaluation compatibility over every extension of the stored coefficient field. -/
theorem equation_evalAt (Q : CMvPolynomial 3 F)
    {K : Type*} [Field K] (embedding : StoredField.Carrier F →+* K) (u v : K) :
    RegularPart.evalAt embedding u v (equation Q) =
      MvPolynomial.eval₂ (embedding.comp constantHom)
        ![embedding challenge, u, v] (fromCMvPolynomial Q) := by
  rw [RegularPart.evalAt, equation_toPoly]
  let h := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom embedding u) v
  change h _ = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [h, scalarHom]
  · funext i
    fin_cases i <;> simp [h, stateVariables]

private theorem outer_derivative_semantics (Q : MvPolynomial (Fin 3) F) :
    (MvPolynomial.eval₂ scalarHom stateVariables Q).derivative =
      MvPolynomial.eval₂ scalarHom stateVariables (MvPolynomial.pderiv 2 Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [scalarHom]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    fin_cases i <;> simp [stateVariables] at hP ⊢ <;> simp [hP, mul_comm, add_comm]

/-- The highest supplied state partial is exactly the outer derivative after conversion. -/
theorem equation_partialDerivative_Z (Q : CMvPolynomial 3 F) :
    equation (CMvPolynomial.partialDerivative 2 Q) = CBivariate.partialDerivY (equation Q) := by
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly _ = CBivariate.toPoly _
  rw [CBivariate.partialDerivY_toPoly, equation_toPoly, equation_toPoly,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]
  exact (outer_derivative_semantics (fromCMvPolynomial Q)).symm

private def storedScalarHom : F →+* CBivariate (StoredField.Carrier F) :=
  (CHom.comp CHom).comp constantHom

private def storedVariables : Fin 3 → CBivariate (StoredField.Carrier F) :=
  ![CPolynomial.C (CPolynomial.C challenge), CPolynomial.C CPolynomial.X, CPolynomial.X]

private theorem equation_stored_semantics (Q : CMvPolynomial 3 F) :
    equation Q = MvPolynomial.eval₂ storedScalarHom storedVariables (fromCMvPolynomial Q) := by
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly _ = CBivariate.toPoly _
  rw [equation_toPoly]
  let h := CBivariate.toPolyRingHom (R := StoredField.Carrier F)
  change _ = h _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [h, scalarHom, storedScalarHom, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;> simp [h, stateVariables, storedVariables, CBivariate.toPolyRingHom,
      CBivariate.ringEquiv, CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

private theorem inner_derivative_C (c : CPolynomial (StoredField.Carrier F)) :
    CBivariate.partialDerivX (CPolynomial.C c) = CPolynomial.C (CPolynomial.derivative c) := by
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly _ = CBivariate.toPoly _
  apply Polynomial.ext
  intro n
  rw [CBivariate.partialDerivX_toPoly]
  simp only [CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, Polynomial.map_C,
    Polynomial.coeff_C]
  split_ifs <;> simp [CPolynomial.derivative_toPoly]

private theorem inner_derivative_X :
    CBivariate.partialDerivX (CPolynomial.X : CBivariate (StoredField.Carrier F)) = 0 := by
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly _ = CBivariate.toPoly _
  apply Polynomial.ext
  intro n
  rw [CBivariate.partialDerivX_toPoly]
  rw [CBivariate.toPoly_zero, Polynomial.coeff_zero]
  simp only [CBivariate.toPoly_eq_map, CPolynomial.X_toPoly, Polynomial.map_X,
    Polynomial.coeff_X]
  split_ifs <;> simp

private theorem stored_derivative_X :
    CPolynomial.derivative (CPolynomial.X : CPolynomial (StoredField.Carrier F)) = 1 := by
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.derivative_toPoly, CPolynomial.X_toPoly,
    Polynomial.derivative_X, CPolynomial.toPoly_one]

private theorem inner_derivative_semantics (Q : MvPolynomial (Fin 3) F) :
    CBivariate.partialDerivX (MvPolynomial.eval₂ storedScalarHom storedVariables Q) =
      MvPolynomial.eval₂ storedScalarHom storedVariables (MvPolynomial.pderiv 1 Q) := by
  classical
  have hC1 : (CPolynomial.C (1 : CPolynomial (StoredField.Carrier F)) :
      CBivariate (StoredField.Carrier F)) = 1 := CPolynomial.CHom.map_one
  induction Q using MvPolynomial.induction_on with
  | C c => simp [storedScalarHom, inner_derivative_C, CPolynomial.derivative_C]
  | add P Q hP hQ => simp [CBivariate.partialDerivX_add, hP, hQ]
  | mul_X P i hP =>
    simp only [storedVariables] at hP
    fin_cases i <;>
      simp [storedVariables, CBivariate.partialDerivX_mul, inner_derivative_C,
        inner_derivative_X, CPolynomial.derivative_C, stored_derivative_X, hP, mul_comm, hC1]

/-- The message-state partial is exactly coefficientwise inner differentiation after conversion. -/
theorem equation_partialDerivative_Y (Q : CMvPolynomial 3 F) :
    equation (CMvPolynomial.partialDerivative 1 Q) = CBivariate.partialDerivX (equation Q) := by
  rw [equation_stored_semantics, equation_stored_semantics,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]
  exact (inner_derivative_semantics (fromCMvPolynomial Q)).symm

/-- Semantic state substitution before the nested bivariate conversion. -/
theorem stateHom_semantics (Q : CMvPolynomial 3 F) :
    fromCMvPolynomial (stateHom Q) =
      MvPolynomial.eval₂ (MvPolynomial.C.comp constantHom)
        ![MvPolynomial.C challenge, MvPolynomial.X 0, MvPolynomial.X 1]
        (fromCMvPolynomial Q) := by
  rw [stateHom, CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv]
  change (CPoly.polyRingEquiv (n := 2) (R := StoredField.Carrier F)).toRingHom _ = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [TaylorReconstruction.coefficientConstant, storedEquiv_apply,
      CMvPolynomial.fromCMvPolynomial_C]
  · funext i
    fin_cases i <;> simp [storedEquiv_apply, CMvPolynomial.fromCMvPolynomial_C,
      CMvPolynomial.fromCMvPolynomial_X]

private noncomputable def rationalStateHom :
    MvPolynomial (Fin 3) F →+* MvPolynomial (Fin 2) (RatFunc F) :=
  (MvPolynomial.map (algebraMap (Polynomial F) (RatFunc F))).comp
    ((MvPolynomial.optionEquivRight F (Fin 2)).toRingHom.comp
      (MvPolynomial.rename (finSuccEquiv' (0 : Fin 3))).toRingHom)

private theorem rationalStateHom_eq : rationalStateHom (F := F) =
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (StoredField.valueHom.comp constantHom))
      ![MvPolynomial.C (StoredField.value challenge), MvPolynomial.X 0, MvPolynomial.X 1] := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rationalStateHom, constantHom,
      StoredField.valueHom, CPolynomial.C_toPoly]
  · intro i
    have hindex : (finSuccEquiv' (0 : Fin 3) : Fin 3 → Option (Fin 2)) =
        ![none, some 0, some 1] := by
      funext j
      fin_cases j <;> rfl
    fin_cases i <;> simp [rationalStateHom, hindex, challenge, CPolynomial.X_toPoly]

/-- Making the challenge coordinate a rational-function coefficient does not lose any
nonzero supplied polynomial. -/
theorem stateHom_injective : Function.Injective (stateHom (F := F)) := by
  intro Q R h
  apply fromCMvPolynomial_injective
  apply (MvPolynomial.rename_injective (finSuccEquiv' (0 : Fin 3))
    (finSuccEquiv' (0 : Fin 3)).injective)
  apply (MvPolynomial.optionEquivRight F (Fin 2)).injective
  apply (MvPolynomial.map_injective (algebraMap (Polynomial F) (RatFunc F))
    (RatFunc.algebraMap_injective F))
  change rationalStateHom (fromCMvPolynomial Q) = rationalStateHom (fromCMvPolynomial R)
  rw [rationalStateHom_eq]
  have hs := congrArg (fun S => MvPolynomial.map StoredField.valueHom
    (fromCMvPolynomial S)) h
  rw [stateHom_semantics, stateHom_semantics, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_comp_left] at hs
  have hcoeff : (MvPolynomial.map (σ := Fin 2) StoredField.valueHom).comp
      (MvPolynomial.C.comp (constantHom (F := F))) =
      MvPolynomial.C.comp (StoredField.valueHom.comp constantHom) := by
    ext a
    simp
  have hvars : (⇑(MvPolynomial.map (σ := Fin 2) (StoredField.valueHom (F := F))) ∘
      ![MvPolynomial.C challenge, MvPolynomial.X 0, MvPolynomial.X 1]) =
      ![MvPolynomial.C (StoredField.value challenge), MvPolynomial.X 0, MvPolynomial.X 1] := by
    funext i
    fin_cases i <;> simp [StoredField.valueHom]
  rw [hcoeff, hvars] at hs
  exact hs

private theorem fromOrdinaryCMv_injective {E : Type*} [Field E] [BEq E] [LawfulBEq E] :
    Function.Injective (fromOrdinaryCMv (F := E)) := by
  classical
  let h : CBivariate E →+* MvPolynomial (Fin 2) E := (Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (MvPolynomial.C : E →+* MvPolynomial (Fin 2) E)
      (MvPolynomial.X (0 : Fin 2)))
      (MvPolynomial.X (1 : Fin 2))).comp CBivariate.toPolyRingHom
  have hleft (Q : CMvPolynomial 2 E) : h (fromOrdinaryCMv Q) = fromCMvPolynomial Q := by
    rw [fromOrdinaryCMv, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
    have hc : h.comp (CHom.comp CHom) = MvPolynomial.C := by
      ext a
      simp [h, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
        CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
    have hv : (⇑h ∘ ![CPolynomial.C CPolynomial.X, CPolynomial.X]) = MvPolynomial.X := by
      funext i
      fin_cases i <;> simp [h, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
        CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]
    rw [hc, hv, MvPolynomial.eval₂_eta]
  intro Q R heq
  apply fromCMvPolynomial_injective
  rw [← hleft Q, ← hleft R, heq]

/-- The full executable trivariate-to-function-field conversion is injective. -/
theorem equation_injective : Function.Injective (equation (F := F)) := by
  intro Q R h
  apply stateHom_injective
  apply fromOrdinaryCMv_injective
  exact h

/-- Nonzero supplied equations remain nonzero after conversion. -/
theorem equation_ne_zero {Q : CMvPolynomial 3 F} (hQ : Q ≠ 0) : equation Q ≠ 0 := by
  intro h
  apply hQ
  apply equation_injective
  exact h.trans equationHom.map_zero.symm

/-- Specializing the two states to a polynomial and its derivative agrees with the supplied
first-order polynomial graph equation, embedded into the rational-function field. -/
theorem equation_graph (Q : CMvPolynomial 3 F) (P : Polynomial F) :
    RegularPart.evalAt StoredField.valueHom
      (algebraMap (Polynomial F) (RatFunc F) P)
      (algebraMap (Polynomial F) (RatFunc F) P.derivative) (equation Q) =
      algebraMap (Polynomial F) (RatFunc F)
        (MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P, P.derivative]
          (fromCMvPolynomial Q)) := by
  rw [equation_evalAt, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [StoredField.valueHom, constantHom, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;> simp [StoredField.valueHom, challenge, CPolynomial.X_toPoly]

/-- Execute ordinary/regular preparation directly on the supplied first-order interpolant.
The characteristic guard makes inverse Frobenius unnecessary in this call. -/
def run (p : ℕ) (Q : CMvPolynomial 3 F) : OrdinaryTail.Result (StoredField.Carrier F) :=
  OrdinaryTail.run p id (equation Q)

/-- The actual supplied-input producer succeeds, returns a nonzero ordinary equation, and
partitions every polynomial solution of the supplied first-order equation. -/
theorem run_exists_partition (p : ℕ) [Fact p.Prime] [CharP F p]
    (Q : CMvPolynomial 3 F) (hQ : Q ≠ 0)
    (hdegree : (ClearDenominators.primitivePart (equation Q)).natDegree < p) :
    ∃ data, run p Q = .prepared data ∧ data.ordinary ≠ 0 ∧
      ∀ P : Polynomial F,
        MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P, P.derivative]
          (fromCMvPolynomial Q) = 0 →
        data.ordinary.toPoly.eval₂ StoredField.valueHom
          (algebraMap (Polynomial F) (RatFunc F) P) = 0 ∨
          (RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative) data.regular = 0 ∧
           RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative)
              (CBivariate.partialDerivY data.regular) ≠ 0) := by
  let : CharP (StoredField.Carrier F) p :=
    charP_of_injective_ringHom (constantHom (F := F)).injective p
  obtain ⟨data, hr, hc⟩ := OrdinaryTail.run_exists_partition p id (equation Q)
    (equation_ne_zero hQ) hdegree
  refine ⟨data, hr, OrdinaryTail.run_ordinary_ne_zero p id (equation Q)
    (equation_ne_zero hQ) hdegree data hr, ?_⟩
  intro P hP
  apply hc StoredField.valueHom
    (algebraMap (Polynomial F) (RatFunc F) P)
    (algebraMap (Polynomial F) (RatFunc F) P.derivative)
  rw [equation_graph, hP, _root_.map_zero]

end Polynomial.FunctionFieldAlgorithms.CommonCenter.SuppliedInput
