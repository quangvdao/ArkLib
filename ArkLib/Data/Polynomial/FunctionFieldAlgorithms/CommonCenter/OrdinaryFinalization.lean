/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.SuppliedInput
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness

/-!
# Finalizing the computed ordinary tail

Canonical coefficient denominators are cleared before the existing executable Radical and
SeparablePart stages. The output guard includes the clearing denominator and the computed
leading-coefficient/resultant obstruction. Constant regular parts give a graph-free branch.
The small-degree entrypoint uses no inverse-Frobenius callback. Its ordinary-degree bound is
on the computed descent; transport from the paper's input jet bound remains separate.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryFinalization

open CompPoly CPolynomial CPoly BivariateReducedSupport

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- The actual global ordinary equation supplied to normalization, in `[X,Y]` order. -/
def input (raw : CPolynomial (StoredField.Carrier F)) : CMvPolynomial 2 F :=
  CBivariate.toOrdinaryCMv (ClearDenominators.clear raw).global

/-- Execute ordinary Radical and SeparablePart after canonical denominator clearing. -/
def finalize (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F)) :
    OrdinaryNormalization.Result F :=
  OrdinaryNormalization.run p inverse (input raw)

/-- Common-center guard, including every canonical coefficient denominator of the raw tail. -/
def guard (raw : CPolynomial (StoredField.Carrier F))
    (result : OrdinaryNormalization.Result F) : CPolynomial F :=
  (ClearDenominators.clear raw).scale *
    match result with
    | .normalized data => data.obstruction
    | _ => 1

/-- The denominator-cleared input retains the actual computed bivariate equation. -/
theorem input_eq (raw : CPolynomial (StoredField.Carrier F)) :
    fromOrdinaryCMv (input raw) = (ClearDenominators.clear raw).global :=
  fromOrdinaryCMv_toOrdinaryCMv _

/-- Denominator clearing preserves polynomial graphs, including at zeros of the denominator:
this statement is an identity of polynomials, not a fiberwise division. -/
theorem input_graph_iff (raw : CPolynomial (StoredField.Carrier F)) (P : Polynomial F) :
    (CBivariate.toPoly (fromOrdinaryCMv (input raw))).eval P = 0 ↔
      raw.toPoly.eval₂ StoredField.valueHom
        (algebraMap (Polynomial F) (RatFunc F) P) = 0 := by
  rw [input_eq]
  have h := congrArg (fun f : Polynomial (RatFunc F) =>
    f.eval (algebraMap (Polynomial F) (RatFunc F) P))
    (ClearDenominators.clear_global_identity raw)
  have hs : algebraMap (Polynomial F) (RatFunc F)
      (ClearDenominators.clear raw).scale.toPoly ≠ 0 :=
    RatFunc.algebraMap_ne_zero (ClearDenominators.clear raw).scale_ne_zero
  simp only [ClearDenominators.valueGlobal, FunctionFieldEuclid.value,
    Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C] at h
  rw [Polynomial.eval₂_at_apply] at h
  constructor
  · intro hz
    rw [hz, _root_.map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hs
  · intro hz
    rw [hz, MulZeroClass.mul_zero] at h
    exact (RatFunc.algebraMap_injective F) (h.trans (_root_.map_zero _).symm)

/-- Nonzero raw tails give nonzero global inputs. -/
theorem input_ne_zero {raw : CPolynomial (StoredField.Carrier F)} (hraw : raw ≠ 0) :
    fromOrdinaryCMv (input raw) ≠ 0 := by
  rw [input_eq]
  apply ClearDenominators.clear_global_ne_zero
  intro hz
  apply hraw
  apply FunctionFieldEuclid.value_injective
  simpa only [FunctionFieldEuclid.value, CPolynomial.toPoly_zero, Polynomial.map_zero] using hz

/-- Correctness of the actual finalization call; the callback law is needed only if the
computed ordinary degree reaches the characteristic. -/
theorem finalize_correct (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) :
    OrdinaryNormalizationCorrectness.CorrectOutcome (input raw) (finalize p inverse raw) := by
  exact OrdinaryNormalizationCorrectness.runCertified_correct p inverse (input raw)
    (by simpa only [input_eq] using hinverse)

/-- A nonzero actual tail reaches a graph-free constant branch or a certified separable
ordinary equation. No successful-run witness is an input to this theorem. -/
theorem finalize_nonzero (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) :
    (∃ data, finalize p inverse raw = .constantRegularPart data ∧
      OrdinaryNormalizationCorrectness.ConstantCertificate (input raw) data) ∨
    (∃ data, finalize p inverse raw = .normalized data ∧
      OrdinaryNormalizationCorrectness.NormalizedCertificate (input raw) data) := by
  exact OrdinaryNormalizationCorrectness.runCertified_nonzero p inverse (input raw)
    (by simpa only [input_eq] using hinverse) (input_ne_zero hraw)

/-- The complete denominator/leading-coefficient/resultant guard never vanishes identically
on a nonzero ordinary tail. -/
theorem guard_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) : guard raw (finalize p inverse raw) ≠ 0 := by
  have hs : (ClearDenominators.clear raw).scale ≠ 0 := by
    intro h
    exact (ClearDenominators.clear raw).scale_ne_zero (by rw [h, toPoly_zero])
  rcases finalize_nonzero p inverse raw hraw hinverse with ⟨data, hr, _⟩ | ⟨data, hr, hc⟩
  · simpa only [guard, hr, mul_one] using hs
  · intro hz
    have hp := congrArg CPolynomial.toPoly hz
    simp only [guard, hr, toPoly_mul, toPoly_zero] at hp
    exact (mul_ne_zero (ClearDenominators.clear raw).scale_ne_zero
      ((toPoly_eq_zero_iff data.obstruction).not.mpr hc.obstruction_ne_zero)) hp

/-- A constant final ordinary part means the raw tail has no polynomial graph. -/
theorem constant_no_graph (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (data : OrdinaryNormalization.Data F)
    (hr : finalize p inverse raw = .constantRegularPart data) (P : Polynomial F) :
    raw.toPoly.eval₂ StoredField.valueHom
      (algebraMap (Polynomial F) (RatFunc F) P) ≠ 0 := by
  have hc := finalize_correct p inverse raw hinverse
  rw [hr] at hc
  intro hP
  apply hc.no_graph P
  rw [hc.original_eq]
  exact (input_graph_iff raw P).mpr hP

/-- The separable normalized equation preserves precisely all polynomial graphs of the
actual function-field ordinary tail. -/
theorem normalized_graph_iff (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (data : OrdinaryNormalization.Data F)
    (hr : finalize p inverse raw = .normalized data) (P : Polynomial F) :
    (CBivariate.toPoly data.regular).eval P = 0 ↔
      raw.toPoly.eval₂ StoredField.valueHom
        (algebraMap (Polynomial F) (RatFunc F) P) = 0 := by
  have hc := finalize_correct p inverse raw hinverse
  rw [hr] at hc
  exact (hc.graph_iff P).trans (by rw [hc.original_eq]; exact input_graph_iff raw P)

/-- A center avoiding the complete guard has the regular fiber certificate consumed by
ordinary lifting. -/
theorem normalized_fiber (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (data : OrdinaryNormalization.Data F)
    (hr : finalize p inverse raw = .normalized data) (a : F)
    (ha : (guard raw (finalize p inverse raw)).eval a ≠ 0) :
    RegularCenterObstruction.FiberFacts data.regular a := by
  have hc := finalize_correct p inverse raw hinverse
  rw [hr] at hc
  apply hc.fiberFacts a
  intro hz
  apply ha
  simp only [guard, hr, CPolynomial.eval_mul, hz, MulZeroClass.mul_zero]

/-- Polynomial roots of a usable ordinary output; the constant branch contributes none. -/
def OrdinaryRoot (result : OrdinaryNormalization.Result F) (P : Polynomial F) : Prop :=
  match result with
  | .normalized data => (CBivariate.toPoly data.regular).eval P = 0
  | _ => False

/-- Finalization preserves the root predicate across both successful branches. -/
theorem ordinaryRoot_iff (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree →
      ∀ a, inverse a ^ p = a) (P : Polynomial F) :
    OrdinaryRoot (finalize p inverse raw) P ↔
      raw.toPoly.eval₂ StoredField.valueHom
        (algebraMap (Polynomial F) (RatFunc F) P) = 0 := by
  rcases finalize_nonzero p inverse raw hraw hinverse with ⟨data, hr, _⟩ | ⟨data, hr, _⟩
  · have hn := constant_no_graph p inverse raw hinverse data hr P
    simp only [hr, OrdinaryRoot, false_iff]
    exact hn
  · simpa only [hr, OrdinaryRoot] using
      normalized_graph_iff p inverse raw hinverse data hr P

/-- Concrete ordinary-lifting input from the actual normalized output. -/
def normalizedInput (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (data : OrdinaryNormalization.Data F)
    (hr : finalize p inverse raw = .normalized data) : RegularCenterObstruction.Input F :=
  OrdinaryNormalization.certifiedInput p inverse (input raw) data hr

/-- Direct supplied-input entrypoint, preserving the prepared regular-state branch alongside
ordinary finalization. `none` records a failure of the preceding state producer. -/
def run (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 3 F) :
    Option (OrdinaryTail.Data (StoredField.Carrier F) × OrdinaryNormalization.Result F) :=
  match SuppliedInput.run p Q with
  | .prepared tail => some (tail, finalize p inverse tail.ordinary)
  | _ => none

/-- Actual-run success and a nonzero guard after ordinary
normalization. The only extra degree hypothesis concerns the computed ordinary descent. -/
theorem run_exists (p : ℕ) [Fact p.Prime] [CharP F p] (Q : CMvPolynomial 3 F)
    (hQ : Q ≠ 0)
    (hdegree : (ClearDenominators.primitivePart (SuppliedInput.equation Q)).natDegree < p)
    (hordinary : ∀ tail, SuppliedInput.run p Q = .prepared tail →
      (ClearDenominators.clear tail.ordinary).global.natDegree < p) :
    ∃ tail result, run p id Q = some (tail, result) ∧ tail.ordinary ≠ 0 ∧
      OrdinaryNormalizationCorrectness.CorrectOutcome (input tail.ordinary) result ∧
      guard tail.ordinary result ≠ 0 := by
  obtain ⟨tail, hr, hn, _⟩ := SuppliedInput.run_exists_partition p Q hQ hdegree
  have hlaw : p ≤ (ClearDenominators.clear tail.ordinary).global.natDegree →
      ∀ a : F, id a ^ p = a := by
    intro h
    exact False.elim (Nat.not_le_of_lt (hordinary tail hr) h)
  refine ⟨tail, finalize p id tail.ordinary, ?_, hn,
    finalize_correct p id tail.ordinary hlaw, guard_ne_zero p id tail.ordinary hn hlaw⟩
  simp only [run, hr]

/-- Every polynomial solution of the supplied first-order equation is retained by the final
ordinary equation or by the prepared regular equation with nonzero separant. -/
theorem run_exists_partition (p : ℕ) [Fact p.Prime] [CharP F p] (Q : CMvPolynomial 3 F)
    (hQ : Q ≠ 0)
    (hdegree : (ClearDenominators.primitivePart (SuppliedInput.equation Q)).natDegree < p)
    (hordinary : ∀ tail, SuppliedInput.run p Q = .prepared tail →
      (ClearDenominators.clear tail.ordinary).global.natDegree < p) :
    ∃ tail result, run p id Q = some (tail, result) ∧
      OrdinaryNormalizationCorrectness.CorrectOutcome (input tail.ordinary) result ∧
      guard tail.ordinary result ≠ 0 ∧
      ∀ P : Polynomial F,
        MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P, P.derivative]
          (fromCMvPolynomial Q) = 0 →
        OrdinaryRoot result P ∨
          (RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative) tail.regular = 0 ∧
           RegularPart.evalAt StoredField.valueHom
            (algebraMap (Polynomial F) (RatFunc F) P)
            (algebraMap (Polynomial F) (RatFunc F) P.derivative)
              (CBivariate.partialDerivY tail.regular) ≠ 0) := by
  obtain ⟨tail, hr, hn, hp⟩ := SuppliedInput.run_exists_partition p Q hQ hdegree
  have hlaw : p ≤ (ClearDenominators.clear tail.ordinary).global.natDegree →
      ∀ a : F, id a ^ p = a := by
    intro h
    exact False.elim (Nat.not_le_of_lt (hordinary tail hr) h)
  refine ⟨tail, finalize p id tail.ordinary, ?_,
    finalize_correct p id tail.ordinary hlaw, guard_ne_zero p id tail.ordinary hn hlaw, ?_⟩
  · simp only [run, hr]
  · intro P hP
    rcases hp P hP with ho | hs
    · exact Or.inl ((ordinaryRoot_iff p id tail.ordinary hn hlaw P).mpr ho)
    · exact Or.inr hs

end Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryFinalization
