/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryDegreeBounds
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.ProjectionBounds

/-!
# Challenge-variable guard assembly

The projection discriminant lies in `F(X)[u]`, so it is not multiplied into an `F[X]` guard.
Instead we collect its canonical coefficient denominator product and the numerator and
denominator of the checked projection scalar. Later challenge-polynomial factors are explicit
list inputs. Producing the final normalization factors and flattening the projection equation's
coefficient denominators are separate obligations. Coefficientwise specialization preserving
the discriminant's monicity and nonzero polynomial property is not proved here.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.GuardAssembly

open CompPoly CPolynomial CPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Challenge factors extracted from a checked function-field projection. -/
def projectionFactors (c : Projection.Candidate (StoredField.Carrier F)) : List (CPolynomial F) :=
  [(ClearDenominators.clear c.discriminant).scale,
    StoredField.numerator c.scale, StoredField.denominator c.scale]

/-- The actual ordinary guard, actual projection challenge factors, and explicit later factors. -/
def factors (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    List (CPolynomial F) :=
  OrdinaryFinalization.guard raw (OrdinaryFinalization.finalize p inverse raw) ::
    (projectionFactors c ++ later)

/-- Executable common guard in the challenge variable. -/
def run (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    CPolynomial F := (factors p inverse raw c later).prod

private theorem product_ne_zero (ps : List (CPolynomial F)) (hp : ∀ f ∈ ps, f ≠ 0) :
    ps.prod ≠ 0 := by
  induction ps with
  | nil =>
    intro hz
    have h := congrArg CPolynomial.toPoly hz
    exact one_ne_zero (by
      simpa only [List.prod_nil, CPolynomial.toPoly_one, CPolynomial.toPoly_zero] using h)
  | cons f ps ih =>
    apply (CPolynomial.toPoly_eq_zero_iff _).not.mp
    rw [List.prod_cons, CPolynomial.toPoly_mul]
    exact mul_ne_zero ((CPolynomial.toPoly_eq_zero_iff f).not.mpr (hp f (by simp)))
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr (ih (fun g hg => hp g (by simp [hg]))))

/-- The numerator of a nonzero stored rational function is nonzero. -/
theorem numerator_ne_zero {a : StoredField.Carrier F} (ha : a ≠ 0) :
    StoredField.numerator a ≠ 0 := by
  intro hn
  apply ha
  apply StoredField.value_injective
  rw [StoredField.value_eq_num_div_den, hn, CPolynomial.toPoly_zero, _root_.map_zero, zero_div,
    StoredField.value_zero]

/-- All projection challenge factors are nonzero for an actual checked output. -/
theorem projectionFactors_ne_zero {Q : CMvPolynomial 2 (StoredField.Carrier F)}
    {c : Projection.Candidate (StoredField.Carrier F)} (hc : Projection.Sound Q c) :
    ∀ f ∈ projectionFactors c, f ≠ 0 := by
  intro f hf
  simp only [projectionFactors, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact (CPolynomial.toPoly_eq_zero_iff _).not.mp
      (ClearDenominators.clear c.discriminant).scale_ne_zero
  · exact numerator_ne_zero hc.scale_ne_zero
  · exact (CPolynomial.toPoly_eq_zero_iff _).not.mp (StoredField.denominator_ne_zero _)

/-- Actual producer guards and explicitly nonzero later factors give a nonzero common guard. -/
theorem run_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree → ∀ a, inverse a ^ p = a)
    {Q : CMvPolynomial 2 (StoredField.Carrier F)}
    (c : Projection.Candidate (StoredField.Carrier F)) (hc : Projection.Sound Q c)
    (later : List (CPolynomial F)) (hlater : ∀ f ∈ later, f ≠ 0) :
    run p inverse raw c later ≠ 0 := by
  apply product_ne_zero
  intro f hf
  simp only [factors, List.mem_cons, List.mem_append] at hf
  rcases hf with rfl | hp | hl
  · exact OrdinaryFinalization.guard_ne_zero p inverse raw hraw hinverse
  · exact projectionFactors_ne_zero hc f hp
  · exact hlater f hl

/-- Product degree is bounded by the sum of the actual factor degrees, with repetitions kept. -/
theorem product_natDegree_le (ps : List (CPolynomial F)) :
    ps.prod.natDegree ≤ (ps.map CPolynomial.natDegree).sum := by
  induction ps with
  | nil => simp [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one]
  | cons f ps ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    have hm : (f * ps.prod).natDegree ≤ f.natDegree + ps.prod.natDegree := by
      simp only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul]
      exact Polynomial.natDegree_mul_le
    exact hm.trans (Nat.add_le_add_left ih _)

/-- The assembled guard has the explicit factor-degree-sum bound. -/
theorem run_natDegree_le (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    (run p inverse raw c later).natDegree ≤
      ((factors p inverse raw c later).map CPolynomial.natDegree).sum :=
  product_natDegree_le _

/-- Uniform specialization of an actual product into any extension field is nonzero exactly
when every listed factor is nonzero there. No base-field-only center restriction is imposed. -/
theorem eval₂_product_ne_zero_iff {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (ps : List (CPolynomial F)) :
    CPolynomial.eval₂ φ a ps.prod ≠ 0 ↔ ∀ f ∈ ps, CPolynomial.eval₂ φ a f ≠ 0 := by
  induction ps with
  | nil => simp [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_one]
  | cons f ps ih =>
    simp only [List.prod_cons, CPolynomial.eval₂_toPoly, CPolynomial.toPoly_mul,
      Polynomial.eval₂_mul, ne_eq, mul_eq_zero, not_or] at ih ⊢
    simpa only [List.mem_cons, forall_eq_or_imp] using and_congr_right (fun _ => ih)

/-- Exact simultaneous nonvanishing contract for the assembled challenge guard. -/
theorem eval₂_run_ne_zero_iff {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    CPolynomial.eval₂ φ a (run p inverse raw c later) ≠ 0 ↔
      ∀ f ∈ factors p inverse raw c later, CPolynomial.eval₂ φ a f ≠ 0 :=
  eval₂_product_ne_zero_iff φ a _

/-- Avoiding the computed clearing scale makes every stored discriminant coefficient defined. -/
theorem coefficient_denominator_ne_zero {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (raw : CPolynomial (StoredField.Carrier F))
    (hscale : CPolynomial.eval₂ φ a (ClearDenominators.clear raw).scale ≠ 0)
    (i : ℕ) (hi : i < raw.val.size) :
    CPolynomial.eval₂ φ a (StoredField.denominator (raw.coeff i)) ≠ 0 := by
  intro hz
  apply hscale
  change CPolynomial.eval₂ φ a (ClearDenominators.denominatorProduct raw) = 0
  rw [← ClearDenominators.denominator_mul_complementaryProduct raw hi]
  simp only [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_mul, Polynomial.eval₂_mul] at hz ⊢
  rw [hz, MulZeroClass.zero_mul]

/-- The assembled guard simultaneously validates the ordinary center, every discriminant
coefficient denominator, and both scalar numerator and denominator at the same extension center. -/
theorem run_specialization {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F))
    (h : CPolynomial.eval₂ φ a (run p inverse raw c later) ≠ 0) :
    CPolynomial.eval₂ φ a
      (OrdinaryFinalization.guard raw (OrdinaryFinalization.finalize p inverse raw)) ≠ 0 ∧
    (∀ i, i < c.discriminant.val.size →
      CPolynomial.eval₂ φ a (StoredField.denominator (c.discriminant.coeff i)) ≠ 0) ∧
    CPolynomial.eval₂ φ a (StoredField.numerator c.scale) ≠ 0 ∧
    CPolynomial.eval₂ φ a (StoredField.denominator c.scale) ≠ 0 := by
  have hall := (eval₂_run_ne_zero_iff φ a p inverse raw c later).mp h
  refine ⟨hall _ (by simp [factors]), ?_,
    hall _ (by simp [factors, projectionFactors]),
    hall _ (by simp [factors, projectionFactors])⟩
  exact coefficient_denominator_ne_zero φ a c.discriminant
    (hall _ (by simp [factors, projectionFactors]))

/-- Direct consumer of an actual projection search result. -/
theorem run_ne_zero_of_search (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree → ∀ a, inverse a ^ p = a)
    (B : ℕ) (Q : CMvPolynomial 2 (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (hr : Projection.search B Q = some c)
    (later : List (CPolynomial F)) (hlater : ∀ f ∈ later, f ≠ 0) :
    run p inverse raw c later ≠ 0 :=
  run_ne_zero p inverse raw hraw hinverse c (Projection.search_sound B Q c hr).1 later hlater

end Polynomial.FunctionFieldAlgorithms.CommonCenter.GuardAssembly
