/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.GuardAssembly

/-!
# Complete projection-equation denominator extraction

The nested equation is stored as an outer polynomial in `v`, whose coefficients are inner
polynomials in `u` over `F(X)`. We visit every stored outer and inner coefficient and extract
its canonical denominator in `F[X]`. These factors extend the actual common guard. No
projection-coordinate polynomial is treated as a challenge polynomial. Later normalization
factors remain explicit inputs; this module does not produce them or a specialized normal ring.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard

open CompPoly CPolynomial CPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Flatten canonical challenge denominators in outer-major, inner-minor order.
Stored zero coefficients contribute the harmless denominator one. -/
def coefficientFactors (equation : CBivariate (StoredField.Carrier F)) : List (CPolynomial F) :=
  (List.range equation.val.size).flatMap fun i =>
    (List.range (CPolynomial.coeff equation i).val.size).map fun j =>
      StoredField.denominator ((CPolynomial.coeff equation i).coeff j)

/-- Every coefficient actually stored in the nested equation appears in the factor list. -/
theorem coefficient_mem (equation : CBivariate (StoredField.Carrier F))
    (i j : ℕ) (hi : i < equation.val.size) (hj : j < (CPolynomial.coeff equation i).val.size) :
    StoredField.denominator ((CPolynomial.coeff equation i).coeff j) ∈
      coefficientFactors equation := by
  simp only [coefficientFactors, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨i, hi, j, hj, rfl⟩

/-- Canonical denominator extraction never creates a zero guard factor. -/
theorem coefficientFactors_ne_zero (equation : CBivariate (StoredField.Carrier F)) :
    ∀ f ∈ coefficientFactors equation, f ≠ 0 := by
  intro f hf
  simp only [coefficientFactors, List.mem_flatMap, List.mem_map] at hf
  obtain ⟨i, _, j, _, rfl⟩ := hf
  exact (CPolynomial.toPoly_eq_zero_iff _).not.mp (StoredField.denominator_ne_zero _)

/-- The actual guard assembly extended by all checked equation coefficient denominators. -/
def run (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    CPolynomial F :=
  GuardAssembly.run p inverse raw c (coefficientFactors c.equation ++ later)

/-- The extended actual guard is nonzero under the same producer assumptions as before. -/
theorem run_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree → ∀ a, inverse a ^ p = a)
    {Q : CMvPolynomial 2 (StoredField.Carrier F)}
    (c : Projection.Candidate (StoredField.Carrier F)) (hc : Projection.Sound Q c)
    (later : List (CPolynomial F)) (hlater : ∀ f ∈ later, f ≠ 0) :
    run p inverse raw c later ≠ 0 := by
  apply GuardAssembly.run_ne_zero p inverse raw hraw hinverse c hc
  intro f hf
  rcases List.mem_append.mp hf with he | hl
  · exact coefficientFactors_ne_zero c.equation f he
  · exact hlater f hl

/-- All added denominator degrees are counted, including repeated factors. -/
theorem run_natDegree_le (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    (run p inverse raw c later).natDegree ≤
      ((GuardAssembly.factors p inverse raw c (coefficientFactors c.equation ++ later)).map
        CPolynomial.natDegree).sum :=
  GuardAssembly.run_natDegree_le p inverse raw c _

/-- The extended guard has the exact all-factor nonvanishing semantics over every extension. -/
theorem eval₂_run_ne_zero_iff {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    CPolynomial.eval₂ φ a (run p inverse raw c later) ≠ 0 ↔
      ∀ f ∈ GuardAssembly.factors p inverse raw c (coefficientFactors c.equation ++ later),
        CPolynomial.eval₂ φ a f ≠ 0 :=
  GuardAssembly.eval₂_run_ne_zero_iff φ a p inverse raw c _

/-- Every nested coefficient denominator is nonzero at an accepted extension center.
The universal indices include coefficients beyond the arrays, whose canonical denominator is one. -/
theorem equation_denominators_ne_zero {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F))
    (h : CPolynomial.eval₂ φ a (run p inverse raw c later) ≠ 0) (i j : ℕ) :
    CPolynomial.eval₂ φ a
      (StoredField.denominator ((CPolynomial.coeff c.equation i).coeff j)) ≠ 0 := by
  by_cases hi : i < c.equation.val.size
  · by_cases hj : j < (CPolynomial.coeff c.equation i).val.size
    · apply (eval₂_run_ne_zero_iff φ a p inverse raw c later).mp h
      have hm := coefficient_mem c.equation i j hi hj
      simp only [GuardAssembly.factors, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (Or.inl hm))
    · rw [CPolynomial.coeff_eq_zero_of_size_le _ (Nat.le_of_not_gt hj),
        StoredField.denominator_zero, CPolynomial.eval₂_toPoly,
        CPolynomial.toPoly_one, Polynomial.eval₂_one]
      exact one_ne_zero
  · rw [CPolynomial.coeff_eq_zero_of_size_le _ (Nat.le_of_not_gt hi), CPolynomial.coeff_zero,
      StoredField.denominator_zero, CPolynomial.eval₂_toPoly,
      CPolynomial.toPoly_one, Polynomial.eval₂_one]
    exact one_ne_zero

/-- The new factors preserve every previous discriminant and scalar safety guarantee. -/
theorem previous_factors_ne_zero {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (p : ℕ) (inverse : F → F) (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F))
    (h : CPolynomial.eval₂ φ a (run p inverse raw c later) ≠ 0) :
    CPolynomial.eval₂ φ a (GuardAssembly.run p inverse raw c later) ≠ 0 := by
  apply (GuardAssembly.eval₂_run_ne_zero_iff φ a p inverse raw c later).mpr
  intro f hf
  apply (eval₂_run_ne_zero_iff φ a p inverse raw c later).mp h
  simp only [GuardAssembly.factors, List.mem_cons, List.mem_append] at hf ⊢
  rcases hf with ho | hp | hl
  · exact Or.inl ho
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inr hl))

/-- The actual checked projection search discharges the projection soundness input. -/
theorem run_ne_zero_of_search (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F)) (hraw : raw ≠ 0)
    (hinverse : p ≤ (ClearDenominators.clear raw).global.natDegree → ∀ a, inverse a ^ p = a)
    (B : ℕ) (Q : CMvPolynomial 2 (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (hr : Projection.search B Q = some c)
    (later : List (CPolynomial F)) (hlater : ∀ f ∈ later, f ≠ 0) :
    run p inverse raw c later ≠ 0 :=
  run_ne_zero p inverse raw hraw hinverse c (Projection.search_sound B Q c hr).1 later hlater

end Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard
