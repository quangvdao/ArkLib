/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationPointBlockSemantics

/-!
# Exact kernel and dimensions of the full received matrix

Every received point uses the same enumerated support ordering. The actual concatenated matrix
kernel is exactly simultaneous low-contact vanishing at every supplied point. All dimensions
are materialized counters, including empty input. Raw rows are bounded by n*K*supportLength,
not by n alone. The total bound is polynomial in n, support length and the X range, with
exponential constants confined to the gap parameters d,m. Ambient-parameter search and the
nonzero kernel solver are subsequent consumers. This generic budget does not assert polynomial
dependence on growing m; the order-zero, growing-m route needs its separate tighter bound.
-/

namespace ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine

noncomputable section

variable {F : Type*} [CommRing F]

/-- The fixed support shared by all point blocks; this is a proof-side name. -/
def support (D d m A : ℕ) : List (List ℕ) :=
  InterpolationSupportMachine.supportSpec (InterpolationSupportMachine.parameters D d m A)

/-- The actual point output, with a default used only to make the proof-side name total. -/
def pointRows (D d m A : ℕ) (p : F × F) : List (Row F) :=
  (InterpolationPointBlockMachine.assemble D d m A p.1 p.2).1.getD []

/-- All properties used by the outer traversal concern the actual successful block output. -/
theorem pointRows_refines (D d m A : ℕ) (p : F × F) :
    ∃ c, InterpolationPointBlockMachine.assemble D d m A p.1 p.2 =
      (some (pointRows D d m A p), c) ∧
      (∀ r ∈ pointRows D d m A p, r.1.length = (support D d m A).length ∧ r.2 = 0) ∧
      (∀ w : ℕ → F, Matrix.PivotSelectionMachine.Satisfies (pointRows D d m A p) w ↔
        localConstraintAt m p.1 p.2 (InterpolationPointBlockMachine.sourceCombination d
          (support D d m A) w) = 0) ∧
      (pointRows D d m A p).length ≤
        InterpolationPointBlockMachine.columnSize d m * (support D d m A).length ∧
      c ≤ InterpolationPointBlockMachine.assemblyBudget d m A (support D d m A).length := by
  obtain ⟨rs, c, hc, _, hw, hk, hl, hcost⟩ :=
    InterpolationPointBlockMachine.assemble_refines D m A p.1 p.2 (d := d)
  have hr : pointRows D d m A p = rs := by simp [pointRows, hc]
  exact ⟨c, by simpa only [hr] using hc, by simpa only [hr, support] using hw,
    by simpa only [hr, support] using hk, by simpa only [hr, support] using hl, hcost⟩

/-- Concatenation imposes all and only the received-point constraints in common column order. -/
theorem matrix_kernel_iff (D d m A : ℕ) (received : List (F × F)) (w : ℕ → F) :
    Matrix.PivotSelectionMachine.Satisfies (received.flatMap (pointRows D d m A)) w ↔
      ∀ p ∈ received, localConstraintAt m p.1 p.2
        (InterpolationPointBlockMachine.sourceCombination d (support D d m A) w) = 0 := by
  have h : Matrix.PivotSelectionMachine.Satisfies
      (received.flatMap (pointRows D d m A)) w ↔
      ∀ p ∈ received, Matrix.PivotSelectionMachine.Satisfies (pointRows D d m A p) w := by
    constructor
    · intro h p hp r hr
      exact h r (List.mem_flatMap.mpr ⟨p, hp, hr⟩)
    · intro h r hr
      obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hr
      exact h p hp r hm
  rw [h]
  exact forall₂_congr (fun p _ => (pointRows_refines D d m A p).choose_spec.2.2.1 w)

/-- Full observed-work budget; counting the support is charged even for no received points. -/
def budget (d m A L n : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor (d + 1) (2 * m) * (m * A + 1) +
    32 * (L + 1) +
    (InterpolationPointBlockMachine.assemblyBudget d m A L +
      64 * (InterpolationPointBlockMachine.columnSize d m * L + 1) + 64) * (n + 1) + 32

/-- The complete actual matrix, exact counters, solver shape, kernel equivalence and work bound. -/
theorem run_refines (D d m A : ℕ) (received : List (F × F)) :
    ∃ out c, run D d m A received = (some out, c) ∧
      out.columns = (support D d m A).length ∧ out.points = received.length ∧
      out.rowCount = out.rows.length ∧
      out.rows = received.flatMap (pointRows D d m A) ∧
      (∀ r ∈ out.rows, r.1.length = out.columns ∧ r.2 = 0) ∧
      (∀ w : ℕ → F, Matrix.PivotSelectionMachine.Satisfies out.rows w ↔
        ∀ p ∈ received, localConstraintAt m p.1 p.2
          (InterpolationPointBlockMachine.sourceCombination d (support D d m A) w) = 0) ∧
      out.rowCount ≤ InterpolationPointBlockMachine.columnSize d m *
        (support D d m A).length * received.length ∧
      c ≤ budget d m A (support D d m A).length received.length := by
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D d m A
  obtain ⟨tc, ht, hrows, hcost⟩ := traverse_correct D d m A (support D d m A).length
    (InterpolationPointBlockMachine.assemblyBudget d m A (support D d m A).length)
    (InterpolationPointBlockMachine.columnSize d m * (support D d m A).length)
    received (pointRows D d m A) (by
      intro p _
      obtain ⟨c, hc, _, _, hl, hb⟩ := pointRows_refines D d m A p
      exact ⟨c, hc, hl, hb⟩)
  refine ⟨⟨(support D d m A).length, received.length,
    (received.flatMap (pointRows D d m A)).length, received.flatMap (pointRows D d m A)⟩,
    32 + sc + 32 * ((support D d m A).length + 1) + tc,
    ?_, rfl, rfl, rfl, rfl, ?_, matrix_kernel_iff D d m A received, hrows, ?_⟩
  · simp only [run, hs, countCells_correct]
    exact congrArg (fun r => (r.1, 32 + sc + 32 * ((support D d m A).length + 1) + r.2)) ht
  · intro r hr
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hr
    exact (pointRows_refines D d m A p).choose_spec.2.1 r hp
  · unfold budget
    omega

/-- A public row retains its originating point and exact local coefficient interpretation. -/
theorem run_entries (D d m A : ℕ) (received : List (F × F)) (out : Result F) (c : ℕ)
    (h : run D d m A received = (some out, c)) (r : Row F) (hr : r ∈ out.rows) :
    ∃ p ∈ received, ∃ q : LocalColumnRewriteMachine.Term F, q.jets.length = d ∧
      r = ((support D d m A).map (fun v =>
        MvPolynomial.coeff (LocalColumnRewriteMachine.exponent d q)
          (localConstraintAt m p.1 p.2 (InterpolationPointBlockMachine.sourceValue d v))), 0) := by
  obtain ⟨result, cost, he, _, _, _, hrows, _⟩ := run_refines D d m A received
  have ho : result = out := by simpa using congrArg Prod.fst (he.symm.trans h)
  rw [← ho, hrows] at hr
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hr
  obtain ⟨pc, hc, _⟩ := pointRows_refines D d m A p
  exact ⟨p, hp, InterpolationPointBlockMachine.assemble_entries D m A p.1 p.2 _ pc hc r hm⟩

/-- Direct solver-facing equivalence for any successfully returned result. -/
theorem run_kernel_iff (D d m A : ℕ) (received : List (F × F)) (out : Result F) (c : ℕ)
    (h : run D d m A received = (some out, c)) (w : ℕ → F) :
    Matrix.PivotSelectionMachine.Satisfies out.rows w ↔
      ∀ p ∈ received, localConstraintAt m p.1 p.2
        (InterpolationPointBlockMachine.sourceCombination d (support D d m A) w) = 0 := by
  obtain ⟨result, cost, he, _, _, _, hrows, _⟩ := run_refines D d m A received
  have ho : result = out := by simpa using congrArg Prod.fst (he.symm.trans h)
  rw [← ho, hrows]
  exact matrix_kernel_iff D d m A received w

end
end ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine
