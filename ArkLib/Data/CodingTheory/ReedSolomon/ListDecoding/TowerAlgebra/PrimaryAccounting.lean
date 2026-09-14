/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimaryTower
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PartitionAccounting

/-! # Nonreduced primary partition and dimension accounting -/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- The residual vanishes on every zero-tagged returned component. -/
theorem primary_residual_eq_zero_of_zero_child
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (out : TaggedTower (F := F))
    (hout : out ∈ splitZeroUnitPrimary r residual hr) (htag : out.tag = .zero)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : out.tower.Point phi u v) :
    TowerRepresentation.evalNested residual phi u v = 0 :=
  (splitZeroUnitPrimary_point_sound r residual hr out hout phi u v hpoint).2.mp htag

/-- The residual is nonzero on every unit-tagged returned component. -/
theorem primary_residual_ne_zero_of_unit_child
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (out : TaggedTower (F := F))
    (hout : out ∈ splitZeroUnitPrimary r residual hr) (htag : out.tag = .unit)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : out.tower.Point phi u v) :
    TowerRepresentation.evalNested residual phi u v ≠ 0 := by
  intro hzero
  have hzeroTag :=
    (splitZeroUnitPrimary_point_sound r residual hr out hout phi u v hpoint).2.mpr hzero
  rw [htag] at hzeroTag
  cases hzeroTag

/-- The at-most-two children of one terminal branch are geometrically disjoint. -/
theorem primary_terminalChildren_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (terminal : TerminalGCDBranch (F := F))
    (hterminal : terminal ∈ factorTower (splitStatePrimary r residual hr)) :
    (terminalChildren r (splitStatePrimary r residual hr) terminal).Pairwise fun a b =>
      GeometricallyDisjoint a.tower b.tower := by
  let state := splitStatePrimary r residual hr
  cases hzero : makeTagged? r .zero terminal.modulus terminal.gcdPolynomial.toCPolynomial with
  | none =>
      cases hunit : makeTagged? r .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) <;>
        simp [terminalChildren, state, hzero, hunit]
  | some zeroChild =>
      cases hunit : makeTagged? r .unit terminal.modulus
          (terminalQuotientPolynomial state terminal) with
      | none =>
          simp [terminalChildren, state, hzero, hunit]
      | some unitChild =>
          have hzeroShape := makeTagged?_eq_some_iff.mp hzero
          have hunitShape := makeTagged?_eq_some_iff.mp hunit
          have hzeroTag : zeroChild.tag = .zero := by simp [hzeroShape.2]
          have hunitTag : unitChild.tag = .unit := by simp [hunitShape.2]
          have hzeroMemTerminal : zeroChild ∈ terminalChildren r state terminal := by
            simp [terminalChildren, hzero, hunit]
          have hunitMemTerminal : unitChild ∈ terminalChildren r state terminal := by
            simp [terminalChildren, hzero, hunit]
          have hzeroMem : zeroChild ∈ splitZeroUnitPrimary r residual hr := by
            change zeroChild ∈ (factorTower state).flatMap (terminalChildren r state)
            exact List.mem_flatMap.mpr ⟨terminal, hterminal, hzeroMemTerminal⟩
          have hunitMem : unitChild ∈ splitZeroUnitPrimary r residual hr := by
            change unitChild ∈ (factorTower state).flatMap (terminalChildren r state)
            exact List.mem_flatMap.mpr ⟨terminal, hterminal, hunitMemTerminal⟩
          have hdisjoint : GeometricallyDisjoint zeroChild.tower unitChild.tower := by
            intro K _ phi u v hzeroPoint hunitPoint
            have hz := primary_residual_eq_zero_of_zero_child r residual hr zeroChild hzeroMem
              hzeroTag phi u v hzeroPoint
            have hu := primary_residual_ne_zero_of_unit_child r residual hr unitChild hunitMem
              hunitTag phi u v hunitPoint
            exact hu hz
          simpa [terminalChildren, state, hzero, hunit] using hdisjoint

/-- The actual returned `splitZeroUnitPrimary` list is pairwise geometrically disjoint. -/
theorem splitZeroUnitPrimary_pairwise_geometricallyDisjoint
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) :
    (splitZeroUnitPrimary r residual hr).Pairwise fun a b =>
      GeometricallyDisjoint a.tower b.tower := by
  let state := splitStatePrimary r residual hr
  change ((factorTower state).flatMap (terminalChildren r state)).Pairwise _
  apply pairwise_flatMap_of_pairwise
  · exact factorTower_pairwise_baseGeometricallyDisjoint state
  · intro terminal hterminal
    exact primary_terminalChildren_pairwise_geometricallyDisjoint r residual hr terminal hterminal
  · intro left right hbase a ha b hb
    exact terminalChildren_cross_geometricallyDisjoint r state hbase ha hb

/-- The actual returned child list preserves the parent quotient dimension exactly. -/
theorem splitZeroUnitPrimary_dimension_sum
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) :
    ((splitZeroUnitPrimary r residual hr).map fun out => out.tower.dimension).sum =
      r.dimension := by
  let state := splitStatePrimary r residual hr
  have hdividend : state.dividend.toCPolynomial.monic := by
    simpa [state, splitStatePrimary] using hr.2.2.2.1
  change (((factorTower state).flatMap (terminalChildren r state)).map
    (fun out => out.tower.dimension)).sum = r.dimension
  rw [sum_map_flatMap]
  calc
    _ = ((factorTower state).map fun terminal =>
        terminal.modulus.natDegree * state.dividend.toCPolynomial.natDegree).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro terminal hterminal
      exact terminalChildren_dimension_sum r state hdividend terminal hterminal
    _ = ((factorTower state).map fun terminal => terminal.modulus.natDegree).sum *
        state.dividend.toCPolynomial.natDegree := by
      induction factorTower state with
      | nil => simp
      | cons terminal terminals ih => simp [ih, Nat.add_mul]
    _ = state.modulus.natDegree * state.dividend.toCPolynomial.natDegree := by
      rw [factorTower_natDegree_sum]
    _ = r.dimension := by
      simp [state, splitStatePrimary, TowerRepresentation.dimension]

/-- `splitZeroUnitPrimary` is therefore an exact list-level geometric partition with exact dimension
accounting and the expected zero/unit residual semantics. -/
theorem splitZeroUnitPrimary_partition_accounting
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) :
    ((splitZeroUnitPrimary r residual hr).Pairwise fun a b =>
        GeometricallyDisjoint a.tower b.tower) ∧
      ((splitZeroUnitPrimary r residual hr).map fun out => out.tower.dimension).sum =
        r.dimension ∧
      ∀ (K : Type) [Field K] (phi : F →+* K) (u v : K), r.Point phi u v →
        ∃ out ∈ splitZeroUnitPrimary r residual hr,
          out.tower.Point phi u v ∧
            (out.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  refine ⟨splitZeroUnitPrimary_pairwise_geometricallyDisjoint r residual hr,
    splitZeroUnitPrimary_dimension_sum r residual hr, ?_⟩
  intro K _ phi u v hpoint
  exact splitZeroUnitPrimary_point_complete r residual hr phi u v hpoint

end ReedSolomon.ListDecoding.TowerAlgebra
