/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.FixedGapSelection
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Rank growth along powered graph edges

This file separates the iterative linear-algebra part of fixed-gap selection from the spectral
argument that supplies a suitable edge at each iteration. An edge is suitable when its first
endpoint escapes the current span and its second endpoint escapes the span after adjoining the
first. Starting from the empty selection, such edges grow the rank by exactly two. When the
target rank is odd, one final label outside the paired span grows it by one.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open GabberGalil
open ReedSolomon.HiddenDerivative.SquareSystems

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A two-endpoint rank-growth witness relative to a selected set of labels. -/
def EscapesPair {n : ℕ} (pool : Fin n → V) (selected : Finset (Fin n))
    (edge : Fin n × Fin n) : Prop :=
  pool edge.1 ∉ Submodule.span F (pool '' (selected : Set (Fin n))) ∧
  pool edge.2 ∉ Submodule.span F (pool '' (insert edge.1 selected : Set (Fin n)))

/-- Escaping successively from the old and enlarged spans preserves linear independence. -/
theorem linearIndepOn_insert_pair {n : ℕ} {pool : Fin n → V}
    {selected : Finset (Fin n)} {edge : Fin n × Fin n}
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hescape : EscapesPair (F := F) pool selected edge) :
    LinearIndepOn F pool (insert edge.2 (insert edge.1 selected) : Finset (Fin n)) := by
  simpa only [Finset.coe_insert] using (hindependent.insert hescape.1).insert hescape.2

private theorem first_not_mem_of_escapesPair {n : ℕ} {pool : Fin n → V}
    {selected : Finset (Fin n)} {edge : Fin n × Fin n}
    (hescape : EscapesPair (F := F) pool selected edge) : edge.1 ∉ selected := by
  intro hmem
  apply hescape.1
  apply Submodule.subset_span
  exact ⟨edge.1, by simpa using hmem, rfl⟩

private theorem second_not_mem_insert_of_escapesPair {n : ℕ} {pool : Fin n → V}
    {selected : Finset (Fin n)} {edge : Fin n × Fin n}
    (hescape : EscapesPair (F := F) pool selected edge) : edge.2 ∉ insert edge.1 selected := by
  intro hmem
  apply hescape.2
  apply Submodule.subset_span
  exact ⟨edge.2, by simpa using hmem, rfl⟩

/-- A pair-augmentation oracle up to `pairs` steps yields an actual tuple of graph edges whose
flattened endpoint labels are pairwise distinct and linearly independent. -/
theorem exists_independent_edge_tuple {n pairs q : ℕ} (graphEdges : List (Fin n × Fin n))
    (pool : Fin n → V)
    (haugment : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ graphEdges, EscapesPair (F := F) pool selected edge)
    (hq : q ≤ pairs) :
    ∃ edges ∈ tuples q graphEdges,
      LinearIndepOn F pool ((edgeLabels edges).toFinset : Set (Fin n)) ∧
      (edgeLabels edges).Nodup := by
  induction q with
  | zero =>
      refine ⟨[], by simp, ?_, by simp [edgeLabels]⟩
      simpa only [edgeLabels_nil, List.toFinset_nil, Finset.coe_empty] using
        linearIndepOn_empty F pool
  | succ q ih =>
      have hqle : q ≤ pairs := Nat.le_trans (Nat.le_succ q) hq
      obtain ⟨edges, hedges, hindependent, hnodup⟩ := ih hqle
      let selected := (edgeLabels edges).toFinset
      have hcard : selected.card = 2 * q := by
        dsimp [selected]
        rw [List.toFinset_card_of_nodup hnodup, edgeLabels_length]
        have hlength := length_of_mem_tuples hedges
        omega
      have hlt : selected.card < 2 * pairs := by omega
      obtain ⟨edge, hedge, hescape⟩ := haugment selected hindependent hlt
      have hfirst : edge.1 ∉ selected := first_not_mem_of_escapesPair hescape
      have hsecond : edge.2 ∉ insert edge.1 selected :=
        second_not_mem_insert_of_escapesPair hescape
      have hfirstList : edge.1 ∉ edgeLabels edges := by simpa [selected] using hfirst
      have hsecondList : edge.2 ∉ edgeLabels edges := by
        intro hmem
        apply hsecond
        simp [selected, hmem]
      have hne : edge.1 ≠ edge.2 := by
        intro heq
        apply hsecond
        simp [heq]
      refine ⟨edge :: edges, ?_, ?_, ?_⟩
      · simp only [tuples_succ, List.mem_flatMap, List.mem_map]
        exact ⟨edge, hedge, edges, hedges, rfl⟩
      · simpa only [edgeLabels_cons, List.toFinset_cons, Finset.coe_insert,
          selected, Set.insert_comm] using
          linearIndepOn_insert_pair hindependent hescape
      · rw [edgeLabels_cons, List.nodup_cons, List.nodup_cons]
        exact ⟨by simpa only [List.mem_cons, not_or] using ⟨hne, hfirstList⟩,
          hsecondList, hnodup⟩

/-- The even-rank tuple produced by rank growth is emitted by the executable graph selector. -/
theorem independent_even_selection_mem {n pairs power : ℕ} (hn : 0 < n)
    (pool : Fin n → V)
    (haugment : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ poweredEdges n hn power, EscapesPair (F := F) pool selected edge) :
    ∃ selected ∈ fixedGapSelections n hn (2 * pairs) power,
      LinearIndepOn F pool (selected : Set (Fin n)) := by
  obtain ⟨edges, hedges, hindependent, hnodup⟩ :=
    exists_independent_edge_tuple (F := F) (pairs := pairs)
      (poweredEdges n hn power) pool haugment le_rfl
  refine ⟨(edgeLabels edges).toFinset, ?_, hindependent⟩
  simp only [fixedGapSelections, List.mem_eraseDups, List.mem_map]
  refine ⟨edgeLabels edges, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · simp only [candidateLabelLists]
    simp only [Nat.mul_mod_right, ↓reduceIte, List.mem_map]
    refine ⟨edges, ?_, rfl⟩
    simpa using hedges
  · apply decide_eq_true
    constructor
    · rw [edgeLabels_length, length_of_mem_tuples hedges]
    · exact hnodup

/-- If one more label escapes the paired span, appending it handles an odd target rank. -/
theorem independent_odd_selection_mem {n pairs power : ℕ} (hn : 0 < n)
    (pool : Fin n → V)
    (haugment : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ poweredEdges n hn power, EscapesPair (F := F) pool selected edge)
    (hodd : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card = 2 * pairs →
      ∃ i, pool i ∉ Submodule.span F (pool '' (selected : Set (Fin n)))) :
    ∃ selected ∈ fixedGapSelections n hn (2 * pairs + 1) power,
      LinearIndepOn F pool (selected : Set (Fin n)) := by
  obtain ⟨edges, hedges, hindependent, hnodup⟩ :=
    exists_independent_edge_tuple (F := F) (pairs := pairs)
      (poweredEdges n hn power) pool haugment le_rfl
  let paired := (edgeLabels edges).toFinset
  have hcard : paired.card = 2 * pairs := by
    dsimp [paired]
    rw [List.toFinset_card_of_nodup hnodup, edgeLabels_length,
      length_of_mem_tuples hedges]
  obtain ⟨i, hi⟩ := hodd paired hindependent hcard
  have hinot : i ∉ paired := by
    intro hmem
    apply hi
    apply Submodule.subset_span
    exact ⟨i, by simpa using hmem, rfl⟩
  let labels := edgeLabels edges ++ [i]
  have hilist : i ∉ edgeLabels edges := by simpa [paired] using hinot
  have hlabelsNodup : labels.Nodup := by
    dsimp only [labels]
    rw [List.nodup_append]
    refine ⟨hnodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro hai
    apply hilist
    rwa [← hai]
  have hselectedIndependent :
      LinearIndepOn F pool (labels.toFinset : Set (Fin n)) := by
    simpa [labels, paired] using hindependent.insert hi
  refine ⟨labels.toFinset, ?_, hselectedIndependent⟩
  simp only [fixedGapSelections, List.mem_eraseDups, List.mem_map]
  refine ⟨labels, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · have hmod : (2 * pairs + 1) % 2 = 1 := by omega
    have hdiv : (2 * pairs + 1) / 2 = pairs := by omega
    simp only [candidateLabelLists, hmod, hdiv, one_ne_zero, ↓reduceIte,
      List.mem_flatMap, List.mem_map]
    refine ⟨edgeLabels edges, ?_, i, by simp, ?_⟩
    · exact ⟨edges, by simpa using hedges, rfl⟩
    · exact rfl
  · apply decide_eq_true
    constructor
    · simp [labels, edgeLabels_length, length_of_mem_tuples hedges]
    · exact hlabelsNodup

/-- On an `r`-dimensional space, `r` independent coordinate functionals make the selected
coordinate map injective. This is the linear-algebra bridge from cotangent rank growth to a
nonsingular selected Jacobian. -/
theorem selectedCoordinateMap_injective_of_independent [FiniteDimensional F V]
    {n r : ℕ} (map : V →ₗ[F] (Fin n → F))
    (selected : Finset (Fin n)) (hcard : selected.card = r)
    (hdim : Module.finrank F V = r)
    (hindependent : LinearIndepOn F (coordinateFunctional map)
      (selected : Set (Fin n))) :
    Function.Injective (selectedCoordinateMap map (rowSubsetEmbedding selected hcard)) := by
  let chosen := rowSubsetEmbedding selected hcard
  change Function.Injective (selectedCoordinateMap map chosen)
  have hchosenMem (j : Fin r) : chosen j ∈ selected := by
    change selected.orderEmbOfFin hcard j ∈ selected
    have hjrange : chosen j ∈ Set.range (selected.orderEmbOfFin hcard) := by
      exact ⟨j, rfl⟩
    rwa [Finset.range_orderEmbOfFin] at hjrange
  let intoSelected : Fin r ↪ {i // i ∈ (selected : Set (Fin n))} :=
    ⟨fun j ↦ ⟨chosen j, hchosenMem j⟩, fun i j hij ↦ chosen.injective (Subtype.ext_iff.mp hij)⟩
  have hrows : LinearIndependent F (fun j ↦ coordinateFunctional map (chosen j)) := by
    convert hindependent.comp intoSelected intoSelected.injective using 1
    rfl
  have hspan : Submodule.span F
      (Set.range fun j ↦ coordinateFunctional map (chosen j)) = ⊤ := by
    apply hrows.span_eq_top_of_card_eq_finrank'
    simp [Subspace.dual_finrank_eq, hdim]
  intro x y hxy
  have hzero : selectedCoordinateMap map chosen (x - y) = 0 := by
    calc
      selectedCoordinateMap map chosen (x - y) =
          selectedCoordinateMap map chosen x - selectedCoordinateMap map chosen y := map_sub _ _ _
      _ = 0 := sub_eq_zero.mpr hxy
  have hall (functional : Module.Dual F V) : functional (x - y) = 0 := by
    have hfunctional : functional ∈ Submodule.span F
        (Set.range fun j ↦ coordinateFunctional map (chosen j)) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction (p := fun phi _ ↦ phi (x - y) = 0) ?_ ?_ ?_ ?_
      hfunctional
    · intro phi hphi
      obtain ⟨j, rfl⟩ := hphi
      have hj := congrFun hzero j
      exact hj
    · simp
    · intro phi psi _ _ hphi hpsi
      simp [hphi, hpsi]
    · intro scalar phi _ hphi
      simp [hphi]
  have hxyZero : x - y = 0 := by
    apply (Module.evalEquiv F V).injective
    ext functional
    simpa [Module.evalEquiv_apply, Module.Dual.eval_apply] using hall functional
  exact sub_eq_zero.mp hxyZero

/-- Injective selected coordinates on the hypersurface tangent space, together with a nonzero
normal, give an injective ambient square differential for the same selected labels. -/
theorem normalSelectedMap_injective_of_tangent
    {W : Type*} [AddCommGroup W] [Module F W] {n r : ℕ}
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F)) (selected : Fin r → Fin n)
    (hselected : Function.Injective
      (selectedCoordinateMap (pool.comp normal.ker.subtype) selected)) :
    Function.Injective (normalSelectedMap normal pool selected) := by
  intro x y hxy
  have hnormal : normal (x - y) = 0 := by
    have hfirst := congrArg Prod.fst hxy
    change normal x = normal y at hfirst
    simpa using sub_eq_zero.mpr hfirst
  let tangent : normal.ker := ⟨x - y, hnormal⟩
  have hrows : selectedCoordinateMap (pool.comp normal.ker.subtype) selected tangent = 0 := by
    ext j
    have hsecond := congrFun (congrArg Prod.snd hxy) j
    change pool x (selected j) = pool y (selected j) at hsecond
    simpa [tangent, selectedCoordinateMap_apply] using sub_eq_zero.mpr hsecond
  have htangent : tangent = 0 := hselected (by simpa using hrows)
  exact sub_eq_zero.mp (congrArg Subtype.val htangent)

/-- Under the pair-escape conclusion of the spectral argument, the even-rank executable family
contains a system with injective ambient differential. -/
theorem fixedGapSelections_contains_even_capture
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (haugment : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ poweredEdges n hn power,
        EscapesPair (F := F) (coordinateFunctional (pool.comp normal.ker.subtype))
          selected edge) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ∈ fixedGapSelections n hn (2 * pairs) power ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  have hrange : LinearMap.range normal = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hnormal)
  have hkerDim : Module.finrank F normal.ker = 2 * pairs := by
    have hrankNullity := normal.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrankNullity
    omega
  obtain ⟨selected, hselected, hindependent⟩ :=
    independent_even_selection_mem hn
      (coordinateFunctional (pool.comp normal.ker.subtype)) haugment
  have hcard := fixedGapSelections_card hselected
  refine ⟨selected, hcard, hselected, ?_⟩
  apply normalSelectedMap_injective_of_tangent
  exact selectedCoordinateMap_injective_of_independent
    (pool.comp normal.ker.subtype) selected hcard hkerDim hindependent

/-- The same capture theorem includes the single leftover label required at odd rank. -/
theorem fixedGapSelections_contains_odd_capture
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (haugment : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ poweredEdges n hn power,
        EscapesPair (F := F) (coordinateFunctional (pool.comp normal.ker.subtype))
          selected edge)
    (hodd : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card = 2 * pairs →
      ∃ i, coordinateFunctional (pool.comp normal.ker.subtype) i ∉
        Submodule.span F
          (coordinateFunctional (pool.comp normal.ker.subtype) ''
            (selected : Set (Fin n)))) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs + 1,
      selected ∈ fixedGapSelections n hn (2 * pairs + 1) power ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  have hrange : LinearMap.range normal = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hnormal)
  have hkerDim : Module.finrank F normal.ker = 2 * pairs + 1 := by
    have hrankNullity := normal.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrankNullity
    omega
  obtain ⟨selected, hselected, hindependent⟩ :=
    independent_odd_selection_mem hn
      (coordinateFunctional (pool.comp normal.ker.subtype)) haugment hodd
  have hcard := fixedGapSelections_card hselected
  refine ⟨selected, hcard, hselected, ?_⟩
  apply normalSelectedMap_injective_of_tangent
  exact selectedCoordinateMap_injective_of_independent
    (pool.comp normal.ker.subtype) selected hcard hkerDim hindependent

end ReedSolomon.ListDecoding.HigherOrderProducer
