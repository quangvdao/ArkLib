/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RankGrowth

/-!
# Cotangent separation and powered-edge mixing

The cotangent argument partitions agreeing labels by their images in the quotient by the cuts
already selected. Two labels from different nonzero projective classes escape successively from
the old span. This module states that separation property on concrete label sets and proves that
a large-set mixing guarantee supplies the exact edge witness consumed by RankGrowth.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open GabberGalil
open ReedSolomon.HiddenDerivative.SquareSystems

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A directed edge list connects every two disjoint sets of at least the threshold many labels. -/
def ConnectsLargeSets {n : ℕ} (edges : List (Fin n × Fin n)) (threshold : ℕ) : Prop :=
  ∀ I J : Finset (Fin n), Disjoint I J → threshold ≤ I.card → threshold ≤ J.card →
    ∃ edge ∈ edges, edge.1 ∈ I ∧ edge.2 ∈ J

/-- Every cross pair of two label sets grows rank by two over the selected set. -/
def CotangentSeparated {n : ℕ} (pool : Fin n → V) (selected I J : Finset (Fin n)) : Prop :=
  Disjoint I J ∧
  ∀ i ∈ I, ∀ j ∈ J, EscapesPair (F := F) pool selected (i, j)

/-- Large separated cotangent sets and large-set connectivity produce an actual escaping edge. -/
theorem exists_escaping_edge_of_large_separated {n threshold : ℕ}
    {edges : List (Fin n × Fin n)} {pool : Fin n → V}
    (hmixing : ConnectsLargeSets edges threshold)
    (selected I J : Finset (Fin n))
    (hseparated : CotangentSeparated (F := F) pool selected I J)
    (hI : threshold ≤ I.card) (hJ : threshold ≤ J.card) :
    ∃ edge ∈ edges, EscapesPair (F := F) pool selected edge := by
  obtain ⟨edge, hedge, hfirst, hsecond⟩ := hmixing I J hseparated.1 hI hJ
  exact ⟨edge, hedge, hseparated.2 edge.1 hfirst edge.2 hsecond⟩

/-- A separated-set witness at every intermediate rank discharges the pair-augmentation contract
used by the executable rank-growth theorem. -/
theorem pair_augmentation_of_cotangent_separation {n pairs threshold : ℕ}
    {edges : List (Fin n × Fin n)} (pool : Fin n → V)
    (hmixing : ConnectsLargeSets edges threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F) pool selected I J ∧
        threshold ≤ I.card ∧ threshold ≤ J.card) :
    ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ edge ∈ edges, EscapesPair (F := F) pool selected edge := by
  intro selected hindependent hcard
  obtain ⟨I, J, hseparated, hI, hJ⟩ := hseparate selected hindependent hcard
  exact exists_escaping_edge_of_large_separated hmixing selected I J hseparated hI hJ

/-- Even-rank graph selection captures a nonsingular square differential once cotangent
separation and powered-graph connectivity have been established. -/
theorem fixedGapSelections_contains_even_capture_of_mixing
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power threshold : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (hmixing : ConnectsLargeSets (poweredEdges n hn power) threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F)
          (coordinateFunctional (pool.comp normal.ker.subtype)) selected I J ∧
        threshold ≤ I.card ∧ threshold ≤ J.card) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ∈ fixedGapSelections n hn (2 * pairs) power ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  apply fixedGapSelections_contains_even_capture hn normal pool hdim hnormal
  exact pair_augmentation_of_cotangent_separation
    (coordinateFunctional (pool.comp normal.ker.subtype)) hmixing hseparate

/-- Odd rank uses the same mixed pairs and one final cotangent functional outside their span. -/
theorem fixedGapSelections_contains_odd_capture_of_mixing
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power threshold : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (hmixing : ConnectsLargeSets (poweredEdges n hn power) threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F)
          (coordinateFunctional (pool.comp normal.ker.subtype)) selected I J ∧
        threshold ≤ I.card ∧ threshold ≤ J.card)
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
  apply fixedGapSelections_contains_odd_capture hn normal pool hdim hnormal
  · exact pair_augmentation_of_cotangent_separation
      (coordinateFunctional (pool.comp normal.ker.subtype)) hmixing hseparate
  · exact hodd

end ReedSolomon.ListDecoding.HigherOrderProducer
