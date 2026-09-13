/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RankGrowth
public import ArkLib.Data.Graph.GabberGalilConstruction.SpectralMixing

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

/-- The powered padded graph connects all real label sets above a threshold once the normalized
energy contraction is smaller than the squared threshold density. -/
theorem connectsLargeSets_poweredEdges {n power threshold : ℕ} [NeZero (ceilSqrt n)]
    (hn : 0 < n)
    (hGG : ExactEnergyEstimate (ceilSqrt n)) (hthreshold : 0 < threshold)
    (hnumeric : ((25 : ℝ) / 32) ^ power * (paddedSize n : ℝ) ^ 2 <
      (threshold : ℝ) ^ 2) :
    ConnectsLargeSets (poweredEdges n hn power) threshold := by
  intro I J _hdisjoint hI hJ
  let embed := paddedEmbedding n hn
  let paddedI := I.map embed
  let paddedJ := J.map embed
  have hIcard : paddedI.card = I.card := by simp [paddedI]
  have hJcard : paddedJ.card = J.card := by simp [paddedJ]
  have hJnonempty : paddedJ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : paddedJ.card = 0 := by rw [hempty]; simp
    omega
  have hvertexCard : Fintype.card (Vertex (ceilSqrt n)) = paddedSize n := by
    simp [paddedSize, pow_two]
  have hIreal : (threshold : ℝ) ≤ I.card := by exact_mod_cast hI
  have hJreal : (threshold : ℝ) ≤ J.card := by exact_mod_cast hJ
  have hproduct : (threshold : ℝ) ^ 2 ≤ (I.card : ℝ) * J.card := by
    nlinarith [show (0 : ℝ) ≤ I.card by positivity,
      show (0 : ℝ) ≤ J.card by positivity]
  have hpaddedNumeric :
      ((25 : ℝ) / 32) ^ power *
          (Fintype.card (Vertex (ceilSqrt n)) : ℝ) ^ 2 <
        (paddedI.card : ℝ) * paddedJ.card := by
    rw [hvertexCard, hIcard, hJcard]
    exact hnumeric.trans_le hproduct
  obtain ⟨start, hstart, word, hword, hfinish⟩ :=
    hasPoweredEdge_of_normalized_product hGG paddedI paddedJ hJnonempty hpaddedNumeric
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hstart
  obtain ⟨j, hj, hwalk⟩ := Finset.mem_map.mp hfinish
  refine ⟨(i, j), mem_poweredEdges_of_walk hn power i j word hword ?_, hi, hj⟩
  exact hwalk.symm

/-- A separated-set witness at every intermediate rank discharges the pair-augmentation contract
used by the executable rank-growth theorem. -/
theorem pair_augmentation_of_cotangent_separation {n pairs threshold : ℕ}
    {edges : List (Fin n × Fin n)} (pool : Fin n → V) (allowed : Finset (Fin n))
    (hmixing : ConnectsLargeSets edges threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      Even selected.card →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F) pool selected I J ∧
        I ⊆ allowed ∧ J ⊆ allowed ∧ threshold ≤ I.card ∧ threshold ≤ J.card) :
    ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card < 2 * pairs →
      Even selected.card →
      ∃ edge ∈ edges, EscapesPair (F := F) pool selected edge ∧
        edge.1 ∈ allowed ∧ edge.2 ∈ allowed := by
  intro selected hindependent hcard heven
  obtain ⟨I, J, hseparated, hIsub, hJsub, hI, hJ⟩ :=
    hseparate selected hindependent hcard heven
  obtain ⟨edge, hedge, hfirst, hsecond⟩ := hmixing I J hseparated.1 hI hJ
  exact ⟨edge, hedge, hseparated.2 edge.1 hfirst edge.2 hsecond,
    hIsub hfirst, hJsub hsecond⟩

/-- Even-rank graph selection captures a nonsingular square differential once cotangent
separation and powered-graph connectivity have been established. -/
theorem fixedGapSelections_contains_even_capture_of_mixing
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power threshold : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (allowed : Finset (Fin n))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (hmixing : ConnectsLargeSets (poweredEdges n hn power) threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      Even selected.card →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F)
          (coordinateFunctional (pool.comp normal.ker.subtype)) selected I J ∧
        I ⊆ allowed ∧ J ⊆ allowed ∧ threshold ≤ I.card ∧ threshold ≤ J.card) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ∈ fixedGapSelections n hn (2 * pairs) power ∧ selected ⊆ allowed ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  apply fixedGapSelections_contains_even_capture hn normal pool allowed hdim hnormal
  exact pair_augmentation_of_cotangent_separation
    (coordinateFunctional (pool.comp normal.ker.subtype)) allowed hmixing hseparate

/-- Odd rank uses the same mixed pairs and one final cotangent functional outside their span. -/
theorem fixedGapSelections_contains_odd_capture_of_mixing
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n pairs power threshold : ℕ} (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (allowed : Finset (Fin n))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (hmixing : ConnectsLargeSets (poweredEdges n hn power) threshold)
    (hseparate : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card < 2 * pairs →
      Even selected.card →
      ∃ I J : Finset (Fin n),
        CotangentSeparated (F := F)
          (coordinateFunctional (pool.comp normal.ker.subtype)) selected I J ∧
        I ⊆ allowed ∧ J ⊆ allowed ∧ threshold ≤ I.card ∧ threshold ≤ J.card)
    (hodd : ∀ selected : Finset (Fin n),
      LinearIndepOn F (coordinateFunctional (pool.comp normal.ker.subtype))
        (selected : Set (Fin n)) → selected.card = 2 * pairs →
      ∃ i ∈ allowed, coordinateFunctional (pool.comp normal.ker.subtype) i ∉
        Submodule.span F
          (coordinateFunctional (pool.comp normal.ker.subtype) ''
            (selected : Set (Fin n)))) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs + 1,
      selected ∈ fixedGapSelections n hn (2 * pairs + 1) power ∧ selected ⊆ allowed ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  apply fixedGapSelections_contains_odd_capture hn normal pool allowed hdim hnormal
  · exact pair_augmentation_of_cotangent_separation
      (coordinateFunctional (pool.comp normal.ker.subtype)) allowed hmixing hseparate
  · exact hodd

end ReedSolomon.ListDecoding.HigherOrderProducer
