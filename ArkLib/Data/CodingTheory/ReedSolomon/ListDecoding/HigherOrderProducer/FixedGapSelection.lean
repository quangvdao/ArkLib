/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectSelection
public import ArkLib.Data.Graph.GabberGalilConstruction.Padding
public import ArkLib.Data.Graph.GabberGalilConstruction.Powering

/-!
# Executable fixed-gap paired selection

This module implements the combinatorial branch of `PairedCandidates`. It enumerates actual
powered Gabber--Galil darts, decodes their endpoints as received-position labels, adds one label
when the requested rank is odd, and rejects dummy endpoints and repeated labels. Parallel darts
and loops remain present until the distinct-label filter, as required by the multigraph algorithm.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open GabberGalil
open ReedSolomon.HiddenDerivative.SquareSystems

/-- Cartesian words over a finite executable alphabet. -/
def tuples {α : Type*} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | t + 1, xs => xs.flatMap fun x ↦ (tuples t xs).map (x :: ·)

@[simp] theorem tuples_zero {α : Type*} (xs : List α) : tuples 0 xs = [[]] := rfl

@[simp] theorem tuples_succ {α : Type*} (t : ℕ) (xs : List α) :
    tuples (t + 1) xs = xs.flatMap fun x ↦ (tuples t xs).map (x :: ·) := rfl

theorem length_of_mem_tuples {α : Type*} {t : ℕ} {xs : List α} {word : List α}
    (hword : word ∈ tuples t xs) : word.length = t := by
  induction t generalizing word with
  | zero => simpa using hword
  | succ t ih =>
      simp only [tuples_succ, List.mem_flatMap, List.mem_map] at hword
      obtain ⟨x, _, tail, htail, rfl⟩ := hword
      simp [ih htail]

/-- A powered labelled dart with both endpoints retained. -/
structure PoweredDart (m : ℕ) where
  start : Vertex m
  word : List Label
  finish : Vertex m
  finish_eq : finish = walk word start
  deriving DecidableEq, Repr

/-- Enumerate all length-`t` darts of the square graph. Walk multiplicity is preserved. -/
def poweredDarts (m t : ℕ) [NeZero m] : List (PoweredDart m) :=
  (List.ofFn fun i : Fin (m * m) ↦ squareVertexEquiv m i).flatMap fun start ↦
    (labelWords t).map fun word ↦
      ⟨start, word, walk word start, rfl⟩

/-- Decode a dart only when both endpoints are genuine received positions. -/
def decodeDart? {n m : ℕ} [NeZero m] (dart : PoweredDart m) :
    Option (Fin n × Fin n) := do
  let i ← unpad? dart.start
  let j ← unpad? dart.finish
  return (i, j)

/-- Powered graph edges on the real received-position labels. Dummy endpoints are discarded. -/
def poweredEdges (n : ℕ) (hn : 0 < n) (t : ℕ) : List (Fin n × Fin n) := by
  letI : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact (poweredDarts (ceilSqrt n) t).filterMap decodeDart?

/-- Any powered walk between two real padded vertices survives dummy-endpoint filtering. -/
theorem mem_poweredEdges_of_walk {n : ℕ} (hn : 0 < n) (t : ℕ) (i j : Fin n)
    (word : List Label) (hword : word ∈ labelWords t)
    (hwalk : walk word (paddedEmbedding n hn i) = paddedEmbedding n hn j) :
    (i, j) ∈ poweredEdges n hn t := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  rw [show poweredEdges n hn t =
      (poweredDarts (ceilSqrt n) t).filterMap decodeDart? by rfl,
    List.mem_filterMap]
  let dart : PoweredDart (ceilSqrt n) :=
    ⟨paddedEmbedding n hn i, word, walk word (paddedEmbedding n hn i), rfl⟩
  refine ⟨dart, ?_, ?_⟩
  · unfold poweredDarts
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨paddedEmbedding n hn i, ?_, word, hword, ?_⟩
    · rw [List.mem_ofFn]
      exact ⟨(squareVertexEquiv (ceilSqrt n)).symm (paddedEmbedding n hn i),
        (squareVertexEquiv (ceilSqrt n)).apply_symm_apply _⟩
    · rfl
  · change (do
      let i' ← unpad? (n := n) (paddedEmbedding n hn i)
      let j' ← unpad? (n := n) (walk word (paddedEmbedding n hn i))
      return (i', j')) = some (i, j)
    rw [hwalk]
    simp [paddedEmbedding]

/-- Flatten endpoints from a tuple of powered darts. Loops intentionally yield duplicate labels
and are rejected by `candidateLabelLists` below. -/
def edgeLabels {n : ℕ} (edges : List (Fin n × Fin n)) : List (Fin n) :=
  edges.flatMap fun edge ↦ [edge.1, edge.2]

@[simp] theorem edgeLabels_nil {n : ℕ} : edgeLabels ([] : List (Fin n × Fin n)) = [] := by
  simp [edgeLabels]

@[simp] theorem edgeLabels_cons {n : ℕ} (edge : Fin n × Fin n)
    (edges : List (Fin n × Fin n)) :
    edgeLabels (edge :: edges) = edge.1 :: edge.2 :: edgeLabels edges := by
  simp [edgeLabels]

@[simp] theorem edgeLabels_length {n : ℕ} (edges : List (Fin n × Fin n)) :
    (edgeLabels edges).length = 2 * edges.length := by
  induction edges with
  | nil => simp [edgeLabels]
  | cons edge edges ih =>
      simp [edgeLabels]
      omega

/-- Candidate label lists before distinctness filtering. For odd `r`, every possible leftover
position is appended. -/
def candidateLabelLists (n : ℕ) (hn : 0 < n) (r t : ℕ) : List (List (Fin n)) :=
  let paired := (tuples (r / 2) (poweredEdges n hn t)).map edgeLabels
  if r % 2 = 0 then paired
  else paired.flatMap fun labels ↦ (List.ofFn id).map fun i ↦ labels ++ [i]

/-- The actual fixed-gap selections. Dummy endpoints have already disappeared, and the filter
requires exactly `r` pairwise-distinct received labels. Equal selections are deduplicated only
after graph-walk multiplicity has served its purpose. -/
def fixedGapSelections (n : ℕ) (hn : 0 < n) (r t : ℕ) : List (Finset (Fin n)) :=
  (((candidateLabelLists n hn r t).filter fun labels ↦
      decide (labels.length = r ∧ labels.Nodup)).map List.toFinset).eraseDups

/-- Every emitted selection has exactly the requested rank. -/
theorem fixedGapSelections_card {n r t : ℕ} {hn : 0 < n}
    {selected : Finset (Fin n)} (hselected : selected ∈ fixedGapSelections n hn r t) :
    selected.card = r := by
  simp only [fixedGapSelections, List.mem_eraseDups, List.mem_map] at hselected
  obtain ⟨labels, hlabels, rfl⟩ := hselected
  have hproperties := of_decide_eq_true (List.mem_filter.mp hlabels).2
  rw [List.toFinset_card_of_nodup hproperties.2]
  exact hproperties.1

/-- Execute the fixed-gap graph selector and build only its selected direct square systems. -/
def fixedGapSystems {P : Type*} [DecidableEq P] {n r : ℕ} (hn : 0 < n) (power : ℕ)
    (hypersurface : P) (agreements : Fin n → P) :
    List (Fin (r + 1) → P) :=
  (fixedGapSelections n hn r power).attach.map fun selected ↦
    squareSystemRows hypersurface agreements
      (rowSubsetEmbedding selected.1 (fixedGapSelections_card selected.2))

/-- Materializing any emitted selection gives a member of the executed system list. -/
theorem squareSystemRows_mem_fixedGapSystems {P : Type*} [DecidableEq P]
    {n r power : ℕ} {hn : 0 < n} (hypersurface : P) (agreements : Fin n → P)
    {selected : Finset (Fin n)} (hselected : selected ∈ fixedGapSelections n hn r power) :
    squareSystemRows hypersurface agreements
        (rowSubsetEmbedding selected (fixedGapSelections_card hselected)) ∈
      fixedGapSystems hn power hypersurface agreements := by
  simp only [fixedGapSystems, List.mem_map]
  refine ⟨⟨selected, hselected⟩, List.mem_attach _ _, ?_⟩
  rfl

/-- Every graph-selected system also occurs in the exhaustive direct family. -/
theorem mem_directSystems_of_mem_fixedGapSystems {P : Type*} [DecidableEq P]
    {n r power : ℕ} {hn : 0 < n} {hypersurface : P} {agreements : Fin n → P}
    {system : Fin (r + 1) → P} (hsystem :
      system ∈ fixedGapSystems hn power hypersurface agreements) :
    system ∈ directSystems r hypersurface agreements := by
  simp only [fixedGapSystems, List.mem_map] at hsystem
  obtain ⟨selected, _, rfl⟩ := hsystem
  exact squareSystemRows_mem_enumerate _ _ _ _

end ReedSolomon.ListDecoding.HigherOrderProducer
