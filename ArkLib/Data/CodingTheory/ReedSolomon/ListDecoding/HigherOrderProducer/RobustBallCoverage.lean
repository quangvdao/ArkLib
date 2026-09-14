/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallGraph
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Local spans in the robust-ball graph

The graph and its enumerated sets do not depend on these vector labels. Dummy vertices and
nonagreeing original vertices carry zero, so they cannot contribute a new span direction.

Deleting growth vertices makes local spans constant on each surviving component. The graph
deletion theorem and the fixed gap force at least `δ / 16` growth vertices at every nonspanning
radius. Summing dimension increases gives the budget `r * N`. Taking `δ = ε * N / 4` and using
`N ≤ 4 * n` yields the exact public radius `floor (64 * r / ε) + 1`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallCoverage

open GabberGalil RobustBallEnumeration RobustBallGraph
open scoped BigOperators

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {n m : ℕ} [NeZero m]

/-- Padded labels retain only actual agreeing original indices. -/
def paddedLabel (labels : Fin n → V) (agreeing : Finset (Fin n)) (v : Vertex m) : V :=
  match unpad? v with
  | none => 0
  | some i => if i ∈ agreeing then labels i else 0

@[simp] theorem paddedLabel_dummy (labels : Fin n → V) (agreeing : Finset (Fin n))
    (v : Vertex m) (hv : unpad? (n := n) v = none) :
    paddedLabel labels agreeing v = 0 := by
  simp [paddedLabel, hv]

@[simp] theorem paddedLabel_original (labels : Fin n → V) (agreeing : Finset (Fin n))
    (h : n ≤ m * m) (i : Fin n) :
    paddedLabel labels agreeing (padEmbedding h i) =
      if i ∈ agreeing then labels i else 0 := by
  simp [paddedLabel, unpad_padEmbedding]

noncomputable section

/-- The span of labels in a radius-`j` ball of the power-six graph. -/
def localSpan (labels : Vertex m → V) (j : ℕ) (v : Vertex m) : Submodule F V :=
  Submodule.span F (labels '' (↑(ball j v) : Set (Vertex m)))

omit [NeZero m] in
theorem label_mem_localSpan (labels : Vertex m → V) (j : ℕ) (v : Vertex m) :
    labels v ∈ localSpan (F := F) labels j v :=
  Submodule.subset_span ⟨v, center_mem_ball j v, rfl⟩

omit [NeZero m] in
theorem localSpan_mono (labels : Vertex m → V) (v : Vertex m) :
    Monotone (fun j ↦ localSpan (F := F) labels j v) := by
  intro i j hij
  exact Submodule.span_mono (Set.image_mono (ball_mono v hij))

/-- Moving the center across a powered edge costs one ball radius. -/
theorem ball_subset_adj_succ {u v : Vertex m} (h : Adj u v) (j : ℕ) :
    ball j u ⊆ ball (j + 1) v := by
  have huv : u ∈ poweredNeighbors 6 v := by
    obtain ⟨word, hw, he⟩ := (adj_iff_word v u).mp (adj_symm h)
    exact List.mem_map.mpr ⟨word, hw, he⟩
  induction j with
  | zero =>
    intro x hx
    have hx' : x = u := by simpa [ball] using hx
    subst x
    rw [mem_ball_succ]
    exact Or.inr ⟨v, center_mem_ball 0 v, huv⟩
  | succ j ih =>
    intro x hx
    rcases (mem_ball_succ j u x).mp hx with rfl | ⟨y, hy, hxy⟩
    · rw [mem_ball_succ]
      exact Or.inr ⟨v, center_mem_ball (j + 1) v, huv⟩
    · exact (mem_ball_succ (j + 1) v x).mpr (Or.inr ⟨y, ih hy, hxy⟩)

theorem localSpan_le_adj_succ (labels : Vertex m → V) {u v : Vertex m}
    (h : Adj u v) (j : ℕ) :
    localSpan (F := F) labels j u ≤ localSpan labels (j + 1) v :=
  Submodule.span_mono (Set.image_mono (ball_subset_adj_succ h j))

/-- Vertices at which the next radius adds a span direction. -/
def growthVertices (labels : Vertex m → V) (j : ℕ) : Finset (Vertex m) :=
  Finset.univ.filter fun v ↦ localSpan (F := F) labels j v ≠ localSpan labels (j + 1) v

@[simp] theorem mem_growthVertices (labels : Vertex m → V) (j : ℕ) (v : Vertex m) :
    v ∈ growthVertices (F := F) labels j ↔
      localSpan (F := F) labels j v ≠ localSpan labels (j + 1) v := by
  classical
  simp [growthVertices]

/-- Adjacent vertices whose spans stop growing have the same local span. -/
theorem localSpan_eq_of_adj_not_growth (labels : Vertex m → V) (j : ℕ)
    {u v : Vertex m} (h : Adj u v)
    (hu : u ∉ growthVertices (F := F) labels j)
    (hv : v ∉ growthVertices (F := F) labels j) :
    localSpan (F := F) labels j u = localSpan labels j v := by
  have hu' : localSpan (F := F) labels j u = localSpan labels (j + 1) u := by
    simpa using hu
  have hv' : localSpan (F := F) labels j v = localSpan labels (j + 1) v := by
    simpa using hv
  exact le_antisymm (hv' ▸ localSpan_le_adj_succ labels h j)
    (hu' ▸ localSpan_le_adj_succ labels (adj_symm h) j)

/-- A component remaining after deleting growth vertices has a single local span. -/
theorem localSpan_eq_on_component (labels : Vertex m → V) (j : ℕ)
    {u v : Vertex m} (hv : v ∈ component (growthVertices (F := F) labels j) u) :
    localSpan (F := F) labels j u = localSpan labels j v := by
  have h := ((mem_component _ _ _).mp hv).2
  clear hv
  induction h with
  | rel x y h => exact localSpan_eq_of_adj_not_growth labels j h.2.2 h.1 h.2.1
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- All labels in such a component lie in its common span. -/
theorem component_label_mem_localSpan (labels : Vertex m → V) (j : ℕ)
    {u v : Vertex m} (hv : v ∈ component (growthVertices (F := F) labels j) u) :
    labels v ∈ localSpan (F := F) labels j u := by
  rw [localSpan_eq_on_component labels j hv]
  exact label_mem_localSpan labels j v

variable [FiniteDimensional F V]

/-- Total local dimension, whose increase pays for all growth vertices. -/
def dimensionSum (labels : Vertex m → V) (j : ℕ) : ℕ :=
  ∑ v, Module.finrank F (localSpan (F := F) labels j v)

/-- Every strict span increase contributes at least one dimension. -/
theorem growth_card_add_dimensionSum_le (labels : Vertex m → V) (j : ℕ) :
    (growthVertices (F := F) labels j).card + dimensionSum (F := F) labels j ≤
      dimensionSum (F := F) labels (j + 1) := by
  classical
  have hpoint (v : Vertex m) :
      (if v ∈ growthVertices (F := F) labels j then 1 else 0) +
        Module.finrank F (localSpan (F := F) labels j v) ≤
          Module.finrank F (localSpan (F := F) labels (j + 1) v) := by
    split_ifs with hv
    · have hne := (mem_growthVertices labels j v).mp hv
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (localSpan_mono labels v (Nat.le_succ j)) hne)
      omega
    · simpa using Submodule.finrank_mono (localSpan_mono labels v (Nat.le_succ j))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦ hpoint v)
  simpa [Finset.sum_add_distrib, dimensionSum, growthVertices, Finset.card_filter] using hsum

/-- The sum of growth counts is bounded by the total ambient dimension budget. -/
theorem sum_growth_card_le (labels : Vertex m → V) (R : ℕ) :
    ∑ j ∈ Finset.range R, (growthVertices (F := F) labels j).card ≤
      Module.finrank F V * Fintype.card (Vertex m) := by
  have htel : ∀ R, ∑ j ∈ Finset.range R, (growthVertices (F := F) labels j).card ≤
      dimensionSum (F := F) labels R := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [Finset.sum_range_succ]
      have := growth_card_add_dimensionSum_le (F := F) labels R
      omega
  refine (htel R).trans ?_
  calc
    dimensionSum (F := F) labels R ≤ ∑ _v : Vertex m, Module.finrank F V :=
      Finset.sum_le_sum fun v _ ↦ (localSpan (F := F) labels R v).finrank_le
    _ = _ := by simp [Nat.mul_comm]

/-- Labels outside a subspace, counted as vertices rather than distinct vector values. -/
def outside (labels : Vertex m → V) (W : Submodule F V) : Finset (Vertex m) := by
  classical
  exact Finset.univ.filter fun v ↦ labels v ∉ W

omit [FiniteDimensional F V] in
/-- Failure to span forces many growth vertices, by the proved deletion theorem. -/
theorem gap_le_growth_card (labels : Vertex m → V) (δ : ℚ)
    (hδ : 0 < δ) (hδN : δ ≤ Fintype.card (Vertex m))
    (hgap : ∀ W : Submodule F V, W ≠ ⊤ → δ ≤ (outside labels W).card)
    (j : ℕ) (hproper : ∀ v, localSpan (F := F) labels j v ≠ ⊤) :
    δ ≤ 16 * ((growthVertices (F := F) labels j).card : ℚ) := by
  classical
  by_contra h
  have hz : (16 : ℚ) * (growthVertices (F := F) labels j).card < δ := lt_of_not_ge h
  have hsmall : 16 * (growthVertices (F := F) labels j).card <
      Fintype.card (Vertex m) := by
    exact_mod_cast hz.trans_le hδN
  obtain ⟨v, _, hv⟩ := exists_component_complement_le
    (growthVertices (F := F) labels j) hsmall
  have hsub : outside labels (localSpan (F := F) labels j v) ⊆
      Finset.univ \ component (growthVertices (F := F) labels j) v := by
    intro w hw
    have hw' : labels w ∉ localSpan (F := F) labels j v := by
      simpa [outside] using hw
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, fun hc ↦
      hw' (component_label_mem_localSpan labels j hc)⟩
  have hcount := (Finset.card_le_card hsub).trans hv
  have hcount' : ((outside labels (localSpan (F := F) labels j v)).card : ℚ) ≤
      5 * (growthVertices (F := F) labels j).card := by exact_mod_cast hcount
  have := hgap _ (hproper v)
  have hznonneg : (0 : ℚ) ≤ (growthVertices (F := F) labels j).card := Nat.cast_nonneg _
  linarith

/-- A robust vector labeling spans on some ball once its radius exceeds the dimension budget. -/
theorem exists_full_span_ball (labels : Vertex m → V) (δ : ℚ)
    (hδ : 0 < δ) (hδN : δ ≤ Fintype.card (Vertex m))
    (hgap : ∀ W : Submodule F V, W ≠ ⊤ → δ ≤ (outside labels W).card)
    (R : ℕ) (hbudget : 16 * (Module.finrank F V : ℚ) * Fintype.card (Vertex m) <
      (R : ℚ) * δ) :
    ∃ v, localSpan (F := F) labels R v = ⊤ := by
  classical
  by_contra hfull
  have hproper : ∀ j ≤ R, ∀ v, localSpan (F := F) labels j v ≠ ⊤ := by
    intro j hj v heq
    apply hfull
    refine ⟨v, top_unique ?_⟩
    rw [← heq]
    exact localSpan_mono labels v hj
  have hlower : (R : ℚ) * δ ≤
      16 * ((∑ j ∈ Finset.range R, (growthVertices (F := F) labels j).card : ℕ) : ℚ) := by
    have := Finset.sum_le_sum (s := Finset.range R) fun j hj ↦
      gap_le_growth_card (F := F) labels δ hδ hδN hgap j
        (hproper j (Nat.le_of_lt (Finset.mem_range.mp hj)))
    simpa [Finset.mul_sum] using this
  have hupper : ((∑ j ∈ Finset.range R,
      (growthVertices (F := F) labels j).card : ℕ) : ℚ) ≤
      (Module.finrank F V : ℚ) * Fintype.card (Vertex m) := by
    exact_mod_cast sum_growth_card_le (F := F) labels R
  linarith

/-- Agreeing real indices whose labels escape a given subspace. -/
def agreeingOutside (labels : Fin n → V) (agreeing : Finset (Fin n))
    (W : Submodule F V) : Finset (Fin n) := by
  classical
  exact agreeing.filter fun i ↦ labels i ∉ W

omit [FiniteDimensional F V] in
/-- Padding cannot lose any agreeing label outside a subspace. -/
theorem agreeingOutside_card_le (labels : Fin n → V) (agreeing : Finset (Fin n))
    (h : n ≤ m * m) (W : Submodule F V) :
    (agreeingOutside labels agreeing W).card ≤
      (outside (paddedLabel (m := m) labels agreeing) W).card := by
  classical
  have hsub : (agreeingOutside labels agreeing W).map (padEmbedding h) ⊆
      outside (paddedLabel labels agreeing) W := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨hia, hiW⟩ := Finset.mem_filter.mp hi
    simpa [outside, paddedLabel_original, hia] using hiW
  simpa using Finset.card_le_card hsub

/-- The exact public radius strictly exceeds the rational dimension threshold. -/
theorem robustRadius_mul_gap_gt (r : ℕ) (epsilon : Gap) :
    64 * (r : ℚ) < (robustRadius r epsilon : ℚ) * epsilon.val := by
  have h := Nat.lt_floor_add_one (64 * (r : ℚ) / epsilon.val)
  have h' : 64 * (r : ℚ) / epsilon.val < (robustRadius r epsilon : ℚ) := by
    simpa [robustRadius] using h
  exact (div_lt_iff₀ epsilon.property.1).mp h'

omit [NeZero m] in
/-- A fixed gap on real agreeing labels gives a full-span ball at the public radius. -/
theorem exists_padded_full_span_ball (labels : Fin n → V) (agreeing : Finset (Fin n))
    (hn : 0 < n) (epsilon : Gap)
    (hgap : ∀ W : Submodule F V, W ≠ ⊤ →
      epsilon.val * n ≤ (agreeingOutside labels agreeing W).card) :
    let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
    ∃ v : Vertex (ceilSqrt n),
      localSpan (F := F) (paddedLabel labels agreeing)
        (robustRadius (Module.finrank F V) epsilon) v = ⊤ := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  let N := Fintype.card (Vertex (ceilSqrt n))
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Fintype.card_pos
  have hN : N = paddedSize n := by
    simp [N, paddedSize, Fintype.card_prod, ZMod.card, pow_two]
  have hpad : n ≤ ceilSqrt n * ceilSqrt n := by
    simpa [paddedSize, pow_two] using le_paddedSize n
  have hNfour : (N : ℚ) ≤ 4 * n := by
    exact_mod_cast hN ▸ paddedSize_le_four_mul hn
  have heps := epsilon.property.1
  refine exists_full_span_ball (F := F) (paddedLabel labels agreeing)
    (epsilon.val * N / 4) (by positivity) ?_ ?_ _ ?_
  · have := epsilon.property.2
    nlinarith
  · intro W hW
    have hreal := hgap W hW
    have hcount : ((agreeingOutside labels agreeing W).card : ℚ) ≤
        (outside (paddedLabel (m := ceilSqrt n) labels agreeing) W).card := by
      exact_mod_cast agreeingOutside_card_le labels agreeing hpad W
    have hmul := mul_le_mul_of_nonneg_left hNfour epsilon.property.1.le
    linarith
  · have hrad := robustRadius_mul_gap_gt (Module.finrank F V) epsilon
    have := mul_lt_mul_of_pos_right hrad hNpos
    dsimp [N] at *
    nlinarith

omit [FiniteDimensional F V] in
/-- A padded full-span ball is spanned by its agreeing original indices. -/
theorem originalBall_agreeing_span_eq_top (labels : Fin n → V)
    (agreeing : Finset (Fin n)) (R : ℕ) (v : Vertex m)
    (hfull : localSpan (F := F) (paddedLabel labels agreeing) R v = ⊤) :
    Submodule.span F (labels '' (↑(originalBall n R v ∩ agreeing) : Set (Fin n))) = ⊤ := by
  classical
  apply top_unique
  rw [← hfull]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  cases he : unpad? (n := n) w with
  | none => simp [paddedLabel, he]
  | some i =>
    by_cases hi : i ∈ agreeing
    · simp only [paddedLabel, he, hi, ↓reduceIte]
      apply Submodule.subset_span
      refine ⟨i, Finset.mem_inter.mpr ⟨?_, hi⟩, rfl⟩
      exact (mem_originalBall n R v i).mpr ⟨w, hw, he⟩
    · simp [paddedLabel, he, hi]

omit [NeZero m] in
/-- Extract original indices, retaining cardinality even when distinct indices share labels. -/
theorem exists_spanning_subset_card_finrank (labels : Fin n → V) (T : Finset (Fin n))
    (hspan : Submodule.span F (labels '' (↑T : Set (Fin n))) = ⊤) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ S.card = Module.finrank F V ∧
      Submodule.span F (labels '' (↑S : Set (Fin n))) = ⊤ := by
  classical
  have hex := Submodule.exists_fun_fin_finrank_span_eq F (labels '' (↑T : Set (Fin n)))
  obtain ⟨f, hfmem, hfspan, hfli⟩ := hex
  choose g hgT hgf using hfmem
  have hginj : Function.Injective g := by
    intro a b hab
    apply hfli.injective
    rw [← hgf a, ← hgf b, hab]
  let e : Fin (Module.finrank F (Submodule.span F (labels '' (↑T : Set (Fin n))))) ↪
      Fin n := ⟨g, hginj⟩
  refine ⟨Finset.univ.map e, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    exact hgT a
  · simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact ((LinearEquiv.ofEq _ _ hspan).trans Submodule.topEquiv).finrank_eq
  · apply Eq.trans _ (hfspan.trans hspan)
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨a, (hgf a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨g a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩, hgf a⟩

omit [NeZero m] in
/-- Fixed-gap robust labels have a full-span agreeing selection in the index-only family. -/
theorem exists_robustSelection_span_eq_top (labels : Fin n → V)
    (agreeing : Finset (Fin n)) (hn : 0 < n) (epsilon : Gap)
    (hgap : ∀ W : Submodule F V, W ≠ ⊤ →
      epsilon.val * n ≤ (agreeingOutside labels agreeing W).card) :
    ∃ S : Finset (Fin n),
      S ∈ robustSelections n hn (Module.finrank F V) epsilon ∧ S ⊆ agreeing ∧
        S.card = Module.finrank F V ∧
        Submodule.span F (labels '' (↑S : Set (Fin n))) = ⊤ := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  obtain ⟨v, hv⟩ := exists_padded_full_span_ball labels agreeing hn epsilon hgap
  obtain ⟨S, hS, hcard, hspan⟩ := exists_spanning_subset_card_finrank labels
    (originalBall n (robustRadius (Module.finrank F V) epsilon) v ∩ agreeing)
    (originalBall_agreeing_span_eq_top labels agreeing _ v hv)
  refine ⟨S, ?_, ?_, hcard, hspan⟩
  · exact (mem_robustSelections hn _ epsilon S).mpr
      ⟨v, fun i hi ↦ (Finset.mem_inter.mp (hS hi)).1, hcard⟩
  · exact fun i hi ↦ (Finset.mem_inter.mp (hS hi)).2

omit [NeZero m] in
/-- Version with an explicit dimension parameter for downstream chart adapters. -/
theorem exists_robustSelection_span_eq_top_of_finrank (labels : Fin n → V)
    (agreeing : Finset (Fin n)) (hn : 0 < n) (r : ℕ)
    (hr : Module.finrank F V = r) (epsilon : Gap)
    (hgap : ∀ W : Submodule F V, W ≠ ⊤ →
      epsilon.val * n ≤ (agreeingOutside labels agreeing W).card) :
    ∃ S : Finset (Fin n), S ∈ robustSelections n hn r epsilon ∧ S ⊆ agreeing ∧
      S.card = r ∧ Submodule.span F (labels '' (↑S : Set (Fin n))) = ⊤ := by
  simpa [hr] using exists_robustSelection_span_eq_top labels agreeing hn epsilon hgap

end
end ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallCoverage
