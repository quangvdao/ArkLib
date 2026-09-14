/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.EnergyEstimate.Main
public import ArkLib.Data.Graph.GabberGalilConstruction.SpectralMixing
public import Mathlib.Tactic.GCongr
public import Mathlib.Logic.Relation

/-!
# Expansion and deletion in the power-six labelled graph

Boundary counts retain all labelled darts, including coincident endpoints. The numerical
expansion bound is derived from the proved exact squared energy constant `50`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallGraph

open GabberGalil
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Indicator with natural values, suitable for executable dart counts. -/
def natIndicator (S : Finset (Vertex m)) (v : Vertex m) : ℕ := if v ∈ S then 1 else 0

/-- Count labelled length-`t` darts from `S` to `T`, without endpoint deduplication. -/
def dartCount (t : ℕ) (S T : Finset (Vertex m)) : ℕ :=
  ∑ v ∈ S, adjacencyPower t (natIndicator T) v

omit [NeZero m] in
/-- The executed count sums one for each labelled word with the requested endpoints. -/
theorem dartCount_words (t : ℕ) (S T : Finset (Vertex m)) :
    dartCount t S T = ∑ v ∈ S,
      ((labelWords t).map fun word ↦ if walk word v ∈ T then 1 else 0).sum := by
  simp [dartCount, adjacencyPower_apply_words, natIndicator]

/-- The paper boundary in the sixth graph power. -/
def edgeBoundary (S : Finset (Vertex m)) : ℕ := dartCount 6 S (Finset.univ \ S)

omit [NeZero m] in
private theorem power_comm {R : Type*} [Semiring R] (t : ℕ) (f : Vertex m → R) :
    adjacencyPower t (adjacency f) = adjacency (adjacencyPower t f) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [adjacencyPower_succ, ih]

/-- Reversal symmetry holds for the full labelled adjacency power. -/
theorem power_selfAdjoint {R : Type*} [CommSemiring R] (t : ℕ) (f g : Vertex m → R) :
    dot (adjacencyPower t f) g = dot f (adjacencyPower t g) := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih => rw [adjacencyPower_succ, adjacency_selfAdjoint, ih, power_comm]; rfl

private theorem dot_comm {R : Type*} [CommSemiring R] (f g : Vertex m → R) :
    dot f g = dot g f := by simp [dot, mul_comm]

private theorem dartCount_dot (t : ℕ) (S T : Finset (Vertex m)) :
    dartCount t S T = dot (natIndicator S) (adjacencyPower t (natIndicator T)) := by
  simp [dartCount, dot, natIndicator, Finset.sum_ite_mem]

theorem dartCount_symm (t : ℕ) (S T : Finset (Vertex m)) :
    dartCount t S T = dartCount t T S := by
  rw [dartCount_dot, dartCount_dot, ← power_selfAdjoint, dot_comm]

omit [NeZero m] in
private theorem power_cast (t : ℕ) (f : Vertex m → ℕ) (v : Vertex m) :
    ((adjacencyPower t f v : ℕ) : ℝ) = adjacencyPower t (fun w ↦ (f w : ℝ)) v := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih => simp [adjacencyPower_succ, adjacency, ih]

theorem dartCount_cast (t : ℕ) (S T : Finset (Vertex m)) :
    (dartCount t S T : ℝ) = ∑ v ∈ S, adjacencyPower t (indicator T) v := by
  simp only [dartCount, Nat.cast_sum, power_cast]
  have hi : (fun w ↦ ((natIndicator T w : ℕ) : ℝ)) = indicator T := by
    funext w
    unfold natIndicator GabberGalil.indicator
    split <;> norm_num
  rw [hi]

private theorem power_sum {R : Type*} [CommSemiring R] (t : ℕ) (f : Vertex m → R) :
    ∑ v, adjacencyPower t f v = 8 ^ t * ∑ v, f v := by
  induction t with
  | zero => simp
  | succ t ih => rw [adjacencyPower_succ, sum_adjacency, ih, pow_succ]; ring

/-- Six steps have normalized squared contraction at most one quarter. -/
theorem power_six_contraction (f : Vertex m → ℝ) (hf : f ∈ MeanZero) :
    normalizedPoweredEnergy 6 f ≤ (1 / 4 : ℝ) * energy f := by
  have h := normalizedPoweredEnergy_le (exactEnergyEstimate m) hf 6
  exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) (energy_nonneg f))

private theorem power_six_energy (f : Vertex m → ℝ) (hf : f ∈ MeanZero) :
    energy (adjacencyPower 6 f) ≤ 17179869184 * energy f := by
  have h := power_six_contraction f hf
  unfold normalizedPoweredEnergy at h
  norm_num only at h
  linarith

/-- A quadratic-form consequence of the squared-energy contraction. -/
theorem power_six_quadratic (f : Vertex m → ℝ) (hf : f ∈ MeanZero) :
    dot f (adjacencyPower 6 f) ≤ 131072 * energy f := by
  have he := power_six_energy f hf
  have hn : 0 ≤ ∑ v, (adjacencyPower 6 f v - 131072 * f v) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hid : (∑ v, (adjacencyPower 6 f v - 131072 * f v) ^ 2) =
      energy (adjacencyPower 6 f) - 262144 * dot f (adjacencyPower 6 f) +
        17179869184 * energy f := by
    unfold energy dot
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hid] at hn
  linarith

private theorem boundary_identity (S : Finset (Vertex m)) :
    (edgeBoundary S : ℝ) =
      262144 * S.card - dot (indicator S) (adjacencyPower 6 (indicator S)) := by
  have hc : indicator (Finset.univ \ S) = (fun _ ↦ (1 : ℝ)) - indicator S := by
    funext v
    by_cases hv : v ∈ S <;> simp [indicator, hv]
  rw [edgeBoundary, dartCount_cast, hc, adjacencyPower_sub, adjacencyPower_const]
  simp only [dot, GabberGalil.indicator, Pi.sub_apply, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem,
    Finset.univ_inter]
  norm_num only
  ring

private theorem centered_energy (S : Finset (Vertex m)) :
    energy (centeredIndicator S) = (S.card : ℝ) - density S * S.card := by
  have hd : density S * Fintype.card (Vertex m) = S.card := by
    unfold density
    exact div_mul_cancel₀ _ (by exact_mod_cast Fintype.card_pos.ne')
  unfold energy centeredIndicator
  have he : (∑ v, (indicator S v - density S) ^ 2) =
      (∑ v, indicator S v ^ 2) - 2 * density S * (∑ v, indicator S v) +
        Fintype.card (Vertex m) * density S ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [show (Fintype.card (Vertex m) : ℝ) * density S ^ 2 =
      ∑ _v : Vertex m, density S ^ 2 by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he, sum_indicator]
  have hi : (∑ v, indicator S v ^ 2) = (S.card : ℝ) := by simp [indicator]
  rw [hi]
  have hd2 := congrArg (fun x : ℝ ↦ x * density S) hd
  nlinarith [hd2]

private theorem centered_quadratic (S : Finset (Vertex m)) :
    dot (centeredIndicator S) (adjacencyPower 6 (centeredIndicator S)) =
      dot (indicator S) (adjacencyPower 6 (indicator S)) - 262144 * density S * S.card := by
  have hd : density S * Fintype.card (Vertex m) = S.card := by
    unfold density
    exact div_mul_cancel₀ _ (by exact_mod_cast Fintype.card_pos.ne')
  have hpower : adjacencyPower 6 (centeredIndicator S) =
      adjacencyPower 6 (indicator S) - fun _ ↦ 262144 * density S := by
    have hc : centeredIndicator S = indicator S - fun _ ↦ density S := rfl
    rw [hc, adjacencyPower_sub, adjacencyPower_const]
    norm_num only
  rw [hpower]
  unfold dot centeredIndicator
  have he : (∑ v, (indicator S v - density S) *
      (adjacencyPower 6 (indicator S) v - 262144 * density S)) =
      (∑ v, indicator S v * adjacencyPower 6 (indicator S) v) -
      262144 * density S * (∑ v, indicator S v) -
      density S * (∑ v, adjacencyPower 6 (indicator S) v) +
      Fintype.card (Vertex m) * (262144 * density S ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [show (Fintype.card (Vertex m) : ℝ) * (262144 * density S ^ 2) =
      ∑ _v : Vertex m, 262144 * density S ^ 2 by simp]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  change (∑ v, (indicator S v - density S) *
      (adjacencyPower 6 (indicator S) v - 262144 * density S)) = _
  rw [he, power_sum, sum_indicator]
  norm_num only
  have hd2 := congrArg (fun x : ℝ ↦ x * density S) hd
  nlinarith [hd2]

/-- The paper's expansion inequality, counted with all labelled dart multiplicities. -/
theorem edgeBoundary_expansion (S : Finset (Vertex m))
    (hsmall : 2 * S.card ≤ Fintype.card (Vertex m)) :
    8 ^ 6 * S.card ≤ 4 * edgeBoundary S := by
  have hq := power_six_quadratic (centeredIndicator S) (centeredIndicator_mem_meanZero S)
  rw [centered_energy, centered_quadratic] at hq
  have hd : density S ≤ (1 / 2 : ℝ) := by
    unfold density
    apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).mpr
    have hs : (2 : ℝ) * S.card ≤ Fintype.card (Vertex m) := by exact_mod_cast hsmall
    linarith
  have hb := boundary_identity S
  have hs : (0 : ℝ) ≤ S.card := by positivity
  have hh := mul_le_mul_of_nonneg_right hd hs
  have hout : (262144 : ℝ) * S.card ≤ 4 * edgeBoundary S := by linarith
  exact_mod_cast hout

/-- Endpoint adjacency, retaining a labelled dart witness in its count. -/
def Adj (u v : Vertex m) : Prop := 0 < dartCount 6 {u} {v}

theorem adj_symm {u v : Vertex m} (h : Adj u v) : Adj v u := by
  rwa [Adj, dartCount_symm] at h

omit [NeZero m] in
theorem adj_iff_word (u v : Vertex m) :
    Adj u v ↔ ∃ word ∈ labelWords 6, walk word u = v := by
  unfold Adj
  rw [dartCount_words]
  simp only [Finset.sum_singleton, Finset.mem_singleton]
  rw [List.sum_pos_iff_exists_pos_nat]
  constructor
  · rintro ⟨a, ha, hpos⟩
    obtain ⟨word, hw, rfl⟩ := List.mem_map.mp ha
    split at hpos
    · exact ⟨word, hw, by assumption⟩
    · omega
  · rintro ⟨word, hw, he⟩
    exact ⟨1, List.mem_map.mpr ⟨word, hw, by simp only [he, ↓reduceIte]⟩, by omega⟩

omit [NeZero m] in
/-- Incoming or outgoing labelled darts have the expected regular-degree capacity. -/
theorem dartCount_le_left (t : ℕ) (S T : Finset (Vertex m)) :
    dartCount t S T ≤ 8 ^ t * S.card := by
  rw [dartCount_words]
  calc
    (∑ v ∈ S, ((labelWords t).map fun word ↦
        if walk word v ∈ T then 1 else 0).sum) ≤
        ∑ _v ∈ S, ((labelWords t).map fun _ ↦ (1 : ℕ)).sum := by
      apply Finset.sum_le_sum
      intro v _
      exact List.sum_le_sum fun _ _ ↦ by split <;> omega
    _ = 8 ^ t * S.card := by simp [Nat.mul_comm]

/-- All surviving neighbors of a set stay inside that set. -/
def ClosedOutside (Z S : Finset (Vertex m)) : Prop :=
  ∀ u ∈ S, ∀ v, Adj u v → v ∉ Z → v ∈ S

/-- A surviving closed set can send boundary darts only to deleted vertices. -/
theorem edgeBoundary_le_deleted {Z S : Finset (Vertex m)} (hc : ClosedOutside Z S) :
    edgeBoundary S ≤ 8 ^ 6 * Z.card := by
  have hle : dartCount 6 S (Finset.univ \ S) ≤ dartCount 6 S Z := by
    rw [dartCount_words, dartCount_words]
    apply Finset.sum_le_sum
    intro u hu
    apply List.sum_le_sum
    intro word hw
    by_cases hs : walk word u ∈ S
    · simp [hs]
    · have hz : walk word u ∈ Z := by
        by_contra hz
        exact hs (hc u hu _ ((adj_iff_word u _).mpr ⟨word, hw, rfl⟩) hz)
      simp [hz, hs]
  calc
    edgeBoundary S ≤ dartCount 6 S Z := hle
    _ = dartCount 6 Z S := dartCount_symm 6 S Z
    _ ≤ 8 ^ 6 * Z.card := dartCount_le_left 6 Z S

/-- Powered adjacency restricted to surviving vertices. -/
def survivorStep (Z : Finset (Vertex m)) (u v : Vertex m) : Prop :=
  u ∉ Z ∧ v ∉ Z ∧ Adj u v

/-- A component is generated by actual surviving adjacency; it is used only in proofs. -/
noncomputable def component (Z : Finset (Vertex m)) (v : Vertex m) : Finset (Vertex m) := by
  classical
  exact Finset.univ.filter fun w ↦ w ∉ Z ∧ Relation.EqvGen (survivorStep Z) v w

@[simp]
theorem mem_component (Z : Finset (Vertex m)) (v w : Vertex m) :
    w ∈ component Z v ↔ w ∉ Z ∧ Relation.EqvGen (survivorStep Z) v w := by
  classical
  simp [component]

/-- The generated component also has the usual finite directed-reachability description,
since every surviving labelled adjacency has a reversed adjacency. -/
theorem mem_component_iff_reachable (Z : Finset (Vertex m)) (v w : Vertex m) :
    w ∈ component Z v ↔ w ∉ Z ∧ Relation.ReflTransGen (survivorStep Z) v w := by
  let _ : Std.Symm (survivorStep Z) := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, adj_symm h.2.2⟩⟩
  rw [mem_component, Relation.EqvGen.eqvGen_eq_reflTransGen]

theorem component_subset (Z : Finset (Vertex m)) (v : Vertex m) :
    component Z v ⊆ Finset.univ \ Z := by
  intro w hw
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (mem_component Z v w).mp hw |>.1⟩

theorem center_mem_component {Z : Finset (Vertex m)} {v : Vertex m} (hv : v ∉ Z) :
    v ∈ component Z v := (mem_component Z v v).mpr ⟨hv, Relation.EqvGen.refl v⟩

theorem component_closed (Z : Finset (Vertex m)) (v : Vertex m) :
    ClosedOutside Z (component Z v) := by
  intro u hu w hadj hw
  obtain ⟨huZ, hrel⟩ := (mem_component Z v u).mp hu
  exact (mem_component Z v w).mpr
    ⟨hw, Relation.EqvGen.trans _ _ _ hrel (Relation.EqvGen.rel _ _ ⟨huZ, hw, hadj⟩)⟩

theorem component_complement_closed (Z : Finset (Vertex m)) (v : Vertex m) :
    ClosedOutside Z ((Finset.univ \ Z) \ component Z v) := by
  intro u hu w hadj hw
  obtain ⟨hu, hunot⟩ := Finset.mem_sdiff.mp hu
  have huZ := (Finset.mem_sdiff.mp hu).2
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩
  intro hwC
  exact hunot (component_closed Z v w hwC u (adj_symm hadj) huZ)

omit [NeZero m] in
/-- Every vertex in a union of surviving components has no surviving edge leaving the union. -/
theorem biUnion_closed {Z : Finset (Vertex m)} {A : Finset (Finset (Vertex m))}
    (hA : ∀ S ∈ A, ClosedOutside Z S) : ClosedOutside Z (A.biUnion id) := by
  intro u hu v hadj hv
  obtain ⟨S, hS, huS⟩ := Finset.mem_biUnion.mp hu
  exact Finset.mem_biUnion.mpr ⟨S, hS, hA S hS u huS v hadj hv⟩

omit [NeZero m] in
/-- A finite family of sets of size at most half the universe has a medium-sized union. -/
private theorem medium_union (N : ℕ)
    (A : Finset (Finset (Vertex m))) :
    (∀ S ∈ A, 2 * S.card ≤ N) → N ≤ 4 * (A.biUnion id).card →
    ∃ B ⊆ A, N ≤ 4 * (B.biUnion id).card ∧ 2 * (B.biUnion id).card ≤ N := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert C A hCA ih =>
    intro hsmall htotal
    by_cases hC : N ≤ 4 * C.card
    · refine ⟨{C}, by simp, ?_⟩
      simpa using And.intro hC (hsmall C (Finset.mem_insert_self _ _))
    · by_cases hA : N ≤ 4 * (A.biUnion id).card
      · obtain ⟨B, hB, hlo, hhi⟩ := ih
          (fun S hS ↦ hsmall S (Finset.mem_insert_of_mem hS)) hA
        exact ⟨B, hB.trans (Finset.subset_insert _ _), hlo, hhi⟩
      · refine ⟨insert C A, Finset.Subset.refl _, htotal, ?_⟩
        have hbound := Finset.card_union_le C (A.biUnion id)
        rw [Finset.biUnion_insert]
        change 2 * (C ∪ A.biUnion id).card ≤ N
        omega

private noncomputable def componentFamily (Z : Finset (Vertex m)) :
    Finset (Finset (Vertex m)) := (Finset.univ \ Z).image (component Z)

private theorem union_componentFamily (Z : Finset (Vertex m)) :
    (componentFamily Z).biUnion id = Finset.univ \ Z := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
    exact component_subset Z w hvC
  · intro hv
    refine Finset.mem_biUnion.mpr ⟨component Z v, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · exact center_mem_component (Finset.mem_sdiff.mp hv).2

/-- With fewer than `N/16` deletions, one surviving component has more than half the vertices. -/
theorem exists_large_component (Z : Finset (Vertex m))
    (hZ : 16 * Z.card < Fintype.card (Vertex m)) :
    ∃ v ∉ Z, Fintype.card (Vertex m) < 2 * (component Z v).card := by
  classical
  by_contra hno
  have hsmall : ∀ C ∈ componentFamily Z, 2 * C.card ≤ Fintype.card (Vertex m) := by
    intro C hC
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
    have hvZ := (Finset.mem_sdiff.mp hv).2
    have hn : ¬ Fintype.card (Vertex m) < 2 * (component Z v).card :=
      fun h ↦ hno ⟨v, hvZ, h⟩
    omega
  have hcover : Fintype.card (Vertex m) ≤ 4 * ((componentFamily Z).biUnion id).card := by
    rw [union_componentFamily, Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ]
    omega
  obtain ⟨B, hB, hlo, hhi⟩ := medium_union (Fintype.card (Vertex m))
    (componentFamily Z) hsmall hcover
  have hclosed : ClosedOutside Z (B.biUnion id) := by
    apply biUnion_closed
    intro C hC
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hB hC)
    exact component_closed Z v
  have he := edgeBoundary_expansion (B.biUnion id) hhi
  have hc := edgeBoundary_le_deleted hclosed
  norm_num only at he hc
  omega

/-- Deleting `z < N/16` vertices leaves a component with at most `5z` vertices outside it.
The complement counts deleted vertices as well as the other surviving components. -/
theorem exists_component_complement_le (Z : Finset (Vertex m))
    (hZ : 16 * Z.card < Fintype.card (Vertex m)) :
    ∃ v ∉ Z, (Finset.univ \ component Z v).card ≤ 5 * Z.card := by
  classical
  obtain ⟨v, hv, hlarge⟩ := exists_large_component Z hZ
  let U := (Finset.univ \ Z) \ component Z v
  have hUcard : U.card = Fintype.card (Vertex m) - Z.card - (component Z v).card := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset (component_subset Z v),
      Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ]
  have hCbound : (component Z v).card ≤ Fintype.card (Vertex m) - Z.card := by
    have h := Finset.card_le_card (component_subset Z v)
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ] at h
  have hsmall : 2 * U.card ≤ Fintype.card (Vertex m) := by omega
  have he := edgeBoundary_expansion U hsmall
  have hc := edgeBoundary_le_deleted (component_complement_closed Z v)
  change edgeBoundary U ≤ _ at hc
  norm_num only at he hc
  refine ⟨v, hv, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  omega

end ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallGraph
