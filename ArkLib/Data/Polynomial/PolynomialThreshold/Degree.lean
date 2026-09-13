/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PolynomialThreshold.BooleanNetwork
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Degree bounds for the executed polynomial threshold -/

@[expose] public section

namespace CompPoly.CPolynomial.PolynomialThreshold

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The valuation of a polynomial at a proof-only prime factor. -/
noncomputable def valuation (q : Polynomial F) (f : CPolynomial F) : ℕ :=
  multiplicity q f.toPoly

/-- Divisibility bounds the finite prime valuations of nonzero polynomials. -/
theorem valuation_le_of_dvd (q : Polynomial F) (hq : Prime q)
    {a b : CPolynomial F} (hb : b ≠ 0) (h : a.toPoly ∣ b.toPoly) :
    valuation q a ≤ valuation q b :=
  (FiniteMultiplicity.of_prime_left hq
    ((toPoly_eq_zero_iff _).not.mpr hb)).le_multiplicity_of_pow_dvd
    ((pow_multiplicity_dvd q a.toPoly).trans h)

/-- The smaller comparator wire takes the minimum prime valuation. -/
theorem valuation_compare_fst (q : Polynomial F) (hq : Prime q)
    {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    valuation q (compare a b).1 = min (valuation q a) (valuation q b) := by
  apply Nat.le_antisymm
  · exact le_min (valuation_le_of_dvd q hq ha (gcdFactor_dvd_left a b))
      (valuation_le_of_dvd q hq hb (gcdFactor_dvd_right a b))
  · apply (FiniteMultiplicity.of_prime_left hq
      ((toPoly_eq_zero_iff _).not.mpr (compare_ne_zero ha hb).1)).le_multiplicity_of_pow_dvd
    let : DecidableEq F := instDecidableEqOfLawfulBEq
    change q ^ min (valuation q a) (valuation q b) ∣ (gcdFactor a b).toPoly
    rw [gcdFactor_toPoly]
    exact (EuclideanDomain.dvd_gcd
      (pow_dvd_of_le_multiplicity (Nat.min_le_left _ _))
      (pow_dvd_of_le_multiplicity (Nat.min_le_right _ _))).trans
        (normalize_associated _).dvd'

/-- The larger comparator wire takes the maximum prime valuation. -/
theorem valuation_compare_snd (q : Polynomial F) (hq : Prime q)
    {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    valuation q (compare a b).2 = max (valuation q a) (valuation q b) := by
  have heq := congrArg (fun f : CPolynomial F => multiplicity q f.toPoly)
    (compare_product (b := b) ha)
  simp only [toPoly_mul] at heq
  have hout := compare_ne_zero ha hb
  rw [multiplicity_mul hq (FiniteMultiplicity.of_prime_left hq
      (mul_ne_zero ((toPoly_eq_zero_iff _).not.mpr hout.1)
        ((toPoly_eq_zero_iff _).not.mpr hout.2))),
    multiplicity_mul hq (FiniteMultiplicity.of_prime_left hq
      (mul_ne_zero ((toPoly_eq_zero_iff _).not.mpr ha)
        ((toPoly_eq_zero_iff _).not.mpr hb)))] at heq
  change valuation q (compare a b).1 + valuation q (compare a b).2 =
    valuation q a + valuation q b at heq
  rw [valuation_compare_fst q hq ha hb] at heq
  omega

/-- Lift a proof-only predicate to the fixed Boolean wire shape. -/
noncomputable def predicateWires (P : CPolynomial F → Prop) :
    {d : ℕ} → Wires F d → BooleanWires d := by
  classical
  exact fun {d} a => match d, a with
    | _, .leaf f => .leaf (decide (P f))
    | _, .node a b => .node (predicateWires P a) (predicateWires P b)

omit [BEq F] [LawfulBEq F] in
theorem predicateWires_toList (P : CPolynomial F → Prop) {d : ℕ} (a : Wires F d) :
    (predicateWires P a).toList =
      a.toList.map (fun f => @decide (P f) (Classical.propDecidable _)) := by
  induction a with
  | leaf a => rfl
  | node a b ia ib => simp [predicateWires, BooleanWires.toList, Wires.toList, ia, ib]

/-- Predicate semantics commute with a layer when comparators give AND/OR. -/
theorem predicateWires_layer (P : CPolynomial F → Prop)
    (hc : ∀ a b, a ≠ 0 → b ≠ 0 →
      (P (compare a b).1 ↔ P a ∧ P b) ∧ (P (compare a b).2 ↔ P a ∨ P b))
    (up : Bool) {d : ℕ} (a b : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) (hb : b.All (fun f => f ≠ 0)) :
    (predicateWires P (layer up a b).1, predicateWires P (layer up a b).2) =
      booleanLayer up (predicateWires P a) (predicateWires P b) := by
  classical
  induction a with
  | leaf a =>
      cases b with
      | leaf b =>
          have h := hc a b ha hb
          cases up <;> simp [layer, booleanLayer, predicateWires, h.1, h.2]
  | node a b ia ib =>
      cases ‹Wires F _› with
      | node c d =>
          have hac := ia c ha.1 hb.1
          have hbd := ib d ha.2 hb.2
          simp only [layer, predicateWires, booleanLayer]
          exact congrArg₂ Prod.mk
            (congrArg₂ BooleanWires.node (congrArg Prod.fst hac) (congrArg Prod.fst hbd))
            (congrArg₂ BooleanWires.node (congrArg Prod.snd hac) (congrArg Prod.snd hbd))

theorem predicateWires_merge (P : CPolynomial F → Prop)
    (hc : ∀ a b, a ≠ 0 → b ≠ 0 →
      (P (compare a b).1 ↔ P a ∧ P b) ∧ (P (compare a b).2 ↔ P a ∨ P b))
    (up : Bool) {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    predicateWires P (merge up a) = booleanMerge up (predicateWires P a) := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
      cases a with
      | node a b =>
          have hn := layer_all _ (fun _ _ ha hb => compare_ne_zero ha hb) up a b ha.1 ha.2
          have hl := predicateWires_layer P hc up a b ha.1 ha.2
          have hl₁ := congrArg Prod.fst hl
          have hl₂ := congrArg Prod.snd hl
          dsimp only at hl₁ hl₂
          simp only [merge, predicateWires, booleanMerge]
          rw [ih _ hn.1, ih _ hn.2, hl₁, hl₂]

theorem predicateWires_sort (P : CPolynomial F → Prop)
    (hc : ∀ a b, a ≠ 0 → b ≠ 0 →
      (P (compare a b).1 ↔ P a ∧ P b) ∧ (P (compare a b).2 ↔ P a ∨ P b))
    (up : Bool) {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    predicateWires P (sort up a) = booleanSort up (predicateWires P a) := by
  induction a generalizing up with
  | leaf a => rfl
  | node a b ia ib =>
      change predicateWires P (merge up (.node (sort true a) (sort false b))) = _
      rw [predicateWires_merge P hc up (.node (sort true a) (sort false b))
        ⟨sort_ne_zero true a ha.1, sort_ne_zero false b ha.2⟩]
      simp only [predicateWires, booleanSort, ia true ha.1, ib false ha.2]

/-- Every prime valuation threshold is sorted by the same executed network. -/
theorem sort_valuation_threshold (q : Polynomial F) (hq : Prime q) (m : ℕ)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    (sort true a).toList.Pairwise (fun f g => m ≤ valuation q f → m ≤ valuation q g) := by
  classical
  have hc : ∀ a b : CPolynomial F, a ≠ 0 → b ≠ 0 →
      (m ≤ valuation q (compare a b).1 ↔ m ≤ valuation q a ∧ m ≤ valuation q b) ∧
      (m ≤ valuation q (compare a b).2 ↔ m ≤ valuation q a ∨ m ≤ valuation q b) := by
    intro a b ha hb
    rw [valuation_compare_fst q hq ha hb, valuation_compare_snd q hq ha hb]
    exact ⟨le_min_iff, le_max_iff⟩
  have hs := booleanSort_pairwise (predicateWires (fun f => m ≤ valuation q f) a)
  rw [← predicateWires_sort _ hc true a ha, predicateWires_toList, List.pairwise_map] at hs
  simpa only [decide_eq_true_eq] using hs

omit [BEq F] [LawfulBEq F] in
/-- The tree predicate holds at each flattened wire. -/
theorem Wires.all_iff_toList {P : CPolynomial F → Prop} {d : ℕ} (a : Wires F d) :
    a.All P ↔ ∀ f ∈ a.toList, P f := by
  induction a with
  | leaf a => simp [Wires.All, Wires.toList]
  | node a b ia ib => simp [Wires.All, Wires.toList, ia, ib, List.mem_append,
      or_imp, forall_and]

/-- Ascending output wires are ordered by every prime valuation simultaneously. -/
theorem sort_valuation_pairwise (q : Polynomial F) (hq : Prime q)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    (sort true a).toList.Pairwise (fun f g => valuation q f ≤ valuation q g) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hs := sort_valuation_threshold q hq
    (valuation q (sort true a).toList[i]) a ha
  exact (List.pairwise_iff_getElem.mp hs) i j hi hj hij le_rfl

/-- Ascending output wires form a divisibility chain. -/
theorem sort_dvd_pairwise {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    (sort true a).toList.Pairwise (fun f g => f.toPoly ∣ g.toPoly) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hn := (Wires.all_iff_toList _).mp (sort_ne_zero true a ha)
  have hi0 := (toPoly_eq_zero_iff _).not.mpr (hn _ (List.getElem_mem hi))
  have hj0 := (toPoly_eq_zero_iff _).not.mpr (hn _ (List.getElem_mem hj))
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hi0).mpr
  intro q hq
  have hs := (List.pairwise_iff_getElem.mp (sort_valuation_pairwise q hq a ha))
    i j hi hj hij
  rw [(FiniteMultiplicity.of_prime_left hq hi0).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hq hj0).emultiplicity_eq_multiplicity]
  exact_mod_cast hs

/-- Divisibility of nonzero wires makes their degrees nondecreasing. -/
theorem sort_degree_pairwise {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    (sort true a).toList.Pairwise (fun f g => f.natDegree ≤ g.natDegree) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hdvd := (List.pairwise_iff_getElem.mp (sort_dvd_pairwise a ha)) i j hi hj hij
  have hn := (Wires.all_iff_toList _).mp (sort_ne_zero true a ha)
  simpa only [← natDegree_toPoly] using Polynomial.natDegree_le_of_dvd hdvd
    ((toPoly_eq_zero_iff _).not.mpr (hn _ (List.getElem_mem hj)))

omit [BEq F] [LawfulBEq F] in
/-- Tree degree is the ordinary sum of flattened wire degrees. -/
theorem Wires.degree_eq_sum {d : ℕ} (a : Wires F d) :
    a.degree = (a.toList.map CPolynomial.natDegree).sum := by
  induction a with
  | leaf a => simp [Wires.degree, Wires.toList]
  | node a b ia ib => simp [Wires.degree, Wires.toList, ia, ib]

omit [BEq F] [LawfulBEq F] in
/-- In a nondecreasing list, every wire after a selected wire pays its degree. -/
theorem selected_degree_bound (l : List (CPolynomial F))
    (hs : l.Pairwise (fun f g => f.natDegree ≤ g.natDegree))
    (i : ℕ) (hi : i < l.length) :
    (l.length - i) * l[i].natDegree ≤ (l.map CPolynomial.natDegree).sum := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
      obtain ⟨hal, hl⟩ := List.pairwise_cons.mp hs
      cases i with
      | zero =>
          have hsum : l.length * a.natDegree ≤ (l.map CPolynomial.natDegree).sum := by
            clear ih hl hi hs
            induction l with
            | nil => simp
            | cons b l ih =>
                have hb := hal b (by simp)
                have ht := ih (fun f hf => hal f (by simp [hf]))
                simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
                omega
          simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add_left hsum a.natDegree
      | succ i =>
          have ht := ih hl i (by simpa using hi)
          simpa only [List.length_cons, Nat.add_sub_add_right, List.getElem_cons_succ,
            List.map_cons, List.sum_cons] using ht.trans (Nat.le_add_left _ _)

/-- Padding by unit wires leaves the total input degree unchanged. -/
theorem padded_degree (input : Array (CPolynomial F)) (d offset : ℕ) :
    (padded input d offset).degree =
      ∑ i ∈ Finset.range (2 ^ d), (input[offset + i]?.getD 1).natDegree := by
  induction d generalizing offset with
  | zero =>
      simp only [pow_zero, Finset.sum_range_one, Nat.add_zero]
      rfl
  | succ d ih =>
      simp only [padded, Wires.degree, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega

/-- Total degree counts only the original, unpadded array positions. -/
theorem padded_degree_eq_original (input : Array (CPolynomial F)) (d : ℕ)
    (hd : input.size ≤ 2 ^ d) :
    (padded input d 0).degree =
      ∑ i ∈ Finset.range input.size, (input[i]?.getD 1).natDegree := by
  rw [padded_degree]
  simp only [Nat.zero_add]
  have hn : 2 ^ d = input.size + (2 ^ d - input.size) := by omega
  rw [hn, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (2 ^ d - input.size),
      (input[input.size + i]?.getD 1).natDegree) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Array.getElem?_eq_none (by omega)]
    change (1 : CPolynomial F).natDegree = 0
    rw [natDegree_toPoly]
    simp [toPoly_one]
  rw [hz, Nat.add_zero]

/-- The prescribed threshold wire satisfies the paper's degree bound.
Repeated factors are handled through simultaneous prime valuations in the
proof; execution remains the fixed gcd/lcm bitonic network. -/
theorem threshold_degree_le (input : Array (CPolynomial F)) (t : ℕ)
    (hinput : ∀ f ∈ input, f ≠ 0) (ht : 1 ≤ t) (htn : t ≤ input.size)
    {H : CPolynomial F} (hH : threshold input t = some H) :
    t * H.natDegree ≤ ∑ i ∈ Finset.range input.size, (input[i]?.getD 1).natDegree := by
  let d := paddingDepth input.size
  let w := padded input d 0
  have hw : w.All (fun f => f ≠ 0) := padded_ne_zero input hinput d 0
  have hs := sort_degree_pairwise w hw
  have hd : input.size ≤ 2 ^ d := paddingDepth_sufficient input.size
  have hi : 2 ^ d - t < (sort true w).toList.length := by
    rw [Wires.length_toList]
    omega
  have hselect : (sort true w).toList[2 ^ d - t] = H := by
    have hrun : (sort true w).toList[2 ^ d - t]? = some H := by
      simpa only [threshold, ht, htn, and_self, ↓reduceIte] using hH
    rw [List.getElem?_eq_getElem hi] at hrun
    exact Option.some.inj hrun
  have hb := selected_degree_bound (sort true w).toList hs (2 ^ d - t) hi
  rw [hselect, Wires.length_toList] at hb
  have hcount : 2 ^ d - (2 ^ d - t) = t := by omega
  rw [hcount, ← Wires.degree_eq_sum, sort_degree true w hw] at hb
  exact hb.trans_eq (padded_degree_eq_original input d hd)

end CompPoly.CPolynomial.PolynomialThreshold
