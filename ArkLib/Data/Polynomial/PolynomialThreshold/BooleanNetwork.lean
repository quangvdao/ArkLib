/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PolynomialThreshold.Correctness

/-! # Boolean semantics of the fixed polynomial network

The Boolean network below has exactly the polynomial network's recursion and
comparator schedule. Evaluating vanishing at an arbitrary extension-field point
commutes with its execution: gcd is conjunction and lcm is disjunction.
-/

@[expose] public section

namespace CompPoly.CPolynomial.PolynomialThreshold

/-- Boolean wires with the same balanced shape as polynomial wires. -/
inductive BooleanWires : ℕ → Type where
  | leaf : Bool → BooleanWires 0
  | node {d : ℕ} : BooleanWires d → BooleanWires d → BooleanWires (d + 1)
  deriving DecidableEq

/-- The Boolean AND/OR comparator layer in the requested direction. -/
def booleanLayer (up : Bool) : {d : ℕ} → BooleanWires d → BooleanWires d →
    BooleanWires d × BooleanWires d
  | _, .leaf a, .leaf b =>
      if up then (.leaf (a && b), .leaf (a || b))
      else (.leaf (a || b), .leaf (a && b))
  | _, .node a b, .node c d =>
      let ac := booleanLayer up a c
      let bd := booleanLayer up b d
      (.node ac.1 bd.1, .node ac.2 bd.2)

/-- Boolean execution of the recursive bitonic merge. -/
def booleanMerge (up : Bool) : {d : ℕ} → BooleanWires d → BooleanWires d
  | _, .leaf a => .leaf a
  | _, .node a b =>
      let c := booleanLayer up a b
      .node (booleanMerge up c.1) (booleanMerge up c.2)

/-- Boolean execution of the fixed bitonic sorting schedule. -/
def booleanSort (up : Bool) : {d : ℕ} → BooleanWires d → BooleanWires d
  | _, .leaf a => .leaf a
  | _, .node a b => booleanMerge up (.node (booleanSort true a) (booleanSort false b))

/-- Flatten Boolean wires in the same order as the polynomial network. -/
def BooleanWires.toList : {d : ℕ} → BooleanWires d → List Bool
  | _, .leaf a => [a]
  | _, .node a b => a.toList ++ b.toList

/-- Count true wires without identifying positions with equal values. -/
def BooleanWires.count : {d : ℕ} → BooleanWires d → ℕ
  | _, .leaf a => if a then 1 else 0
  | _, .node a b => a.count + b.count

/-- Boolean flattening retains exactly the depth-determined number of wires. -/
theorem BooleanWires.length_toList {d : ℕ} (a : BooleanWires d) :
    a.toList.length = 2 ^ d := by
  induction a with
  | leaf a => rfl
  | node a b ia ib => simp [toList, ia, ib, pow_succ, Nat.mul_two]

/-- Recursive true counts agree with list counts. -/
theorem BooleanWires.count_eq_count_toList {d : ℕ} (a : BooleanWires d) :
    a.count = a.toList.count true := by
  induction a with
  | leaf a => cases a <;> simp [count, toList]
  | node a b ia ib => simp [count, toList, ia, ib]

/-- Boolean comparators preserve the number of true positions. -/
theorem booleanLayer_count (up : Bool) {d : ℕ} (a b : BooleanWires d) :
    (booleanLayer up a b).1.count + (booleanLayer up a b).2.count = a.count + b.count := by
  induction a with
  | leaf a =>
      cases b with
      | leaf b => cases up <;> cases a <;> cases b <;> rfl
  | node a b ia ib =>
      cases ‹BooleanWires _› with
      | node c d =>
          have hac := ia c
          have hbd := ib d
          simp only [booleanLayer, BooleanWires.count]
          omega

/-- Boolean merge preserves the number of true positions. -/
theorem booleanMerge_count (up : Bool) {d : ℕ} (a : BooleanWires d) :
    (booleanMerge up a).count = a.count := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
      cases a with
      | node a b =>
          simp only [booleanMerge, BooleanWires.count, ih]
          exact booleanLayer_count up a b

/-- The exact Boolean sorting schedule preserves the number of true positions. -/
theorem booleanSort_count (up : Bool) {d : ℕ} (a : BooleanWires d) :
    (booleanSort up a).count = a.count := by
  induction a generalizing up with
  | leaf a => rfl
  | node a b ia ib =>
      simp only [booleanSort, booleanMerge_count, BooleanWires.count, ia, ib]

/-- An ascending Boolean list consists of its false wires followed by its true
wires; the latter block has exactly the positional true count. -/
theorem booleanList_eq_replicate_of_pairwise (l : List Bool)
    (h : l.Pairwise (fun a b => a = true → b = true)) :
    l = List.replicate (l.length - l.count true) false ++
      List.replicate (l.count true) true := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      cases a with
      | false =>
          have hc : l.count true ≤ l.length := List.count_le_length
          have hn : l.length + 1 - l.count true = (l.length - l.count true) + 1 := by
            omega
          simp only [List.length_cons, List.count_cons]
          change false :: l = List.replicate (l.length + 1 - l.count true) false ++
            List.replicate (l.count true) true
          rw [hn, List.replicate_succ, List.cons_append, ← ih htail]
      | true =>
          have hl : l = List.replicate l.length true :=
            List.eq_replicate_of_mem (fun b hb => hhead b hb rfl)
          rw [hl]
          simp [List.replicate_succ]

/-- The `length-t` entry of an ascending Boolean list is true exactly when at
least `t` distinct list positions are true. -/
theorem booleanList_selected_eq_true_iff (l : List Bool)
    (h : l.Pairwise (fun a b => a = true → b = true))
    (t : ℕ) (ht : 1 ≤ t) (htl : t ≤ l.length) :
    l[l.length - t]? = some true ↔ t ≤ l.count true := by
  have hc : l.count true ≤ l.length := List.count_le_length
  have heq := booleanList_eq_replicate_of_pairwise l h
  conv_lhs => rw [heq]
  simp only [List.length_append, List.length_replicate]
  by_cases htc : t ≤ l.count true
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    rw [List.getElem?_replicate]
    simp [htc, show l.length - l.count true + l.count true - t -
      (l.length - l.count true) < l.count true by omega]
  · rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_replicate]
    simp [htc, show l.length - l.count true + l.count true - t <
      l.length - l.count true by omega]

/-- Fill a balanced Boolean tree from its zero-based positions. -/
def BooleanWires.tabulate : (d : ℕ) → (ℕ → Bool) → BooleanWires d
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (tabulate d f) (tabulate d (fun i => f (2 ^ d + i)))

/-- Tabulation depends only on positions within the tree. -/
theorem BooleanWires.tabulate_congr (d : ℕ) (f g : ℕ → Bool)
    (h : ∀ i < 2 ^ d, f i = g i) : tabulate d f = tabulate d g := by
  induction d generalizing f g with
  | zero => simp only [tabulate]; rw [h 0 (by simp)]
  | succ d ih =>
      simp only [tabulate]
      apply congrArg₂ BooleanWires.node
      · apply ih
        intro i hi
        exact h i (by simp only [pow_succ, Nat.mul_two]; omega)
      · apply ih
        intro i hi
        exact h (2 ^ d + i) (by simp only [pow_succ, Nat.mul_two]; omega)

/-- A parallel layer acts pointwise on tabulated inputs. -/
theorem booleanLayer_tabulate (up : Bool) (d : ℕ) (f g : ℕ → Bool) :
    booleanLayer up (BooleanWires.tabulate d f) (BooleanWires.tabulate d g) =
      (BooleanWires.tabulate d (fun i => if up then f i && g i else f i || g i),
       BooleanWires.tabulate d (fun i => if up then f i || g i else f i && g i)) := by
  induction d generalizing f g with
  | zero => cases up <;> rfl
  | succ d ih => simp only [BooleanWires.tabulate, booleanLayer, ih]

/-- A constant tree. -/
def BooleanWires.constant (d : ℕ) (b : Bool) : BooleanWires d :=
  tabulate d (fun _ => b)

/-- An interval of equal Boolean values, with the complementary value outside. -/
def BooleanWires.interval (d l r : ℕ) (outside : Bool) : BooleanWires d :=
  tabulate d (fun i => if l ≤ i ∧ i < r then !outside else outside)

/-- Boolean bitonicity: either the true positions or the false positions form
one interval. The endpoint bounds include empty and constant intervals. -/
def BooleanWires.Bitonic {d : ℕ} (a : BooleanWires d) : Prop :=
  ∃ l r outside, l ≤ r ∧ r ≤ 2 ^ d ∧ a = interval d l r outside

/-- Pointwise negation of a Boolean tree. -/
def BooleanWires.negate : {d : ℕ} → BooleanWires d → BooleanWires d
  | _, .leaf a => .leaf (!a)
  | _, .node a b => .node a.negate b.negate

theorem BooleanWires.negate_tabulate (d : ℕ) (f : ℕ → Bool) :
    (tabulate d f).negate = tabulate d (fun i => !(f i)) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih => simp only [tabulate, negate, ih]

theorem BooleanWires.negate_interval (d l r : ℕ) (outside : Bool) :
    (interval d l r outside).negate = interval d l r (!outside) := by
  rw [interval, negate_tabulate, interval]
  apply tabulate_congr
  intro i hi
  split <;> simp_all

theorem BooleanWires.bitonic_constant (d : ℕ) (b : Bool) :
    (constant d b).Bitonic := by
  refine ⟨0, 0, b, Nat.zero_le _, Nat.zero_le _, ?_⟩
  simp [constant, interval]

theorem BooleanWires.Bitonic.negate {d : ℕ} {a : BooleanWires d}
    (h : a.Bitonic) : a.negate.Bitonic := by
  obtain ⟨l, r, b, hl, hr, rfl⟩ := h
  exact ⟨l, r, !b, hl, hr, negate_interval d l r b⟩

theorem booleanMerge_constant (up : Bool) (d : ℕ) (b : Bool) :
    booleanMerge up (BooleanWires.constant d b) = BooleanWires.constant d b := by
  induction d with
  | zero => rfl
  | succ d ih =>
      change BooleanWires.node
        (booleanMerge up (booleanLayer up (BooleanWires.constant d b)
          (BooleanWires.constant d b)).1)
        (booleanMerge up (booleanLayer up (BooleanWires.constant d b)
          (BooleanWires.constant d b)).2) = _
      rw [BooleanWires.constant, booleanLayer_tabulate]
      cases up <;> cases b <;> simpa [BooleanWires.constant, BooleanWires.tabulate] using
        congrArg₂ BooleanWires.node ih ih

/-- Splitting an interval at antipodal positions leaves bitonic halves, with
either an entirely false lower half or an entirely true upper half. -/
theorem booleanLayer_interval_false (d l r : ℕ) (hlr : l ≤ r)
    (hr : r ≤ 2 ^ (d + 1)) :
    let a := BooleanWires.tabulate d (fun i => if l ≤ i ∧ i < r then true else false)
    let b := BooleanWires.tabulate d
      (fun i => if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)
    let c := booleanLayer true a b
    c.1.Bitonic ∧ c.2.Bitonic ∧
      (c.1 = BooleanWires.constant d false ∨ c.2 = BooleanWires.constant d true) := by
  dsimp only
  rw [booleanLayer_tabulate]
  simp only [↓reduceIte]
  simp only [pow_succ, Nat.mul_two] at hr
  by_cases hrn : r ≤ 2 ^ d
  · have hlow : BooleanWires.tabulate d
        (fun i => (if l ≤ i ∧ i < r then true else false) &&
          (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
        BooleanWires.constant d false := by
      apply BooleanWires.tabulate_congr
      intro i hi
      apply Bool.eq_iff_iff.mpr
      simp
      omega
    have hhigh : BooleanWires.tabulate d
        (fun i => (if l ≤ i ∧ i < r then true else false) ||
          (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
        BooleanWires.interval d l r false := by
      apply BooleanWires.tabulate_congr
      intro i hi
      apply Bool.eq_iff_iff.mpr
      simp
      omega
    rw [hlow, hhigh]
    exact ⟨BooleanWires.bitonic_constant _ _, ⟨l, r, false, hlr, hrn, rfl⟩,
      Or.inl rfl⟩
  · by_cases hnl : 2 ^ d ≤ l
    · have hlow : BooleanWires.tabulate d
          (fun i => (if l ≤ i ∧ i < r then true else false) &&
            (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
          BooleanWires.constant d false := by
        apply BooleanWires.tabulate_congr
        intro i hi
        apply Bool.eq_iff_iff.mpr
        simp
        omega
      have hhigh : BooleanWires.tabulate d
          (fun i => (if l ≤ i ∧ i < r then true else false) ||
            (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
          BooleanWires.interval d (l - 2 ^ d) (r - 2 ^ d) false := by
        apply BooleanWires.tabulate_congr
        intro i hi
        apply Bool.eq_iff_iff.mpr
        simp
        omega
      rw [hlow, hhigh]
      exact ⟨BooleanWires.bitonic_constant _ _,
        ⟨l - 2 ^ d, r - 2 ^ d, false, by omega, by omega, rfl⟩, Or.inl rfl⟩
    · by_cases hoverlap : l ≤ r - 2 ^ d
      · have hlow : BooleanWires.tabulate d
            (fun i => (if l ≤ i ∧ i < r then true else false) &&
              (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
            BooleanWires.interval d l (r - 2 ^ d) false := by
          apply BooleanWires.tabulate_congr
          intro i hi
          apply Bool.eq_iff_iff.mpr
          simp
          omega
        have hhigh : BooleanWires.tabulate d
            (fun i => (if l ≤ i ∧ i < r then true else false) ||
              (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
            BooleanWires.constant d true := by
          apply BooleanWires.tabulate_congr
          intro i hi
          apply Bool.eq_iff_iff.mpr
          simp
          omega
        rw [hlow, hhigh]
        exact ⟨⟨l, r - 2 ^ d, false, hoverlap, by omega, rfl⟩,
          BooleanWires.bitonic_constant _ _, Or.inr rfl⟩
      · have hlow : BooleanWires.tabulate d
            (fun i => (if l ≤ i ∧ i < r then true else false) &&
              (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
            BooleanWires.constant d false := by
          apply BooleanWires.tabulate_congr
          intro i hi
          apply Bool.eq_iff_iff.mpr
          simp
          omega
        have hhigh : BooleanWires.tabulate d
            (fun i => (if l ≤ i ∧ i < r then true else false) ||
              (if l ≤ 2 ^ d + i ∧ 2 ^ d + i < r then true else false)) =
            BooleanWires.interval d (r - 2 ^ d) l true := by
          apply BooleanWires.tabulate_congr
          intro i hi
          apply Bool.eq_iff_iff.mpr
          simp
          omega
        rw [hlow, hhigh]
        exact ⟨BooleanWires.bitonic_constant _ _,
          ⟨r - 2 ^ d, l, true, by omega, by omega, rfl⟩, Or.inl rfl⟩

theorem BooleanWires.negate_negate {d : ℕ} (a : BooleanWires d) :
    a.negate.negate = a := by
  induction a with
  | leaf a => cases a <;> rfl
  | node a b ia ib => simp only [negate, ia, ib]

theorem BooleanWires.negate_constant (d : ℕ) (b : Bool) :
    (constant d b).negate = constant d (!b) := negate_tabulate _ _

theorem booleanLayer_false {d : ℕ} (a b : BooleanWires d) :
    booleanLayer false a b = ((booleanLayer true a b).2, (booleanLayer true a b).1) := by
  induction a with
  | leaf a => cases b; rfl
  | node a b ia ib =>
      cases ‹BooleanWires _› with
      | node c d => simp only [booleanLayer, ia c, ib d]

theorem booleanLayer_negate {d : ℕ} (a b : BooleanWires d) :
    booleanLayer true a.negate b.negate =
      ((booleanLayer true a b).2.negate, (booleanLayer true a b).1.negate) := by
  induction a with
  | leaf a => cases b with
    | leaf b => cases a <;> cases b <;> rfl
  | node a b ia ib =>
      cases ‹BooleanWires _› with
      | node c d => simp only [BooleanWires.negate, booleanLayer, ia c, ib d]

theorem booleanLayer_interval_node {d : ℕ} (a b : BooleanWires d)
    (l r : ℕ) (hlr : l ≤ r) (hr : r ≤ 2 ^ (d + 1))
    (h : BooleanWires.node a b = BooleanWires.interval (d + 1) l r false) :
    (booleanLayer true a b).1.Bitonic ∧ (booleanLayer true a b).2.Bitonic ∧
      ((booleanLayer true a b).1 = BooleanWires.constant d false ∨
        (booleanLayer true a b).2 = BooleanWires.constant d true) := by
  simp only [BooleanWires.interval, BooleanWires.tabulate, Bool.not_false] at h
  cases h
  exact booleanLayer_interval_false d l r hlr hr

/-- A bitonic layer produces two bitonic halves and a constant extreme half. -/
theorem booleanLayer_bitonic (up : Bool) {d : ℕ} (a b : BooleanWires d)
    (h : (BooleanWires.node a b).Bitonic) :
    (booleanLayer up a b).1.Bitonic ∧ (booleanLayer up a b).2.Bitonic ∧
      ((booleanLayer up a b).1 = BooleanWires.constant d (!up) ∨
        (booleanLayer up a b).2 = BooleanWires.constant d up) := by
  have htrue : (booleanLayer true a b).1.Bitonic ∧ (booleanLayer true a b).2.Bitonic ∧
      ((booleanLayer true a b).1 = BooleanWires.constant d false ∨
        (booleanLayer true a b).2 = BooleanWires.constant d true) := by
    obtain ⟨l, r, outside, hlr, hr, heq⟩ := h
    cases outside with
    | false => exact booleanLayer_interval_node a b l r hlr hr heq
    | true =>
        have hn : BooleanWires.node a.negate b.negate =
            BooleanWires.interval (d + 1) l r false := by
          simpa only [BooleanWires.negate, BooleanWires.negate_interval, Bool.not_true]
            using congrArg BooleanWires.negate heq
        have hh := booleanLayer_interval_node a.negate b.negate l r hlr hr hn
        rw [booleanLayer_negate] at hh
        refine ⟨?_, ?_, ?_⟩
        · simpa only [BooleanWires.negate_negate] using hh.2.1.negate
        · simpa only [BooleanWires.negate_negate] using hh.1.negate
        · rcases hh.2.2 with hlow | hhigh
          · right
            simpa only [BooleanWires.negate_negate, BooleanWires.negate_constant,
              Bool.not_false] using congrArg BooleanWires.negate hlow
          · left
            simpa only [BooleanWires.negate_negate, BooleanWires.negate_constant,
              Bool.not_true] using congrArg BooleanWires.negate hhigh
  cases up with
  | true => exact htrue
  | false =>
      rw [booleanLayer_false]
      exact ⟨htrue.2.1, htrue.1, htrue.2.2.symm⟩

/-- Ascending or descending order on the flattened Boolean wires. -/
def BooleanWires.Ordered (up : Bool) {d : ℕ} (a : BooleanWires d) : Prop :=
  a.toList.Pairwise (fun x y => if up then x = true → y = true else y = true → x = true)

theorem BooleanWires.mem_constant {d : ℕ} (b x : Bool)
    (h : x ∈ (constant d b).toList) : x = b := by
  induction d with
  | zero => simpa [constant, tabulate, toList] using h
  | succ d ih =>
      change x ∈ (constant d b).toList ++ (constant d b).toList at h
      exact ih (List.mem_append.mp h |>.elim id id)

/-- Recursive bitonic merging orders every bitonic Boolean input. -/
theorem booleanMerge_ordered (up : Bool) {d : ℕ} (a : BooleanWires d)
    (h : a.Bitonic) : (booleanMerge up a).Ordered up := by
  induction d with
  | zero => cases a; simp [BooleanWires.Ordered, booleanMerge, BooleanWires.toList]
  | succ d ih =>
      cases a with
      | node a b =>
          have hc := booleanLayer_bitonic up a b h
          change ((booleanMerge up (booleanLayer up a b).1).toList ++
            (booleanMerge up (booleanLayer up a b).2).toList).Pairwise _
          apply List.pairwise_append.mpr
          refine ⟨ih _ hc.1, ih _ hc.2.1, ?_⟩
          intro x hx y hy
          rcases hc.2.2 with hlow | hhigh
          · rw [hlow, booleanMerge_constant] at hx
            have heq := BooleanWires.mem_constant (!up) x hx
            cases up <;> simp_all
          · rw [hhigh, booleanMerge_constant] at hy
            have heq := BooleanWires.mem_constant up y hy
            cases up <;> simp_all

/-- Flattening is injective at a fixed depth. -/
theorem BooleanWires.toList_injective {d : ℕ} :
    Function.Injective (toList (d := d)) := by
  intro a b h
  induction a with
  | leaf a => cases b; simpa [toList] using h
  | node a b ia ib =>
      cases ‹BooleanWires _› with
      | node c e =>
          have hh := List.append_inj h (by simp [length_toList])
          exact congrArg₂ BooleanWires.node (ia hh.1) (ib hh.2)

/-- Reading a tabulated tree returns the assigned value at each valid position. -/
theorem BooleanWires.getElem?_tabulate (d : ℕ) (f : ℕ → Bool) (i : ℕ)
    (hi : i < 2 ^ d) : (tabulate d f).toList[i]? = some (f i) := by
  induction d generalizing f i with
  | zero =>
      have : i = 0 := by simpa using hi
      subst i
      rfl
  | succ d ih =>
      simp only [tabulate, toList]
      by_cases hin : i < 2 ^ d
      · rw [List.getElem?_append_left (by simpa only [length_toList] using hin)]
        exact ih f i hin
      · rw [List.getElem?_append_right (by simp only [length_toList]; omega),
          length_toList, ih _ _ (by simp only [pow_succ, Nat.mul_two] at hi; omega)]
        congr 2
        omega

/-- Two constant list blocks determine the positional tabulation of a tree. -/
theorem BooleanWires.eq_tabulate_of_blocks {d : ℕ} (a : BooleanWires d)
    (u v : ℕ) (b c : Bool) (huv : u + v = 2 ^ d)
    (h : a.toList = List.replicate u b ++ List.replicate v c) :
    a = tabulate d (fun i => if i < u then b else c) := by
  apply toList_injective
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 ^ d
  · rw [getElem?_tabulate d _ i hi, h]
    by_cases hiu : i < u
    · rw [List.getElem?_append_left (by simpa using hiu)]
      simp [hiu]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp [hiu, show i - u < v by omega]
  · rw [List.getElem?_eq_none (by simp only [length_toList]; omega),
      List.getElem?_eq_none (by simp only [length_toList]; omega)]

/-- The decreasing counterpart of the Boolean block decomposition. -/
theorem booleanList_eq_replicate_of_pairwise_descending (l : List Bool)
    (h : l.Pairwise (fun a b => b = true → a = true)) :
    l = List.replicate (l.count true) true ++
      List.replicate (l.length - l.count true) false := by
  have hr : l.reverse.Pairwise (fun a b => a = true → b = true) := by
    simpa only [List.pairwise_reverse] using h
  have heq := congrArg List.reverse (booleanList_eq_replicate_of_pairwise l.reverse hr)
  simpa using heq

/-- Oppositely ordered halves form a Boolean bitonic input. -/
theorem BooleanWires.bitonic_node_of_ordered {d : ℕ} (a b : BooleanWires d)
    (ha : a.Ordered true) (hb : b.Ordered false) : (node a b).Bitonic := by
  have hca : a.toList.count true ≤ 2 ^ d := by
    simpa only [length_toList] using (List.count_le_length (l := a.toList) (a := true))
  have hcb : b.toList.count true ≤ 2 ^ d := by
    simpa only [length_toList] using (List.count_le_length (l := b.toList) (a := true))
  have hea := eq_tabulate_of_blocks a (2 ^ d - a.toList.count true)
    (a.toList.count true) false true (by omega)
    (by simpa only [length_toList] using booleanList_eq_replicate_of_pairwise a.toList ha)
  have heb := eq_tabulate_of_blocks b (b.toList.count true)
    (2 ^ d - b.toList.count true) true false (by omega)
    (by simpa only [length_toList] using
      booleanList_eq_replicate_of_pairwise_descending b.toList hb)
  refine ⟨2 ^ d - a.toList.count true, 2 ^ d + b.toList.count true, false,
    by omega, by simp only [pow_succ, Nat.mul_two]; omega, ?_⟩
  rw [interval, tabulate]
  apply congrArg₂ node
  · conv_lhs => rw [hea]
    apply tabulate_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simp
    omega
  · conv_lhs => rw [heb]
    apply tabulate_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simp
    omega

/-- The exact fixed bitonic sorting schedule orders every Boolean input. -/
theorem booleanSort_ordered (up : Bool) {d : ℕ} (a : BooleanWires d) :
    (booleanSort up a).Ordered up := by
  induction a generalizing up with
  | leaf a => simp [booleanSort, BooleanWires.Ordered, BooleanWires.toList]
  | node a b ia ib =>
      exact booleanMerge_ordered up _
        (BooleanWires.bitonic_node_of_ordered _ _ (ia true) (ib false))

/-- Ascending sortedness of the executed Boolean network, without assumptions. -/
theorem booleanSort_pairwise {d : ℕ} (a : BooleanWires d) :
    (booleanSort true a).toList.Pairwise (fun x y => x = true → y = true) :=
  booleanSort_ordered true a

variable {F K : Type*} [Field F] [BEq F] [LawfulBEq F] [Field K]

/-- A single polynomial's vanishing indicator. -/
noncomputable def rootIndicator (phi : F →+* K) (x : K) (f : CPolynomial F) : Bool := by
  classical
  exact decide (f.toPoly.eval₂ phi x = 0)

/-- Record whether each wire vanishes at the specified extension-field point. -/
noncomputable def rootWires (phi : F →+* K) (x : K) :
    {d : ℕ} → Wires F d → BooleanWires d := by
  classical
  exact fun {d} a => match d, a with
    | _, .leaf f => .leaf (decide (f.toPoly.eval₂ phi x = 0))
    | _, .node a b => .node (rootWires phi x a) (rootWires phi x b)

omit [BEq F] [LawfulBEq F] in
/-- Flattening the root indicators is pointwise evaluation of the wire list. -/
theorem rootWires_toList (phi : F →+* K) (x : K) {d : ℕ} (a : Wires F d) :
    (rootWires phi x a).toList =
      a.toList.map (rootIndicator phi x) := by
  classical
  induction a with
  | leaf a => rfl
  | node a b ia ib => simp [rootWires, BooleanWires.toList, Wires.toList, ia, ib]

omit [BEq F] [LawfulBEq F] in
/-- The Boolean execution counts precisely the polynomial vanishing positions. -/
theorem rootWires_count (phi : F →+* K) (x : K) {d : ℕ} (a : Wires F d) :
    (rootWires phi x a).count = rootCount phi x a := by
  classical
  induction a with
  | leaf a => simp [rootWires, BooleanWires.count, rootCount]
  | node a b ia ib => simp [rootWires, BooleanWires.count, rootCount, ia, ib]

/-- Polynomial comparator layers implement exactly Boolean AND/OR layers. -/
theorem rootWires_layer (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a b : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) (hb : b.All (fun f => f ≠ 0)) :
    (rootWires phi x (layer up a b).1, rootWires phi x (layer up a b).2) =
      booleanLayer up (rootWires phi x a) (rootWires phi x b) := by
  classical
  induction a with
  | leaf a =>
      cases b with
      | leaf b =>
          have hs := compare_fst_eval₂_eq_zero_iff phi x a b
          have hl := compare_snd_eval₂_eq_zero_iff phi x (b := b) ha
          cases up <;> simp [layer, booleanLayer, rootWires, hs, hl]
  | node a b ia ib =>
      cases ‹Wires F _› with
      | node c d =>
          have hac := ia c ha.1 hb.1
          have hbd := ib d ha.2 hb.2
          have hac₁ := congrArg Prod.fst hac
          have hac₂ := congrArg Prod.snd hac
          have hbd₁ := congrArg Prod.fst hbd
          have hbd₂ := congrArg Prod.snd hbd
          simp only [layer, rootWires, booleanLayer]
          exact congrArg₂ Prod.mk (congrArg₂ BooleanWires.node hac₁ hbd₁)
            (congrArg₂ BooleanWires.node hac₂ hbd₂)

/-- Vanishing semantics commutes with every recursive merge. -/
theorem rootWires_merge (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    rootWires phi x (merge up a) = booleanMerge up (rootWires phi x a) := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
      cases a with
      | node a b =>
          have hn := layer_all _ (fun _ _ ha hb => compare_ne_zero ha hb)
            up a b ha.1 ha.2
          have hl := rootWires_layer phi x up a b ha.1 ha.2
          have hl₁ := congrArg Prod.fst hl
          have hl₂ := congrArg Prod.snd hl
          dsimp only at hl₁ hl₂
          simp only [merge, rootWires, booleanMerge]
          rw [ih _ hn.1, ih _ hn.2, hl₁, hl₂]

/-- Over every field extension, the polynomial network executes the exact
Boolean schedule on the input vanishing indicators. -/
theorem rootWires_sort (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    rootWires phi x (sort up a) = booleanSort up (rootWires phi x a) := by
  induction a generalizing up with
  | leaf a => rfl
  | node a b ia ib =>
      change rootWires phi x (merge up (.node (sort true a) (sort false b))) = _
      rw [rootWires_merge phi x up (.node (sort true a) (sort false b))
        ⟨sort_ne_zero true a ha.1, sort_ne_zero false b ha.2⟩]
      simp only [rootWires, booleanSort, ia true ha.1, ib false ha.2]

/-- Selection correctness reduces to the explicit Boolean sortedness property
of the executed schedule. This bridge preserves the original positional count. -/
theorem selected_root_iff_of_boolean_sorted (phi : F →+* K) (x : K)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0))
    (hsorted : (booleanSort true (rootWires phi x a)).toList.Pairwise
      (fun a b => a = true → b = true))
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ 2 ^ d) (H : CPolynomial F)
    (hH : (sort true a).toList[2 ^ d - t]? = some H) :
    H.toPoly.eval₂ phi x = 0 ↔ t ≤ rootCount phi x a := by
  classical
  have hs : (rootWires phi x (sort true a)).toList.Pairwise
      (fun a b => a = true → b = true) := by
    rw [rootWires_sort phi x true a ha]
    exact hsorted
  have hsel := booleanList_selected_eq_true_iff
    (rootWires phi x (sort true a)).toList hs t ht
    (by simpa only [BooleanWires.length_toList] using htn)
  rw [BooleanWires.length_toList, ← BooleanWires.count_eq_count_toList,
    rootWires_count, sort_rootCount phi x true a ha] at hsel
  rw [rootWires_toList, List.getElem?_map, hH] at hsel
  simpa [rootIndicator] using hsel

/-- The selected `N-t` polynomial vanishes exactly when at least `t` original
wire positions vanish, for the exact executed bitonic schedule. -/
theorem selected_root_iff (phi : F →+* K) (x : K)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0))
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ 2 ^ d) (H : CPolynomial F)
    (hH : (sort true a).toList[2 ^ d - t]? = some H) :
    H.toPoly.eval₂ phi x = 0 ↔ t ≤ rootCount phi x a :=
  selected_root_iff_of_boolean_sorted phi x a ha
    (booleanSort_pairwise _) t ht htn H hH

/-- The executable array threshold is correct over every extension field.
The sum counts distinct original array positions; repeated roots within one
polynomial contribute only one, and unit padding contributes zero. -/
theorem threshold_eval₂_eq_zero_iff (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (hinput : ∀ f ∈ input, f ≠ 0)
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ input.size) (H : CPolynomial F)
    (hH : threshold input t = some H) :
    H.toPoly.eval₂ phi x = 0 ↔
      t ≤ ∑ i ∈ Finset.range input.size, positionRootCount phi x input i := by
  have hn := paddingDepth_sufficient input.size
  have hselected : (sort true (padded input (paddingDepth input.size) 0)).toList[
      2 ^ paddingDepth input.size - t]? = some H := by
    simpa only [threshold, ht, htn, and_self, ↓reduceIte] using hH
  have hcorrect := selected_root_iff phi x _
    (padded_ne_zero input hinput _ _) t ht (by omega) H hselected
  rwa [rootCount_padded_eq_original phi x input _ hn] at hcorrect

/-- Distinct original array indices whose polynomials vanish at the point. -/
noncomputable def vanishingPositions (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) : Finset ℕ := by
  classical
  exact (Finset.range input.size).filter
    (fun i => (input[i]?.getD 1).toPoly.eval₂ phi x = 0)

/-- Threshold roots are characterized by the cardinality of the original
vanishing-position set, with no Boolean sortedness premise. -/
theorem threshold_root_positions_iff (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (hinput : ∀ f ∈ input, f ≠ 0)
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ input.size) (H : CPolynomial F)
    (hH : threshold input t = some H) :
    H.toPoly.eval₂ phi x = 0 ↔ t ≤ (vanishingPositions phi x input).card := by
  classical
  simpa only [positionRootCount, Finset.sum_boole, Nat.cast_id, vanishingPositions] using
    threshold_eval₂_eq_zero_iff phi x input hinput t ht htn H hH

end CompPoly.CPolynomial.PolynomialThreshold
