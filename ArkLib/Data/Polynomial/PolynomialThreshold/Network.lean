/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PolynomialThreshold.Comparator

/-!
# Fixed bitonic polynomial network

Balanced wire trees enforce power-of-two network sizes. Each merge layer
compares corresponding wires in its two halves. Recursive sorting uses opposite
directions in the halves before merging, as in the bitonic sorting network.
-/

@[expose] public section

namespace CompPoly.CPolynomial.PolynomialThreshold

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- A power-of-two collection of wires, in left-to-right order. -/
inductive Wires (F : Type*) [Field F] : ℕ → Type _ where
  | leaf : CPolynomial F → Wires F 0
  | node {d : ℕ} : Wires F d → Wires F d → Wires F (d + 1)

/-- Universal wire predicate. -/
def Wires.All (P : CPolynomial F → Prop) : {d : ℕ} → Wires F d → Prop
  | _, .leaf a => P a
  | _, .node a b => a.All P ∧ b.All P

/-- Sum of the degrees on all wires. -/
def Wires.degree : {d : ℕ} → Wires F d → ℕ
  | _, .leaf a => a.natDegree
  | _, .node a b => a.degree + b.degree

/-- Flatten wires in their fixed network order. -/
def Wires.toList : {d : ℕ} → Wires F d → List (CPolynomial F)
  | _, .leaf a => [a]
  | _, .node a b => a.toList ++ b.toList

omit [BEq F] [LawfulBEq F] in
/-- Tree depth fixes the number of wires independently of their values. -/
theorem Wires.length_toList {d : ℕ} (a : Wires F d) : a.toList.length = 2 ^ d := by
  induction a with
  | leaf a => rfl
  | node a b ia ib => simp [toList, ia, ib, pow_succ, Nat.mul_two]

/-- One layer of parallel comparators; `up` puts smaller outputs first. -/
def layer (up : Bool) : {d : ℕ} → Wires F d → Wires F d → Wires F d × Wires F d
  | _, .leaf a, .leaf b =>
      let c := compare a b
      if up then (.leaf c.1, .leaf c.2) else (.leaf c.2, .leaf c.1)
  | _, .node a b, .node c d =>
      let ac := layer up a c
      let bd := layer up b d
      (.node ac.1 bd.1, .node ac.2 bd.2)

/-- Recursive bitonic merge in a fixed direction. -/
def merge (up : Bool) : {d : ℕ} → Wires F d → Wires F d
  | _, .leaf a => .leaf a
  | _, .node a b =>
      let c := layer up a b
      .node (merge up c.1) (merge up c.2)

/-- The fixed bitonic sorting network; its comparator schedule ignores values. -/
def sort (up : Bool) : {d : ℕ} → Wires F d → Wires F d
  | _, .leaf a => .leaf a
  | _, .node a b => merge up (.node (sort true a) (sort false b))

/-- Fill a power-of-two tree from an offset, padding missing positions by one. -/
def padded (input : Array (CPolynomial F)) : (d : ℕ) → ℕ → Wires F d
  | 0, offset => .leaf (input[offset]?.getD 1)
  | d + 1, offset => .node (padded input d offset) (padded input d (offset + 2 ^ d))

/-- Find a sufficient power of two by doubling, with a size-derived fuel bound. -/
def paddingDepthAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, depth => depth
  | fuel + 1, n, depth =>
      if n ≤ 2 ^ depth then depth else paddingDepthAux fuel n (depth + 1)

/-- Depth of the least power of two reached by the doubling loop. -/
def paddingDepth (n : ℕ) : ℕ := paddingDepthAux n n 0

/-- Execute the ascending network and select the one-based `t`-th largest wire.
Invalid thresholds are rejected. The padded array has `N = 2^d` wires, so the
selected zero-based index is `N-t`. -/
def threshold (input : Array (CPolynomial F)) (t : ℕ) : Option (CPolynomial F) :=
  if 1 ≤ t ∧ t ≤ input.size then
    let d := paddingDepth input.size
    (sort true (padded input d 0)).toList[2 ^ d - t]?
  else none

/-- A comparator layer preserves a predicate whenever each comparator does. -/
theorem layer_all (P : CPolynomial F → Prop)
    (hc : ∀ a b, P a → P b → P (compare a b).1 ∧ P (compare a b).2)
    (up : Bool) {d : ℕ} (a b : Wires F d) (ha : a.All P) (hb : b.All P) :
    (layer up a b).1.All P ∧ (layer up a b).2.All P := by
  induction a with
  | leaf a =>
      cases b with
      | leaf b =>
          have h := hc a b ha hb
          cases up <;> simp_all [layer, Wires.All]
  | node a b ia ib =>
      cases ‹Wires F _› with
      | node c d =>
          obtain ⟨ha', hb'⟩ := ha
          obtain ⟨hc', hd⟩ := hb
          have hac := ia c ha' hc'
          have hbd := ib d hb' hd
          exact ⟨⟨hac.1, hbd.1⟩, ⟨hac.2, hbd.2⟩⟩

/-- Every merge preserves a comparator-invariant wire predicate. -/
theorem merge_all (P : CPolynomial F → Prop)
    (hc : ∀ a b, P a → P b → P (compare a b).1 ∧ P (compare a b).2)
    (up : Bool) {d : ℕ} (a : Wires F d) (ha : a.All P) :
    (merge up a).All P := by
  induction d with
  | zero => cases a; exact ha
  | succ d ih =>
      cases a with
      | node a b =>
          have h := layer_all P hc up a b ha.1 ha.2
          exact ⟨ih _ h.1, ih _ h.2⟩

/-- The entire fixed network preserves a comparator-invariant predicate. -/
theorem sort_all (P : CPolynomial F → Prop)
    (hc : ∀ a b, P a → P b → P (compare a b).1 ∧ P (compare a b).2)
    (up : Bool) {d : ℕ} (a : Wires F d) (ha : a.All P) :
    (sort up a).All P := by
  induction a generalizing up with
  | leaf a => exact ha
  | node a b ia ib =>
      exact merge_all P hc up _ ⟨ia true ha.1, ib false ha.2⟩

/-- Monic inputs remain monic throughout the network. -/
theorem sort_monic (up : Bool) {d : ℕ} (a : Wires F d)
    (ha : a.All (fun f => f.monic)) :
    (sort up a).All (fun f => f.monic) :=
  sort_all _ (fun _ _ ha hb => compare_monic ha hb) up a ha

/-- Nonzero inputs remain nonzero throughout the network. -/
theorem sort_ne_zero (up : Bool) {d : ℕ} (a : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) :
    (sort up a).All (fun f => f ≠ 0) :=
  sort_all _ (fun _ _ ha hb => compare_ne_zero ha hb) up a ha

/-- Each parallel comparator layer conserves total degree. -/
theorem layer_degree (up : Bool) {d : ℕ} (a b : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) (hb : b.All (fun f => f ≠ 0)) :
    (layer up a b).1.degree + (layer up a b).2.degree = a.degree + b.degree := by
  induction a with
  | leaf a =>
      cases b with
      | leaf b =>
          have h := compare_degree ha hb
          cases up <;> simp_all [layer, Wires.degree, Nat.add_comm]
  | node a b ia ib =>
      cases ‹Wires F _› with
      | node c d =>
          have hac := ia c ha.1 hb.1
          have hbd := ib d ha.2 hb.2
          simp only [layer, Wires.degree]
          omega

/-- A bitonic merge conserves total degree across its layers. -/
theorem merge_degree (up : Bool) {d : ℕ} (a : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) : (merge up a).degree = a.degree := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
      cases a with
      | node a b =>
          have h := layer_all _ (fun _ _ ha hb => compare_ne_zero ha hb) up a b ha.1 ha.2
          simp only [merge, Wires.degree]
          rw [ih _ h.1, ih _ h.2]
          exact layer_degree up a b ha.1 ha.2

/-- Sorting conserves the sum of degrees of every input wire. -/
theorem sort_degree (up : Bool) {d : ℕ} (a : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) : (sort up a).degree = a.degree := by
  induction a generalizing up with
  | leaf a => rfl
  | node a b ia ib =>
      change (merge up (.node (sort true a) (sort false b))).degree = _
      rw [merge_degree up (.node (sort true a) (sort false b))
        ⟨sort_ne_zero true a ha.1, sort_ne_zero false b ha.2⟩]
      simp only [Wires.degree, ia true ha.1, ib false ha.2]

end CompPoly.CPolynomial.PolynomialThreshold
