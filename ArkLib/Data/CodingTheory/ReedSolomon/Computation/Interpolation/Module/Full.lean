/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Local
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.RemainderMap

/-! # Full normalized local modules for interpolation

The finite target retains every `T^t V^u Y^b` with `t < m` and `u + sum b ≤ B`,
including rows outside the image of the old contact coordinates. Normalization sends
`T^i E^u Y^b` to `T^(i+d*u) V^u Y^b`. The full target has ordinary Jordan blocks.
This file constructs their matrices and generator vectors; it supplies no minimal-basis solver.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationModule

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Extend contact coordinates to the full normalized module, retaining extra rows as zero. -/
def extend (v : Coordinates F d) : Coordinates F d := fun e =>
  if d * e (some none) ≤ e none then
    v (fun j => if j = none then e none - d * e (some none) else e j)
  else 0

/-- Read the old contact coordinates at their normalized row positions. -/
def restrict (v : Coordinates F d) : Coordinates F d := fun e =>
  v (fun j => if j = none then e none + d * e (some none) else e j)

/-- Ordinary T-truncated Jordan action on the full target, without a contact-order guard. -/
def fullJordan (m : ℕ) (a : F) (v : Coordinates F d) : Coordinates F d := fun e =>
  if e none < m then
    a * v e + if e none = 0 then 0 else v (fun j => if j = none then e j - 1 else e j)
  else 0

/-- Materialize the complete bounded jet frame, including all possible V exponents. -/
def jetFrame (d B : ℕ) : List (List ℕ) :=
  (List.CartesianProductMachine.productSpec
    (List.replicate (d + 1) (List.range (B + 1)))).filter (fun b => b.sum ≤ B)

/-- Full local frame in Jordan-block order: jet monomial first, then increasing T exponent. -/
def fullFrame (d m B : ℕ) : List (List ℕ) :=
  (jetFrame d B).flatMap (fun b => (List.range m).map (fun t => t :: b))

/-- Interpret a stored frame vector as an executable coordinate query. -/
def frameQuery (d : ℕ) (row : List ℕ) : LocalVariable d → ℕ
  | none => row.getD 0 0
  | some none => row.getD 1 0
  | some (some j) => row.getD (j.val + 2) 0

/-- One ordinary Jordan matrix in coefficient-column convention. -/
def jordanMatrix (m : ℕ) (a : F) : List (List F) :=
  (List.range m).map fun t => (List.range m).map fun s =>
    (if t = s then a else 0) + (if t = s + 1 then 1 else 0)

/-- The full local multiplication operator is a list of identical Jordan blocks. -/
def fullMatrix (d m B : ℕ) (a : F) : List (List (List F)) :=
  (jetFrame d B).map (fun _ => jordanMatrix m a)

/-- Materialize normalized coordinates of an already executed scalar seed. -/
def fullSeed (d m B : ℕ) (seed : InterpolationPointBlockMachine.DenseColumn F) : List F :=
  (fullFrame d m B).map (fun row => extend (denseCoordinates seed) (frameQuery d row))

/-- Build the full generator vector at one point, using the actual zero-X column program. -/
def generator? (d m B : ℕ) (a y : F) (b : JetMonomial) : Option (List F) :=
  (zeroColumn d m a y b).1.map (fullSeed d m B)

/-- Concrete materialized input for a future minimal interpolation basis implementation.
The block order is point, jet monomial, T exponent; generator rows share this order. -/
structure FullInstance (F : Type*) where
  frame : List (List ℕ)
  blocks : List (List (List F))
  generators : List (List F)
  shifts : List ℕ
  cutoff : ℕ
  deriving Repr

/-- Assemble every generator across all received points; failure is an actual column failure. -/
def generatorAcross? (d m B : ℕ) (received : List (F × F)) (b : JetMonomial) :
    Option (List F) := do
  let rows ← received.mapM (fun p => generator? d m B p.1 p.2 b)
  return rows.flatten

/-- Materialize the exact matrix/vector inputs. No solver callback is accepted. -/
def buildFull? (d m B D W : ℕ) (received : List (F × F)) (bs : List JetMonomial) :
    Option (FullInstance F) := do
  if bs.all (fun b => b.higher.length == d && b.zeroth + b.higher.sum ≤ B) then
    pure PUnit.unit
  else
    none
  let generators ← bs.mapM (generatorAcross? d m B received)
  return ⟨fullFrame d m B, received.flatMap (fun p => fullMatrix d m B p.1),
    generators, bs.map (fun b => b.weight D), W⟩

@[simp]
theorem restrict_extend (v : Coordinates F d) : restrict (extend v) = v := by
  funext e
  simp only [restrict, extend, ↓reduceIte, reduceCtorEq]
  simp only [Nat.le_add_left, if_true, Nat.add_sub_cancel_right]
  congr 1
  funext j
  by_cases h : j = none <;> simp [h]

/-- Every row outside the normalization image remains present and has coefficient zero. -/
theorem extend_extra_row (v : Coordinates F d) (e : LocalVariable d → ℕ)
    (he : e none < d * e (some none)) : extend v e = 0 := by
  simp [extend, Nat.not_le.mpr he]

/-- Exact finite frame membership, including the full rows omitted by contact coordinates. -/
theorem mem_fullFrame (d m B t : ℕ) (b : List ℕ) :
    t :: b ∈ fullFrame d m B ↔
      t < m ∧ b ∈ jetFrame d B := by
  simp only [fullFrame, List.mem_flatMap, List.mem_map, List.cons.injEq, List.mem_range]
  constructor
  · rintro ⟨b', hb, t', ht, rfl, rfl⟩
    exact ⟨ht, hb⟩
  · rintro ⟨ht, hb⟩
    exact ⟨b, hb, t, ht, rfl, rfl⟩

/-- The finite jet frame is complete for the total-degree cutoff, not a contact cutoff. -/
theorem mem_jetFrame (d B : ℕ) (b : List ℕ) :
    b ∈ jetFrame d B ↔ b.length = d + 1 ∧ b.sum ≤ B := by
  have hcoord : ∀ a ∈ b, a ≤ b.sum := by
    intro a ha
    induction b with
    | nil => simp at ha
    | cons c cs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · have h := ih ha; simp only [List.sum_cons]; omega
  simp only [jetFrame, List.mem_filter, decide_eq_true_eq]
  rw [List.CartesianProductMachine.mem_productSpec,
    InterpolationSupportMachine.forall₂_jet_axes]
  constructor
  · tauto
  · rintro ⟨hw, hs⟩
    exact ⟨⟨hw, fun a ha => by have h := hcoord a ha; omega⟩, hs⟩

/-- The full frame is m copies of every bounded jet coordinate. -/
theorem fullFrame_length (d m B : ℕ) :
    (fullFrame d m B).length = (jetFrame d B).length * m := by
  simp [fullFrame, List.length_flatMap]

/-- Every ordinary Jordan block entry is explicitly materialized. -/
theorem jordanMatrix_entry (m : ℕ) (a : F) (i j : Fin m) :
    ((jordanMatrix m a)[i.val]'(by simp [jordanMatrix, i.isLt]))[j.val]'(by
      simp [jordanMatrix, j.isLt]) =
      (if i = j then a else 0) + (if i.val = j.val + 1 then 1 else 0) := by
  simp [jordanMatrix, Fin.ext_iff]

/-- Matrix-vector multiplication has the ordinary truncated Jordan coefficient action. -/
theorem jordanMatrix_action (m : ℕ) (a : F) (v : Fin m → F) (i : Fin m) :
    (∑ j : Fin m, ((if i = j then a else 0) +
      (if i.val = j.val + 1 then 1 else 0)) * v j) =
      a * v i + if h : i.val = 0 then 0 else v ⟨i.val - 1, by omega⟩ := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  congr 1
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro j _
    simp [h]
  · have he : ∀ j : Fin m, i.val = j.val + 1 ↔ j = ⟨i.val - 1, by omega⟩ := by
      intro j
      rw [Fin.ext_iff]
      change i.val = j.val + 1 ↔ j.val = i.val - 1
      omega
    simp only [he]
    simp

/-- The materialized Jordan matrix has exactly m rows of width m, including m=0. -/
theorem jordanMatrix_shape (m : ℕ) (a : F) :
    (jordanMatrix m a).length = m ∧ ∀ row ∈ jordanMatrix m a, row.length = m := by
  simp [jordanMatrix]

/-- Every generator vector has exactly the full local frame width. -/
theorem fullSeed_length (d m B : ℕ) (seed : InterpolationPointBlockMachine.DenseColumn F) :
    (fullSeed d m B seed).length = (fullFrame d m B).length := by
  simp [fullSeed]

noncomputable section

open MvPolynomial

private theorem normalized_index (e : LocalVariable d → ℕ) :
    normalizeLocalExponent d (index e) =
      index (fun j => if j = none then e none + d * e (some none) else e j) := by
  ext j
  rcases j with (_ | (_ | j)) <;>
    simp [normalizeLocalExponent, localT, localE, localAux]

private theorem coeff_normalize (P : LocalPolynomial F d) (e : LocalVariable d →₀ ℕ) :
    coeff (normalizeLocalExponent d e) (normalizeError d P) = coeff e P := by
  rw [normalizeError_eq_normalizeErrorByExponent]
  change Finsupp.mapDomain (normalizeLocalExponent d) (AddMonoidAlgebra.coeff P)
    (normalizeLocalExponent d e) = _
  exact Finsupp.mapDomain_apply (normalizeLocalExponent_injective d) _ e

/-- The executable extension has exactly the coefficient meaning of error normalization. -/
theorem extend_coeff (P : LocalPolynomial F d) :
    extend (fun e => coeff (index e) P) = fun e => coeff (index e) (normalizeError d P) := by
  funext e
  by_cases h : d * e (some none) ≤ e none
  · let f : LocalVariable d → ℕ :=
      fun j => if j = none then e none - d * e (some none) else e j
    have hf : normalizeLocalExponent d (index f) = index e := by
      ext j
      rcases j with (_ | (_ | j)) <;>
        simp [f, normalizeLocalExponent, localT, localE, localAux, Nat.sub_add_cancel h]
    simp only [extend, h, if_true]
    exact (coeff_normalize P (index f)).symm.trans (congrArg (fun z =>
      coeff z (normalizeError d P)) hf)
  · have hn : index e ∉ Set.range (normalizeLocalExponent d) := by
      rintro ⟨f, hf⟩
      have ht := congrArg (fun z => z (localT d)) hf
      have he := congrArg (fun z => z (localE d)) hf
      have ht' : f none + d * f (some none) = e none := by
        simpa [normalizeLocalExponent, localT, localE, localAux] using ht
      have he' : f (some none) = e (some none) := by
        simpa [normalizeLocalExponent, localT, localE, localAux] using he
      rw [he'] at ht'
      omega
    simp only [extend, h, if_false]
    symm
    rw [normalizeError_eq_normalizeErrorByExponent]
    change Finsupp.mapDomain (normalizeLocalExponent d) (AddMonoidAlgebra.coeff P) (index e) = 0
    exact Finsupp.mapDomain_of_notMem_range _ _ hn

/-- The full Jordan action is ordinary multiplication by a+T followed by T truncation. -/
theorem fullJordan_coeff (m : ℕ) (a : F) (P : LocalPolynomial F d) :
    fullJordan m a (fun e => coeff (index e) P) = fun e =>
      coeff (index e) (truncateLocalT m ((C a + X (localT d)) * P)) := by
  funext e
  have hp : index (fun j => if j = none then e j - 1 else e j) =
      index e - Finsupp.single (localT d) 1 := by
    ext j
    by_cases h : j = none <;> simp [h, localT]
  change fullJordan m a (fun e => coeff (index e) P) e =
    if e none < m then coeff (index e) ((C a + X (localT d)) * P) else 0
  simp only [fullJordan]
  by_cases h : e none < m <;>
    simp [h, add_mul, coeff_X_mul', Finsupp.mem_support_iff, hp, localT]

/-- A generated full vector consists of the manuscript's normalized local coefficients. -/
theorem fullSeed_coeff (d m B : ℕ) (a y : F) (b : JetMonomial)
    (hb : b.higher.length = d) :
    fullSeed d m B (InterpolationPointBlockMachine.columnValue d m a y (b.vector 0)) =
      (fullFrame d m B).map (fun row => coeff (index (frameQuery d row))
        (normalizedLocalConstraintAt m a y
          (InterpolationPointBlockMachine.sourceValue d (b.vector 0)))) := by
  obtain ⟨_, _, hp, hw, _⟩ := InterpolationPointBlockMachine.makeColumn_refines
    m a y 0 b.zeroth b.higher hb
  unfold fullSeed
  simp only [JetMonomial.vector]
  rw [denseCoordinates_coeff _ hw, extend_coeff, hp,
    normalizedLocalConstraintAt_eq_normalize_localConstraintAt]

/-- Every well-shaped jet monomial produces its full normalized local generator. -/
theorem generator_success (d m B : ℕ) (a y : F) (b : JetMonomial)
    (hb : b.higher.length = d) :
    generator? d m B a y b = some ((fullFrame d m B).map (fun row =>
      coeff (index (frameQuery d row)) (normalizedLocalConstraintAt m a y
        (InterpolationPointBlockMachine.sourceValue d (b.vector 0))))) := by
  obtain ⟨c, hc, _⟩ := zeroColumn_refines m a y b hb
  simp only [generator?, hc, Option.map_some]
  rw [fullSeed_coeff d m B a y b hb]

private theorem mapM_some {α β : Type*} (xs : List α) (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.mapM_cons, h x (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Constructor success exposes the actual full normalized generators in the common row order. -/
theorem buildFull_success (d m B D W : ℕ) (received : List (F × F)) (bs : List JetMonomial)
    (hb : ∀ b ∈ bs, b.higher.length = d ∧ b.zeroth + b.higher.sum ≤ B) :
    buildFull? d m B D W received bs = some
      ⟨fullFrame d m B, received.flatMap (fun p => fullMatrix d m B p.1),
        bs.map (fun b => received.flatMap (fun p => (fullFrame d m B).map (fun row =>
          coeff (index (frameQuery d row)) (normalizedLocalConstraintAt m p.1 p.2
            (InterpolationPointBlockMachine.sourceValue d (b.vector 0)))))),
        bs.map (fun b => b.weight D), W⟩ := by
  have hg : bs.all (fun b => b.higher.length == d && b.zeroth + b.higher.sum ≤ B) = true := by
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact hb
  have hp : ∀ b ∈ bs, generatorAcross? d m B received b = some
      (received.flatMap (fun p => (fullFrame d m B).map (fun row =>
        coeff (index (frameQuery d row)) (normalizedLocalConstraintAt m p.1 p.2
          (InterpolationPointBlockMachine.sourceValue d (b.vector 0)))))) := by
    intro b hmem
    unfold generatorAcross?
    rw [mapM_some received _ _ (fun p _ => generator_success d m B p.1 p.2 b (hb b hmem).1)]
    simp [List.flatMap_def]
  simp only [buildFull?, hg, ↓reduceIte, pure, bind]
  rw [mapM_some bs _ _ hp]
  rfl

/-- Restriction of the normalized polynomial recovers all original coefficients. -/
theorem restrict_normalized_coeff (P : LocalPolynomial F d) :
    restrict (fun e => coeff (index e) (normalizeError d P)) = fun e => coeff (index e) P := by
  funext e
  simp only [restrict, ← normalized_index, coeff_normalize]

/-- Restricting the full Jordan action on normalized coefficients recovers the scalar action. -/
theorem restrict_fullJordan (m : ℕ) (a : F) (P : LocalPolynomial F d) :
    restrict (fullJordan m a (extend (fun e => coeff (index e) P))) =
      jordan m a (fun e => coeff (index e) P) := by
  rw [extend_coeff, fullJordan_coeff]
  have hm : (C a + X (localT d)) * normalizeError d P =
      normalizeError d ((C a + X (localT d)) * P) := by simp
  rw [hm, truncateLocalT_normalizeError, restrict_normalized_coeff, jordan_coeff]

/-- Executed full rows at normalized old coordinates recover the reviewed scalar adapter. -/
theorem fullSeed_restrict (seed : InterpolationPointBlockMachine.DenseColumn F) :
    restrict (extend (denseCoordinates (d := d) seed)) = denseCoordinates seed :=
  restrict_extend _

/-- Normalized local constraints and the old scalar constraints have exactly the same kernel. -/
theorem normalized_kernel (m : ℕ) (a y : F)
    (Q : PolynomialDifferential.DifferentialPolynomial F d) :
    normalizedLocalConstraintAt m a y Q = 0 ↔ localConstraintAt m a y Q = 0 :=
  normalizedLocalConstraintAt_eq_zero_iff m a y Q

/-- No constraint is lost by the finite full frame when the source has the certified jet cap. -/
theorem fullFrame_kernel (m B : ℕ) (a y : F)
    (Q : PolynomialDifferential.DifferentialPolynomial F d)
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B) :
    (∀ row ∈ fullFrame d m B, coeff (index (frameQuery d row))
      (normalizedLocalConstraintAt m a y Q) = 0) ↔ localConstraintAt m a y Q = 0 := by
  constructor
  · intro h
    apply MvPolynomial.ext
    intro e
    by_cases he : coeff e (localConstraintAt m a y Q) = 0
    · simpa using he
    · have hp : localContactOrder d e < m ∧
          e ∈ (unscaledLocalSubstitution d a y Q).support := by
        change coeff e (projectLowContact m (unscaledLocalSubstitution d a y Q)) ≠ 0 at he
        rw [projectLowContact, coeff_filterLocalMonomials] at he
        split_ifs at he with hc
        · exact ⟨hc, MvPolynomial.mem_support_iff.mpr he⟩
        · exact False.elim (he rfl)
      have hd := unscaledLocal_jet_degree_le a y hQ hp.2
      let row := (e none + d * e (some none)) :: e (some none) ::
        List.ofFn (fun j : Fin d => e (some (some j)))
      have hr : row ∈ fullFrame d m B := by
        rw [mem_fullFrame, mem_jetFrame]
        constructor
        · simpa [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
            localContactWeight, mul_comm] using hp.1
        · constructor
          · simp
          · simpa [reachableLocalJetDegree, Finsupp.degree_eq_sum,
              Fintype.sum_option, List.sum_ofFn] using hd
      have hi : index (frameQuery d row) = normalizeLocalExponent d e := by
        ext j
        rcases j with (_ | (_ | j)) <;>
          simp [frameQuery, row, normalizeLocalExponent, localT, localE, localAux,
            List.getD_eq_getElem?_getD]
      have hz := h row hr
      rw [hi, normalizedLocalConstraintAt_eq_normalize_localConstraintAt,
        coeff_normalize] at hz
      simpa using hz
  · intro h row _
    rw [normalizedLocalConstraintAt_eq_normalize_localConstraintAt, h, map_zero, coeff_zero]

/-- Full module constraints recover the scalar matrix on certified source support. -/
theorem fullFrame_matrix_kernel (D d m J A B : ℕ) (received : List (F × F)) (w : ℕ → F)
    (hQ : ∀ u ∈ (InterpolationPointBlockMachine.sourceCombination d
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w).support,
      totalJetDegree u ≤ B) :
    (∀ p ∈ received, ∀ row ∈ fullFrame d m B,
      coeff (index (frameQuery d row)) (normalizedLocalConstraintAt m p.1 p.2
        (InterpolationPointBlockMachine.sourceCombination d
          (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w)) = 0) ↔
    Matrix.PivotSelectionMachine.Satisfies
      (received.flatMap (ReceivedInterpolationMatrixMachine.pointRowsWithBudget D d m J A)) w := by
  rw [ReceivedInterpolationMatrixMachine.matrixWithBudget_kernel_iff]
  exact forall₂_congr (fun p _ => fullFrame_kernel m B p.1 p.2 _ hQ)

end
end ReedSolomon.HiddenDerivative.InterpolationModule
