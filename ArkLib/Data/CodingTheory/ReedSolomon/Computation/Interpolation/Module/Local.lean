/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Support
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Matrix.Semantics

/-! # Local Jordan action for interpolation columns

The executable coefficient action is multiplication by `a + T`, followed by the existing
low-contact truncation. Zero-X columns are materialized by the existing checked scalar program.
No minimal-basis algorithm or fast-interpolation complexity claim is supplied here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationModule

open MvPolynomial
open PolynomialDifferential

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Execute the existing local column producer only at X exponent zero. -/
def zeroColumn (d m : ℕ) (a y : F) (b : JetMonomial) :=
  InterpolationPointBlockMachine.makeColumn d m a y (b.vector 0)

/-- Coefficient state for the local quotient; only queried finite coordinates need be stored. -/
abbrev Coordinates (F : Type*) (d : ℕ) := (LocalVariable d → ℕ) → F

/-- Truncated Jordan action on coefficients: diagonal `a` and a single T shift. -/
def jordan (m : ℕ) (a : F) (v : Coordinates F d) : Coordinates F d := fun e =>
  if e none + d * e (some none) < m then
    a * v e + if e (localT d) = 0 then 0 else v (fun j => if j = none then e j - 1 else e j)
  else 0

/-- Repeated action, without re-running a scalar column producer at each X exponent. -/
def powers (m : ℕ) (a : F) (v : Coordinates F d) : ℕ → Coordinates F d
  | 0 => v
  | n + 1 => jordan m a (powers m a v n)

/-- Read a coefficient from an actual dense local column, adding duplicate terms. -/
def denseCoordinates (ts : InterpolationPointBlockMachine.DenseColumn F) : Coordinates F d :=
  fun e => (LocalColumnRewriteMachine.lookup
    (e none :: e (some none) :: List.ofFn (fun j : Fin d => e (some (some j)))) ts).1

/-- Evaluate a finite module relation from supplied materialized seed columns and X exponents. -/
def evaluate (m : ℕ) (a : F) :
    List (ℕ × InterpolationPointBlockMachine.DenseColumn F) → (ℕ → F) → Coordinates F d
  | [], _ => fun _ => 0
  | (x, seed) :: rest, w => fun e =>
      w 0 * powers m a (denseCoordinates seed) x e +
        evaluate m a rest (fun i => w (i + 1)) e

noncomputable section

/-- Proof-only conversion from executable local coordinates to polynomial exponents. -/
def index (e : LocalVariable d → ℕ) : LocalVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm e

@[simp]
theorem index_apply (e : LocalVariable d → ℕ) (j : LocalVariable d) : index e j = e j := by
  simp [index]

/-- Dense storage and executable local coordinate queries have the same coefficient meaning. -/
theorem denseCoordinates_coeff (ts : InterpolationPointBlockMachine.DenseColumn F)
    (ht : ∀ t ∈ ts, t.2.length = d + 2) :
    denseCoordinates ts = fun e => coeff (index e)
      (LocalColumnRewriteMachine.denseRepresented d ts) := by
  funext e
  let q : LocalColumnRewriteMachine.Term F :=
    ⟨0, e none, e (some none), List.ofFn (fun j : Fin d => e (some (some j)))⟩
  have he : LocalColumnRewriteMachine.exponent d q = index e := by
    ext j
    rcases j with (_ | (_ | j)) <;>
      simp [q, LocalColumnRewriteMachine.exponent, LocalColumnRewriteMachine.higher,
        LocalColumnTranslationMachine.exponent, LocalColumnTranslationMachine.higherExponent,
        Finsupp.single_apply, localT, localU, localAux, localY, List.getD_eq_getElem?_getD]
  have h := LocalColumnRewriteMachine.coordinate_coeff q (by simp [q]) ts ht
  simpa [denseCoordinates, LocalColumnRewriteMachine.lookup_result, q, he] using h

private theorem index_pred (e : LocalVariable d → ℕ) :
    index (fun j => if j = none then e j - 1 else e j) =
      index e - Finsupp.single (localT d) 1 := by
  ext j
  by_cases h : j = none <;> simp [h, localT]

private theorem contact_formula (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = e none + d * e (some none) := by
  simp [localContactOrder, Finsupp.weight_apply, Finsupp.sum_fintype,
    Fintype.sum_option, localContactWeight, mul_comm]

private theorem contact_sub_le (e : LocalVariable d →₀ ℕ) :
    localContactOrder d (e - Finsupp.single (localT d) 1) ≤ localContactOrder d e := by
  simp only [contact_formula, Finsupp.coe_tsub, Pi.sub_apply]
  simp [localT] at *

/-- Jordan action is exactly multiplication by `a + T` and contact projection. -/
theorem jordan_coeff (m : ℕ) (a : F) (P : LocalPolynomial F d) :
    jordan m a (fun e => coeff (index e) P) =
      fun e => coeff (index e) (projectLowContact m ((C a + X (localT d)) * P)) := by
  funext e
  simp only [jordan]
  have hc := contact_formula (index e)
  simp only [index_apply] at hc
  by_cases h : localContactOrder d (index e) < m <;>
    simp [← hc, h, index_pred, projectLowContact, coeff_filterLocalMonomials, add_mul,
    coeff_C_mul, coeff_X_mul', Finsupp.mem_support_iff]

private theorem jordan_project (m : ℕ) (a : F) (P : LocalPolynomial F d) :
    jordan m a (fun e => coeff (index e) (projectLowContact m P)) =
      jordan m a (fun e => coeff (index e) P) := by
  funext e
  have hc := contact_formula (index e)
  simp only [index_apply] at hc
  by_cases h : localContactOrder d (index e) < m
  · have hs := (contact_sub_le (index e)).trans_lt h
    simp only [jordan, ← hc, h, if_true, index_pred]
    simp [projectLowContact, coeff_filterLocalMonomials, h, hs]
  · simp only [jordan, ← hc, h, if_false]

/-- Local constraints intertwine global X multiplication with the truncated Jordan action. -/
theorem jordan_localConstraint (m : ℕ) (a y : F) (Q : DifferentialPolynomial F d) :
    jordan m a (fun e => coeff (index e) (localConstraintAt m a y Q)) =
      fun e => coeff (index e) (localConstraintAt m a y (X none * Q)) := by
  change jordan m a (fun e => coeff (index e)
    (projectLowContact m (unscaledLocalSubstitution d a y Q))) = _
  rw [jordan_project, jordan_coeff]
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, unscaledLocalSubstitution_X]

/-- Repeated local action reconstructs every scalar X column from its zero-X column. -/
theorem powers_localConstraint (m : ℕ) (a y : F) (b : JetMonomial) (x : ℕ) :
    powers m a (fun e => coeff (index e)
      (localConstraintAt m a y (InterpolationPointBlockMachine.sourceValue d (b.vector 0)))) x =
      fun e => coeff (index e)
        (localConstraintAt m a y (InterpolationPointBlockMachine.sourceValue d (b.vector x))) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [powers, ih, jordan_localConstraint]
    simp [JetMonomial.vector, InterpolationPointBlockMachine.sourceValue, sourceMonomial,
      pow_succ, mul_assoc, mul_left_comm]

/-- The base column is supplied by the actual materializing scalar producer. -/
theorem zeroColumn_refines (m : ℕ) (a y : F) (b : JetMonomial)
    (hb : b.higher.length = d) :
    ∃ c, zeroColumn d m a y b =
      (some (InterpolationPointBlockMachine.columnValue d m a y (b.vector 0)), c) ∧
      LocalColumnRewriteMachine.denseRepresented d
        (InterpolationPointBlockMachine.columnValue d m a y (b.vector 0)) =
      localConstraintAt m a y (InterpolationPointBlockMachine.sourceValue d (b.vector 0)) := by
  obtain ⟨c, hc, hp, _⟩ :=
    InterpolationPointBlockMachine.makeColumn_refines m a y 0 b.zeroth b.higher hb
  exact ⟨c, hc, hp⟩

/-- Executing Jordan powers on the materialized zero-X column recovers the scalar producer. -/
theorem powers_denseColumn (m : ℕ) (a y : F) (b : JetMonomial)
    (hb : b.higher.length = d) (x : ℕ) :
    powers (d := d) m a (denseCoordinates
      (InterpolationPointBlockMachine.columnValue d m a y (b.vector 0))) x =
    denseCoordinates (InterpolationPointBlockMachine.columnValue d m a y (b.vector x)) := by
  obtain ⟨_, _, hp0, hw0, _⟩ :=
    InterpolationPointBlockMachine.makeColumn_refines m a y 0 b.zeroth b.higher hb
  obtain ⟨_, _, hpx, hwx, _⟩ :=
    InterpolationPointBlockMachine.makeColumn_refines m a y x b.zeroth b.higher hb
  simp only [JetMonomial.vector]
  rw [denseCoordinates_coeff (d := d) _ hw0, denseCoordinates_coeff (d := d) _ hwx,
    hp0, hpx]
  exact powers_localConstraint m a y b x

/-- Module evaluation in the scalar support order; each column uses only its zero-X seed. -/
def relation (m : ℕ) (a y : F) : List (List ℕ) → (ℕ → F) → Coordinates F d
  | [], _ => 0
  | v :: vs, w => fun e =>
      w 0 * (match v with
        | x :: b :: higher => powers m a (fun e => coeff (index e)
            (localConstraintAt m a y (InterpolationPointBlockMachine.sourceValue d
              (JetMonomial.vector ⟨b, higher⟩ 0)))) x e
        | _ => 0) + relation m a y vs (fun i => w (i + 1)) e

/-- Module-relation evaluation equals the existing local polynomial constraints. -/
theorem relation_eq (m : ℕ) (a y : F) (vs : List (List ℕ)) (w : ℕ → F) :
    relation (d := d) m a y vs w = fun e => coeff (index e)
      (localConstraintAt m a y (InterpolationPointBlockMachine.sourceCombination d vs w)) := by
  induction vs generalizing w with
  | nil => funext e; simp [relation, InterpolationPointBlockMachine.sourceCombination,
      InterpolationPointBlockMachine.combine]
  | cons v vs ih =>
    funext e
    simp only [relation, InterpolationPointBlockMachine.sourceCombination, List.map_cons,
      InterpolationPointBlockMachine.combine, map_add, map_smul, coeff_add, coeff_smul,
      smul_eq_mul]
    rw [ih]
    congr 1
    cases v with
    | nil => simp [InterpolationPointBlockMachine.sourceValue]
    | cons x v =>
      cases v with
      | nil => simp [InterpolationPointBlockMachine.sourceValue]
      | cons b higher =>
        simp only [powers_localConstraint]
        rfl

/-- Executable evaluation of actual zero-X producers has the module relation semantics. -/
theorem evaluate_eq_relation (m : ℕ) (a y : F) (bs : List (JetMonomial × ℕ))
    (hb : ∀ b ∈ bs, b.1.higher.length = d) (w : ℕ → F) :
    evaluate (d := d) m a (bs.map (fun b => (b.2,
      InterpolationPointBlockMachine.columnValue d m a y (b.1.vector 0)))) w =
    relation m a y (bs.map (fun b => b.1.vector b.2)) w := by
  induction bs generalizing w with
  | nil => rfl
  | cons b bs ih =>
    have hh := hb b (by simp)
    have ht := ih (fun b h => hb b (by simp [h])) (fun i => w (i + 1))
    obtain ⟨_, _, hp, hw, _⟩ := InterpolationPointBlockMachine.makeColumn_refines
      m a y 0 b.1.zeroth b.1.higher hh
    funext e
    simp only [List.map_cons, evaluate, JetMonomial.vector, relation]
    simp only [JetMonomial.vector] at ht
    rw [denseCoordinates_coeff (d := d) _ hw, hp, ht]

/-- The executed finite relation has exactly the existing local-constraint evaluation. -/
theorem evaluate_eq_localConstraint (m : ℕ) (a y : F) (bs : List (JetMonomial × ℕ))
    (hb : ∀ b ∈ bs, b.1.higher.length = d) (w : ℕ → F) :
    evaluate (d := d) m a (bs.map (fun b => (b.2,
      InterpolationPointBlockMachine.columnValue d m a y (b.1.vector 0)))) w =
    fun e => coeff (index e) (localConstraintAt m a y
      (InterpolationPointBlockMachine.sourceCombination d
        (bs.map (fun b => b.1.vector b.2)) w)) :=
  (evaluate_eq_relation m a y bs hb w).trans (relation_eq m a y _ w)

/-- Vanishing module relations impose exactly the already checked scalar matrix kernel. -/
theorem relation_zero_iff_matrix (D d m J A : ℕ) (received : List (F × F)) (w : ℕ → F) :
    (∀ p ∈ received, relation (d := d) m p.1 p.2
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w = 0) ↔
    Matrix.PivotSelectionMachine.Satisfies
      (received.flatMap (ReceivedInterpolationMatrixMachine.pointRowsWithBudget D d m J A)) w := by
  rw [ReceivedInterpolationMatrixMachine.matrixWithBudget_kernel_iff]
  apply forall₂_congr
  intro p _
  rw [relation_eq]
  constructor
  · intro h
    apply MvPolynomial.ext
    intro e
    have he := congrFun h (fun j => e j)
    have hi : index (fun j => e j) = e := by ext j; simp
    simpa [hi] using he
  · intro h
    funext e
    simp [h]

end
end ReedSolomon.HiddenDerivative.InterpolationModule
