/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Materialize
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PreprocessFiber
public import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix

/-!
# First-order norm candidate assembly

These are the stable executable stages after generic component descent and multiplicity
decomposition.  They compute the determinant norms themselves, establish the positive natural
threshold before subtraction, construct the retained finite tower, run the actual D5 fiber
preprocessor, and materialize the Taylor coefficients using the common denominator inverse.

The final `firstOrderNormCandidates` composition belongs here once the concrete descended-block
and labelled-decomposition producers are integrated.  This module deliberately has no callback
or oracle standing in for either producer.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPolynomial Polynomial
open ReedSolomon.HiddenDerivative.FastTaylor
open TowerAlgebra

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- The determinant norm of one nonuniversal agreement on a descended monic component. -/
def blockNorm (fiber agreement : CPolynomial (CPolynomial E)) : CPolynomial E :=
  NormProducts.polynomialNorm fiber agreement

/-- Compute precisely the norm rows whose indices were not classified as universal. -/
def blockNorms (fiber : CPolynomial (CPolynomial E))
    (agreements : List (CPolynomial (CPolynomial E))) (universal : List ℕ) :
    List (CPolynomial E) :=
  (agreements.zipIdx.filter fun row => row.2 ∉ universal).map fun row =>
    blockNorm fiber row.1

/-- The actual all-position determinant product for one descended component. -/
def blockNormProduct (fiber : CPolynomial (CPolynomial E))
    (agreements : List (CPolynomial (CPolynomial E))) (universal : List ℕ) :
    CPolynomial E :=
  (blockNorms fiber agreements universal).prod

@[simp] theorem blockNormProduct_nil (fiber : CPolynomial (CPolynomial E))
    (universal : List ℕ) : blockNormProduct fiber [] universal = 1 := rfl

/-- Specialization of a nested polynomial at a tower point, stated in the form used by the
multiplication-matrix norm theorem. -/
theorem aeval_map_eq_evalNested {L : Type*} [Field L] (base : E →+* L) (u v : L)
    (polynomial : CPolynomial (CPolynomial E)) :
    Polynomial.aeval v (polynomial.toPoly.map
      (FirstOrderNormDecoder.D5.coefficientEval base u)) =
      TowerRepresentation.evalNested polynomial base u v := by
  rfl

/-- A vanishing agreement contributes a vanishing computed norm at the projected coordinate.
No squarefreeness or unramified-fiber premise is used. -/
theorem blockNorm_eq_zero_of_point {L : Type*} [Field L] (base : E →+* L) (u v : L)
    (fiber agreement : CPolynomial (CPolynomial E)) (hfiber : fiber.monic)
    (hpoint : TowerRepresentation.evalNested fiber base u v = 0)
    (hagreement : TowerRepresentation.evalNested agreement base u v = 0) :
    (blockNorm fiber agreement).toPoly.eval₂ base u = 0 := by
  rw [← FirstOrderNormDecoder.D5.coefficientEval_apply]
  unfold blockNorm NormProducts.polynomialNorm
  rw [CPolynomial.natDegree_toPoly]
  apply NormProducts.map_norm_eq_zero_of_point
    (FirstOrderNormDecoder.D5.coefficientEval base u) fiber agreement hfiber v
  · simpa only [aeval_map_eq_evalNested] using hpoint
  · simpa only [aeval_map_eq_evalNested] using hagreement

/-- The paper threshold for a block with `z₀` universal agreements. -/
def threshold (A : ℕ) (universal : List ℕ) : ℕ := A - universal.length

/-- The geometric universal-position bound is applied before interpreting natural subtraction. -/
theorem universal_lt_agreementThreshold {k A : ℕ} {universal : List ℕ}
    (hk : 0 < k) (huniversal : universal.length ≤ k - 1) (hkA : k ≤ A) :
    universal.length < A := by
  omega

/-- Consequently the computed norm-multiplicity threshold is positive. -/
theorem threshold_pos {k A : ℕ} {universal : List ℕ}
    (hk : 0 < k) (huniversal : universal.length ≤ k - 1) (hkA : k ≤ A) :
    0 < threshold A universal := by
  unfold threshold
  exact Nat.sub_pos_of_lt (universal_lt_agreementThreshold hk huniversal hkA)

/-- Truncated subtraction agrees with the intended exact equation on the proved domain. -/
theorem universal_add_threshold {k A : ℕ} {universal : List ℕ}
    (hk : 0 < k) (huniversal : universal.length ≤ k - 1) (hkA : k ≤ A) :
    universal.length + threshold A universal = A := by
  unfold threshold
  exact Nat.add_sub_of_le (Nat.le_of_lt (universal_lt_agreementThreshold hk huniversal hkA))

/-- The raw finite tower selected by the multiplicity threshold. -/
def retainedTower (support : CPolynomial E) (fiber : CPolynomial (CPolynomial E)) :
    TowerRepresentation (F := E) :=
  { modulus := support, fiber, coefficients := [] }

/-- The labelled decomposition supplies exactly the invariants needed to invoke the actual
finite-fiber preprocessor. -/
theorem retainedTower_preprocessable (support : CPolynomial E)
    (fiber : CPolynomial (CPolynomial E)) (hsupport : support.monic)
    (hsquarefree : Squarefree support.toPoly) (hfiber : fiber.monic) :
    Preprocessable (retainedTower support fiber) := by
  exact ⟨hsupport, hsquarefree, hfiber⟩

/-- Run `PreprocessFiber` on the retained squarefree base support. -/
def preprocessRetained (support : CPolynomial E) (fiber separant : CPolynomial (CPolynomial E))
    (hsupport : support.monic) (hsquarefree : Squarefree support.toPoly)
    (hfiber : fiber.monic) : List (TowerRepresentation (F := E)) :=
  preprocessFiber (retainedTower support fiber) separant
    (retainedTower_preprocessable support fiber hsupport hsquarefree hfiber)

/-- Materialize all `k` Taylor coefficients on every retained preprocessed tower.  A failed
denominator inversion is represented by omission here; the theorem layer below proves that no
output is malformed, while the chart regularity theorem will prove that no wanted point is lost. -/
def materializeRetained [DecidableEq E] {k : ℕ} (support : CPolynomial E)
    (fiber separant denominator : CPolynomial (CPolynomial E))
    (numerators : Fin k → CPolynomial (CPolynomial E))
    (hsupport : support.monic) (hsquarefree : Squarefree support.toPoly)
    (hfiber : fiber.monic) : List (TowerRepresentation (F := E)) :=
  (preprocessRetained support fiber separant hsupport hsquarefree hfiber).filterMap fun tower =>
    materializeCoefficients? tower denominator (List.ofFn numerators)

/-- Membership records the actual preprocessing branch and successful coefficient materializer
that produced a candidate. -/
theorem mem_materializeRetained_iff [DecidableEq E] {k : ℕ} (support : CPolynomial E)
    (fiber separant denominator : CPolynomial (CPolynomial E))
    (numerators : Fin k → CPolynomial (CPolynomial E))
    (hsupport : support.monic) (hsquarefree : Squarefree support.toPoly)
    (hfiber : fiber.monic) (out : TowerRepresentation (F := E)) :
    out ∈ materializeRetained support fiber separant denominator numerators
      hsupport hsquarefree hfiber ↔
      ∃ tower ∈ preprocessRetained support fiber separant hsupport hsquarefree hfiber,
        materializeCoefficients? tower denominator (List.ofFn numerators) = some out := by
  simp [materializeRetained]

/-- Every emitted candidate satisfies the common tower contract, including canonical reduction
of the base, fiber and all `k` materialized message coefficients. -/
theorem materializeRetained_wellFormed [DecidableEq E]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    {k : ℕ} (support : CPolynomial E)
    (fiber separant denominator : CPolynomial (CPolynomial E))
    (numerators : Fin k → CPolynomial (CPolynomial E))
    (hsupport : support.monic) (hsquarefree : Squarefree support.toPoly)
    (hfiber : fiber.monic) (hdegree : fiber.natDegree < p)
    (out : TowerRepresentation (F := E))
    (hout : out ∈ materializeRetained support fiber separant denominator numerators
      hsupport hsquarefree hfiber) : out.WellFormed k := by
  obtain ⟨tower, htower, hout⟩ := (mem_materializeRetained_iff support fiber separant denominator
    numerators hsupport hsquarefree hfiber out).mp hout
  have hpre : tower.WellFormed 0 := by
    exact preprocessFiber_wellFormed p (retainedTower support fiber) separant
      (retainedTower_preprocessable support fiber hsupport hsquarefree hfiber) hdegree tower htower
  have hwell := materializeCoefficients?_wellFormed tower hpre denominator
    (List.ofFn numerators) out hout
  simpa using hwell

/-- Materialization changes only the coefficient payload, so it preserves every geometric
tower point exactly. -/
theorem materializeCoefficients?_point_iff [DecidableEq E]
    (tower : TowerRepresentation (F := E))
    (denominator : CPolynomial (CPolynomial E))
    (numerators : List (CPolynomial (CPolynomial E)))
    (out : TowerRepresentation (F := E))
    (hout : materializeCoefficients? tower denominator numerators = some out)
    {L : Type*} [Field L] (base : E →+* L) (u v : L) :
    out.Point base u v ↔ tower.Point base u v := by
  unfold materializeCoefficients? at hout
  cases hinverse : inverseElimination? tower.modulus tower.fiber denominator with
  | none => simp [hinverse] at hout
  | some inverse =>
      simp only [hinverse, Option.some.injEq] at hout
      subst out
      rfl

/-- A retained root with nonzero separant survives the actual D5 preprocessing and actual
denominator inversion.  The resulting specialization is the chart's rational coefficient list.
This is the candidate-membership bridge consumed by the per-chart coverage theorem. -/
theorem materializeRetained_point_complete [DecidableEq E]
    (p : ℕ) [Fact p.Prime] [CharP E p]
    {k : ℕ} (support : CPolynomial E)
    (fiber separant denominator : CPolynomial (CPolynomial E))
    (numerators : Fin k → CPolynomial (CPolynomial E))
    (hsupport : support.monic) (hsquarefree : Squarefree support.toPoly)
    (hfiber : fiber.monic) (hdegree : fiber.natDegree < p)
    (hdenominator : ∀ u v : AlgebraicClosure E,
      (retainedTower support fiber).Point (algebraMap E (AlgebraicClosure E)) u v →
      TowerRepresentation.evalNested separant
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0 →
      TowerRepresentation.evalNested denominator
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0)
    {L : Type} [Field L] (base : E →+* L) (u v : L)
    (hpoint : (retainedTower support fiber).Point base u v)
    (hseparant : TowerRepresentation.evalNested separant base u v ≠ 0) :
    ∃ out ∈ materializeRetained support fiber separant denominator numerators
        hsupport hsquarefree hfiber,
      out.Point base u v ∧
        out.specialize base u v =
          Polynomial.JetHornerMachine.coefficientPolynomial
            ((List.ofFn numerators).map fun numerator =>
              TowerRepresentation.evalNested numerator base u v /
                TowerRepresentation.evalNested denominator base u v) := by
  let input := retainedTower support fiber
  let hinput : Preprocessable input :=
    retainedTower_preprocessable support fiber hsupport hsquarefree hfiber
  obtain ⟨tower, htower, htowerPoint⟩ :=
    preprocessFiber_point_complete p input separant hinput hdegree base u v hpoint hseparant
  have htowerWell : tower.WellFormed 0 :=
    preprocessFiber_wellFormed p input separant hinput hdegree tower htower
  have hnonzero : ∀ x y : AlgebraicClosure E,
      tower.Point (algebraMap E (AlgebraicClosure E)) x y →
        TowerRepresentation.evalNested denominator
          (algebraMap E (AlgebraicClosure E)) x y ≠ 0 := by
    intro x y hxy
    have hretained := preprocessFiber_point_sound p input separant hinput hdegree tower htower
      (algebraMap E (AlgebraicClosure E)) x y hxy
    exact hdenominator x y hretained.1 hretained.2
  obtain ⟨out, hout, _houtWell⟩ := materializeCoefficients?_exists_of_geometric_nonvanishing
    tower htowerWell denominator (List.ofFn numerators) hnonzero
  refine ⟨out, (mem_materializeRetained_iff support fiber separant denominator numerators
    hsupport hsquarefree hfiber out).mpr ⟨tower, htower, hout⟩, ?_, ?_⟩
  · exact (materializeCoefficients?_point_iff tower denominator (List.ofFn numerators)
      out hout base u v).mpr htowerPoint
  · exact materializeCoefficients?_specialize tower htowerWell denominator
      (List.ofFn numerators) out hout base u v htowerPoint

end ReedSolomon.ListDecoding.FirstOrderNormProducer
