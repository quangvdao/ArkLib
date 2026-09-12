/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ChartData
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectSelection
public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative

/-!
# Direct Jacobians of stored fast Taylor charts

This module connects the executed `FastTaylor.ChartData.agreement` rows to the direct all-subsets
selection theorem.  Its Jacobian entries are evaluations of the computable formal partial
derivatives of the stored polynomials.  Chart construction, validity, and global coverage remain
separate obligations.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian

open CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.HiddenDerivative.SquareSystems
open scoped BigOperators

variable {E L : Type*} [Field E] [BEq E] [LawfulBEq E] [Field L]

/-- The formal differential obtained by executing the stored partial derivatives and evaluating
them after the supplied coefficient embedding. -/
def evaluatedDifferential {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p : CMvPolynomial m E) : (Fin m → L) →ₗ[L] L where
  toFun direction :=
    ∑ i, direction i * CMvPolynomial.eval₂ base point (CMvPolynomial.partialDerivative i p)
  map_add' direction direction' := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' scalar direction := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

omit [BEq E] [LawfulBEq E] in
@[simp] theorem eval₂_ringHom_id {m : ℕ} (point : Fin m → E)
    (p : CMvPolynomial m E) :
    CMvPolynomial.eval₂ (RingHom.id E) point p = CMvPolynomial.eval point p := rfl

theorem evaluatedDifferential_apply {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p : CMvPolynomial m E) (direction : Fin m → L) :
    evaluatedDifferential base point p direction =
      ∑ i, direction i *
        CMvPolynomial.eval₂ base point (CMvPolynomial.partialDerivative i p) := rfl

theorem evaluatedDifferential_single {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p : CMvPolynomial m E) (column : Fin m) :
    evaluatedDifferential base point p (Pi.single column 1) =
      CMvPolynomial.eval₂ base point (CMvPolynomial.partialDerivative column p) := by
  classical
  simp [evaluatedDifferential_apply, Pi.single_apply]

/-- The executed Jacobian matrix of a square stored system. -/
def evaluatedJacobian {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (system : Fin m → CMvPolynomial m E) : Matrix (Fin m) (Fin m) L :=
  fun row column ↦
    CMvPolynomial.eval₂ base point (CMvPolynomial.partialDerivative column (system row))

/-- The row action of the executed Jacobian. -/
def evaluatedJacobianMap {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (system : Fin m → CMvPolynomial m E) : (Fin m → L) →ₗ[L] (Fin m → L) :=
  LinearMap.pi fun row ↦ evaluatedDifferential base point (system row)

@[simp]
theorem evaluatedJacobianMap_apply {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (system : Fin m → CMvPolynomial m E) (direction : Fin m → L) (row : Fin m) :
    evaluatedJacobianMap base point system direction row =
      ∑ column, evaluatedJacobian base point system row column * direction column := by
  change (∑ column, direction column * CMvPolynomial.eval₂ base point
    (CMvPolynomial.partialDerivative column (system row))) = _
  simp only [evaluatedJacobian]
  apply Finset.sum_congr rfl
  intro column _
  ring

private theorem partialDerivative_add {m : ℕ} (i : Fin m) (p q : CMvPolynomial m E) :
    CMvPolynomial.partialDerivative i (p + q) =
      CMvPolynomial.partialDerivative i p + CMvPolynomial.partialDerivative i q := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_add,
    _root_.map_add (MvPolynomial.pderiv i), CPoly.map_add,
    CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]

private theorem partialDerivative_sub {m : ℕ} (i : Fin m) (p q : CMvPolynomial m E) :
    CMvPolynomial.partialDerivative i (p - q) =
      CMvPolynomial.partialDerivative i p - CMvPolynomial.partialDerivative i q := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_sub', (MvPolynomial.pderiv i).map_sub,
    CMvPolynomial.fromCMvPolynomial_sub',
    CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]

private theorem partialDerivative_C {m : ℕ} (i : Fin m) (a : E) :
    CMvPolynomial.partialDerivative i (CMvPolynomial.C a) = 0 := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.pderiv_C]
  exact CPoly.map_zero.symm

private theorem partialDerivative_zero {m : ℕ} (i : Fin m) :
    CMvPolynomial.partialDerivative i (0 : CMvPolynomial m E) = 0 := by
  apply CPoly.fromCMvPolynomial_injective
  simp [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_zero]

private theorem partialDerivative_X {m : ℕ} (i j : Fin m) :
    CMvPolynomial.partialDerivative i (CMvPolynomial.X j : CMvPolynomial m E) =
      (CMvPolynomial.C (if i = j then 1 else 0) : CMvPolynomial m E) := by
  classical
  apply CPoly.fromCMvPolynomial_injective
  simp [CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_X, CMvPolynomial.fromCMvPolynomial_C,
    MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

private theorem partialDerivative_one {m : ℕ} (i : Fin m) :
    CMvPolynomial.partialDerivative i (1 : CMvPolynomial m E) = 0 := by
  apply CPoly.fromCMvPolynomial_injective
  simp [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_zero]

private theorem partialDerivative_mul {m : ℕ} (i : Fin m) (p q : CMvPolynomial m E) :
    CMvPolynomial.partialDerivative i (p * q) =
      CMvPolynomial.partialDerivative i p * q + p * CMvPolynomial.partialDerivative i q := by
  apply CPoly.fromCMvPolynomial_injective
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative, CPoly.map_mul,
    MvPolynomial.pderiv_mul, CPoly.map_add, CPoly.map_mul, CPoly.map_mul,
    CMvPolynomial.fromCMvPolynomial_partialDerivative,
    CMvPolynomial.fromCMvPolynomial_partialDerivative]

private theorem eval₂_C {m : ℕ} (base : E →+* L) (point : Fin m → L) (a : E) :
    CMvPolynomial.eval₂ base point (CMvPolynomial.C a) = base a := by
  rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.eval₂_C]

theorem evaluatedDifferential_add {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p q : CMvPolynomial m E) :
    evaluatedDifferential base point (p + q) =
      evaluatedDifferential base point p + evaluatedDifferential base point q := by
  apply LinearMap.ext
  intro direction
  simp only [evaluatedDifferential_apply, LinearMap.add_apply]
  simp_rw [partialDerivative_add, ← CMvPolynomial.eval₂Hom_apply,
    _root_.map_add (CMvPolynomial.eval₂Hom base point)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem evaluatedDifferential_sub {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p q : CMvPolynomial m E) :
    evaluatedDifferential base point (p - q) =
      evaluatedDifferential base point p - evaluatedDifferential base point q := by
  apply LinearMap.ext
  intro direction
  simp only [evaluatedDifferential_apply, LinearMap.sub_apply]
  simp_rw [partialDerivative_sub, ← CMvPolynomial.eval₂Hom_apply,
    _root_.map_sub (CMvPolynomial.eval₂Hom base point)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evaluatedDifferential_C {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (a : E) : evaluatedDifferential base point (CMvPolynomial.C a) = 0 := by
  apply LinearMap.ext
  intro direction
  simp [evaluatedDifferential_apply, partialDerivative_C, ← CMvPolynomial.eval₂Hom_apply]

@[simp]
theorem evaluatedDifferential_one {m : ℕ} (base : E →+* L) (point : Fin m → L) :
    evaluatedDifferential base point (1 : CMvPolynomial m E) = 0 := by
  apply LinearMap.ext
  intro direction
  simp [evaluatedDifferential_apply, partialDerivative_one,
    ← CMvPolynomial.eval₂Hom_apply]

@[simp]
theorem evaluatedDifferential_X {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (i : Fin m) (direction : Fin m → L) :
    evaluatedDifferential base point (CMvPolynomial.X i) direction = direction i := by
  classical
  simp [evaluatedDifferential_apply, partialDerivative_X, eval₂_C, eq_comm]

theorem evaluatedDifferential_mul {m : ℕ} (base : E →+* L) (point : Fin m → L)
    (p q : CMvPolynomial m E) :
    evaluatedDifferential base point (p * q) =
      CMvPolynomial.eval₂ base point q • evaluatedDifferential base point p +
        CMvPolynomial.eval₂ base point p • evaluatedDifferential base point q := by
  apply LinearMap.ext
  intro direction
  simp only [evaluatedDifferential_apply, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  simp_rw [partialDerivative_mul, ← CMvPolynomial.eval₂Hom_apply,
    _root_.map_add (CMvPolynomial.eval₂Hom base point),
    _root_.map_mul (CMvPolynomial.eval₂Hom base point)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem evaluatedDifferential_sum {m k : ℕ} (base : E →+* L)
    (point : Fin m → L) (p : Fin k → CMvPolynomial m E) :
    evaluatedDifferential base point (∑ j : Fin k, p j) =
      ∑ j : Fin k, evaluatedDifferential base point (p j) := by
  classical
  have hsum : ∀ s : Finset (Fin k),
      evaluatedDifferential base point (∑ j ∈ s, p j) =
        ∑ j ∈ s, evaluatedDifferential base point (p j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        apply LinearMap.ext
        intro direction
        simp [evaluatedDifferential_apply, partialDerivative_zero,
          ← CMvPolynomial.eval₂Hom_apply]
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, evaluatedDifferential_add, ih]
  simpa using hsum Finset.univ

/-- Actual stored chart equations used by the direct all-subsets mode. -/
def chartAgreementRows {n r k : ℕ} (chart : ChartData E r k)
    (domain received : Fin n → E) : Fin n → CMvPolynomial (r + 1) E :=
  fun i ↦ chart.agreement (domain i) (received i)

/-- Enumerate only the chart equation and `r` actual stored agreement rows. -/
def directChartSystems [DecidableEq E] {n r k : ℕ} (chart : ChartData E r k)
    (domain received : Fin n → E) : Finset (Fin (r + 1) → CMvPolynomial (r + 1) E) :=
  directSystems r chart.equation (chartAgreementRows chart domain received)

/-- The two explicit local guards checked before claiming a simple isolated chart point. -/
inductive GuardFailure where
  | zeroSeparant
  | zeroDenominator
  deriving DecidableEq, Repr

/-- A point-specialized diagnostic for the two local chart guards. Its successful result is not a
nonsingularity certificate; unknown-point solver input must use the point-independent
`directChartSystems`. -/
def guardedDirectChartSystems [DecidableEq E] [DecidableEq L] {n r k : ℕ}
    (chart : ChartData E r k)
    (base : E →+* L) (point : Fin (r + 1) → L) (domain received : Fin n → E) :
    Except GuardFailure (Finset (Fin (r + 1) → CMvPolynomial (r + 1) E)) :=
  if CMvPolynomial.eval₂ base point chart.separant = 0 then
    .error .zeroSeparant
  else if CMvPolynomial.eval₂ base point chart.denominator = 0 then
    .error .zeroDenominator
  else
    .ok (directChartSystems chart domain received)

@[simp]
theorem guardedDirectChartSystems_zeroSeparant [DecidableEq E] [DecidableEq L] {n r k : ℕ}
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (domain received : Fin n → E)
    (hzero : CMvPolynomial.eval₂ base point chart.separant = 0) :
    guardedDirectChartSystems chart base point domain received = .error .zeroSeparant := by
  simp [guardedDirectChartSystems, hzero]

@[simp]
theorem guardedDirectChartSystems_zeroDenominator [DecidableEq E] [DecidableEq L] {n r k : ℕ}
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (domain received : Fin n → E)
    (hseparant : CMvPolynomial.eval₂ base point chart.separant ≠ 0)
    (hzero : CMvPolynomial.eval₂ base point chart.denominator = 0) :
    guardedDirectChartSystems chart base point domain received = .error .zeroDenominator := by
  simp [guardedDirectChartSystems, hseparant, hzero]

/-- Embed the supplied agreeing received positions into the evaluation field. -/
def mappedAgreeingPoints {n k : ℕ} (base : E →+* L) (domain : Fin n ↪ E)
    (positions : Fin k ↪ Fin n) : Fin k ↪ L where
  toFun i := base (domain (positions i))
  inj' := by
    intro i j hij
    exact positions.injective (domain.injective (base.injective hij))

/-- Evaluation of an actual stored agreement row vanishes from numerator/denominator values and
the corresponding scalar agreement. -/
theorem eval_chartAgreement_eq_zero {n r k : ℕ} (chart : ChartData E r k)
    (base : E →+* L) (point : Fin (r + 1) → L) (domain received : Fin n → E)
    (positions : Fin k ↪ Fin n) (coefficients : Fin k → L)
    (hnumerators : ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
      CMvPolynomial.eval₂ base point chart.denominator * coefficients j)
    (hagreements : ∀ i, (∑ j, coefficients j *
      (base (domain (positions i)) - base chart.center) ^ j.val) =
        base (received (positions i))) (i : Fin k) :
    CMvPolynomial.eval₂ base point
      (chartAgreementRows chart domain received (positions i)) = 0 := by
  rw [chartAgreementRows, chart.eval₂_agreement]
  simp_rw [hnumerators]
  have hsumfactor :
      (∑ j, CMvPolynomial.eval₂ base point chart.denominator * coefficients j *
        (base (domain (positions i)) - base chart.center) ^ j.val) -
        base (received (positions i)) * CMvPolynomial.eval₂ base point chart.denominator =
      CMvPolynomial.eval₂ base point chart.denominator *
        ((∑ j, coefficients j *
          (base (domain (positions i)) - base chart.center) ^ j.val) -
            base (received (positions i))) := by
      have hsum :
          (∑ j, CMvPolynomial.eval₂ base point chart.denominator * coefficients j *
            (base (domain (positions i)) - base chart.center) ^ j.val) =
          CMvPolynomial.eval₂ base point chart.denominator *
            (∑ j, coefficients j *
              (base (domain (positions i)) - base chart.center) ^ j.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsum]
      ring
  rw [hsumfactor, hagreements]
  ring

/-- The differential of the actual stored sum/product agreement expression. -/
theorem evaluatedDifferential_chartAgreement {r k : ℕ} (chart : ChartData E r k)
    (base : E →+* L) (point : Fin (r + 1) → L) (alpha received : E)
    (direction : Fin (r + 1) → L) :
    evaluatedDifferential base point (chart.agreement alpha received) direction =
      (∑ j, evaluatedDifferential base point (chart.numerators j) direction *
        (base alpha - base chart.center) ^ j.val) -
        base received * evaluatedDifferential base point chart.denominator direction := by
  rw [ChartData.agreement, evaluatedDifferential_sub, evaluatedDifferential_sum]
  simp_rw [evaluatedDifferential_mul, evaluatedDifferential_C]
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, eval₂_C,
    _root_.map_sub base, _root_.map_pow base, add_zero, mul_zero, zero_add]
  apply congrArg (fun value ↦ value -
    base received * evaluatedDifferential base point chart.denominator direction)
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual agreement differential is the common-denominator multiple of coefficient
evaluation.  This is derived row by row from the numerator/denominator differential relation;
the final agreement-differential identity is not assumed. -/
theorem evaluatedDifferential_chartAgreement_scaled {n r k : ℕ}
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (domain : Fin n ↪ E) (received : Fin n → E) (positions : Fin k ↪ Fin n)
    (coefficients : Fin k → L)
    (coefficientDirections : (Fin (r + 1) → L) →ₗ[L] (Fin k → L))
    (hnumeratorDifferentials : ∀ direction j,
      evaluatedDifferential base point (chart.numerators j) direction =
        CMvPolynomial.eval₂ base point chart.denominator * coefficientDirections direction j +
          coefficients j * evaluatedDifferential base point chart.denominator direction)
    (hagreements : ∀ i, (∑ j, coefficients j *
      (base (domain (positions i)) - base chart.center) ^ j.val) =
        base (received (positions i)))
    (direction : Fin (r + 1) → L) (i : Fin k) :
    evaluatedDifferential base point
        (chartAgreementRows chart domain received (positions i)) direction =
      CMvPolynomial.eval₂ base point chart.denominator *
        directEvaluation (base chart.center) (mappedAgreeingPoints base domain positions)
          (coefficientDirections direction) i := by
  rw [chartAgreementRows, evaluatedDifferential_chartAgreement]
  have hsum :
      (∑ j, evaluatedDifferential base point (chart.numerators j) direction *
        (base (domain (positions i)) - base chart.center) ^ j.val) =
      CMvPolynomial.eval₂ base point chart.denominator *
          (∑ j, coefficientDirections direction j *
            (base (domain (positions i)) - base chart.center) ^ j.val) +
        evaluatedDifferential base point chart.denominator direction *
          (∑ j, coefficients j *
            (base (domain (positions i)) - base chart.center) ^ j.val) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hnumeratorDifferentials]
    ring
  rw [hsum, hagreements]
  simp only [directEvaluation_apply]
  change CMvPolynomial.eval₂ base point chart.denominator *
        (∑ j, coefficientDirections direction j *
          (base (domain (positions i)) - base chart.center) ^ j.val) +
      evaluatedDifferential base point chart.denominator direction *
        base (received (positions i)) -
      base (received (positions i)) *
        evaluatedDifferential base point chart.denominator direction =
    CMvPolynomial.eval₂ base point chart.denominator *
      (∑ j, coefficientDirections direction j *
        (base (domain (positions i)) - base chart.center) ^ j.val)
  ring

/-- Strengthening of direct common-zero capture which records that every selected received label
comes from the supplied embedding of agreeing positions. -/
theorem directSystems_contains_commonZero_capture_in_range {W : Type*}
    [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    {P : Type*} [DecidableEq P] {n k r : ℕ}
    (hypersurface : P) (equations : Fin n → P) (evaluate : P → L)
    (positions : Fin k ↪ Fin n)
    (normal : W →ₗ[L] L) (pool : W →ₗ[L] (Fin n → L))
    (hdim : Module.finrank L W = r + 1) (hnormal : normal ≠ 0)
    (htangent : Function.Injective
      ((selectedCoordinateMap pool positions).comp normal.ker.subtype))
    (hzero : evaluate hypersurface = 0)
    (hagree : ∀ i, evaluate (equations (positions i)) = 0) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      (∀ i ∈ selected, i ∈ Set.range positions) ∧
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        directSystems r hypersurface equations ∧
      (∀ i, evaluate
        (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) i) = 0) ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  obtain ⟨chosen, hchosen⟩ := exists_injective_normalSelectedMap normal
    (selectedCoordinateMap pool positions) hdim hnormal htangent
  let full := chosen.trans positions
  have hfull : Function.Injective (normalSelectedMap normal pool full) := hchosen
  let rows := Finset.univ.map full
  have hcard : rows.card = r := card_map_univ_embedding full
  refine ⟨rows, hcard, ?_, squareSystemRows_mem_enumerate _ _ _ _, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, hji⟩ := Finset.mem_map.mp hi
    exact ⟨chosen j, by simpa [full] using hji⟩
  · intro i
    refine Fin.cases hzero (fun j ↦ ?_) i
    change evaluate (equations (rowSubsetEmbedding rows hcard j)) = 0
    have hmem : rowSubsetEmbedding rows hcard j ∈ rows := by
      have hm : rowSubsetEmbedding rows hcard j ∈ Set.range (rows.orderEmbOfFin hcard) :=
        ⟨j, rfl⟩
      rwa [Finset.range_orderEmbOfFin] at hm
    obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hmem
    rw [← hl]
    exact hagree (chosen l)
  · exact rowSubsetEmbedding_preserves_injective normal pool full hfull

/-- Under the explicit local chart premises, one emitted direct system consists of `r+1` actual
stored polynomial rows, vanishes at the point, and has injective evaluated Jacobian. -/
theorem directChartSystems_contains_actualJacobian {n r k : ℕ}
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (domain : Fin n ↪ E) (received : Fin n → E) (positions : Fin k ↪ Fin n)
    (coefficients : Fin k → L)
    (coefficientDirections : (Fin (r + 1) → L) →ₗ[L] (Fin k → L))
    (hequation : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hseparant : CMvPolynomial.eval₂ base point chart.separant ≠ 0)
    (hseparantDirection :
      evaluatedDifferential base point chart.equation (Pi.single (Fin.last r) 1) =
        CMvPolynomial.eval₂ base point chart.separant)
    (hdenominator : CMvPolynomial.eval₂ base point chart.denominator ≠ 0)
    (hnumerators : ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
      CMvPolynomial.eval₂ base point chart.denominator * coefficients j)
    (hnumeratorDifferentials : ∀ direction j,
      evaluatedDifferential base point (chart.numerators j) direction =
        CMvPolynomial.eval₂ base point chart.denominator * coefficientDirections direction j +
          coefficients j * evaluatedDifferential base point chart.denominator direction)
    (hretained : Function.Injective
      (coefficientDirections.comp
        (evaluatedDifferential base point chart.equation).ker.subtype))
    [DecidableEq E]
    (hagreements : ∀ i, (∑ j, coefficients j *
      (base (domain (positions i)) - base chart.center) ^ j.val) =
        base (received (positions i))) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      let system := squareSystemRows chart.equation (chartAgreementRows chart domain received)
        (rowSubsetEmbedding selected hcard)
      system ∈ directChartSystems chart domain received ∧
      (∀ row, CMvPolynomial.eval₂ base point (system row) = 0) ∧
      Function.Injective (evaluatedJacobianMap base point system) := by
  let normal := evaluatedDifferential base point chart.equation
  let pool : (Fin (r + 1) → L) →ₗ[L] (Fin n → L) :=
    LinearMap.pi fun i ↦
      evaluatedDifferential base point (chartAgreementRows chart domain received i)
  have hnormal : normal ≠ 0 := by
    intro hzero
    have hvalue := LinearMap.congr_fun hzero (Pi.single (Fin.last r) 1)
    change evaluatedDifferential base point chart.equation
        (Pi.single (Fin.last r) 1) = 0 at hvalue
    rw [hseparantDirection] at hvalue
    exact hseparant hvalue
  have hidentity : ∀ direction : normal.ker,
      selectedCoordinateMap pool positions direction =
        CMvPolynomial.eval₂ base point chart.denominator •
          directEvaluation (base chart.center) (mappedAgreeingPoints base domain positions)
            (coefficientDirections direction) := by
    intro direction
    funext i
    change evaluatedDifferential base point
        (chartAgreementRows chart domain received (positions i)) direction = _
    rw [evaluatedDifferential_chartAgreement_scaled chart base point domain received positions
      coefficients coefficientDirections hnumeratorDifferentials hagreements direction i]
    rfl
  have htangent : Function.Injective
      ((selectedCoordinateMap pool positions).comp normal.ker.subtype) :=
    tangent_agreements_injective (base chart.center)
      (mappedAgreeingPoints base domain positions) normal coefficientDirections
      (selectedCoordinateMap pool positions) (CMvPolynomial.eval₂ base point chart.denominator)
      hdenominator hretained hidentity
  have hdim : Module.finrank L (Fin (r + 1) → L) = r + 1 := by simp
  obtain ⟨selected, hcard, hmember, hzero, hinjective⟩ :=
    directSystems_contains_commonZero_capture chart.equation
      (chartAgreementRows chart domain received)
      (CMvPolynomial.eval₂ base point) positions normal pool hdim hnormal htangent hequation
      (eval_chartAgreement_eq_zero chart base point domain received positions coefficients
        hnumerators hagreements)
  refine ⟨selected, hcard, hmember, hzero, ?_⟩
  intro direction direction' hequal
  apply hinjective
  apply Prod.ext
  · have hrow := congrFun hequal 0
    exact hrow
  · funext j
    have hrow := congrFun hequal j.succ
    exact hrow

/-- The actual-Jacobian witness can be chosen entirely from the supplied agreeing-position
embedding, even though the executable family enumerates the full received-position pool. -/
theorem directChartSystems_contains_actualJacobian_in_range {n r k : ℕ}
    (chart : ChartData E r k) (base : E →+* L) (point : Fin (r + 1) → L)
    (domain : Fin n ↪ E) (received : Fin n → E) (positions : Fin k ↪ Fin n)
    (coefficients : Fin k → L)
    (coefficientDirections : (Fin (r + 1) → L) →ₗ[L] (Fin k → L))
    (hequation : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hseparant : CMvPolynomial.eval₂ base point chart.separant ≠ 0)
    (hseparantDirection :
      evaluatedDifferential base point chart.equation (Pi.single (Fin.last r) 1) =
        CMvPolynomial.eval₂ base point chart.separant)
    (hdenominator : CMvPolynomial.eval₂ base point chart.denominator ≠ 0)
    (hnumerators : ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
      CMvPolynomial.eval₂ base point chart.denominator * coefficients j)
    (hnumeratorDifferentials : ∀ direction j,
      evaluatedDifferential base point (chart.numerators j) direction =
        CMvPolynomial.eval₂ base point chart.denominator * coefficientDirections direction j +
          coefficients j * evaluatedDifferential base point chart.denominator direction)
    (hretained : Function.Injective
      (coefficientDirections.comp
        (evaluatedDifferential base point chart.equation).ker.subtype))
    [DecidableEq E]
    (hagreements : ∀ i, (∑ j, coefficients j *
      (base (domain (positions i)) - base chart.center) ^ j.val) =
        base (received (positions i))) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      (∀ i ∈ selected, i ∈ Set.range positions) ∧
      let system := squareSystemRows chart.equation (chartAgreementRows chart domain received)
        (rowSubsetEmbedding selected hcard)
      system ∈ directChartSystems chart domain received ∧
      (∀ row, CMvPolynomial.eval₂ base point (system row) = 0) ∧
      Function.Injective (evaluatedJacobianMap base point system) := by
  let normal := evaluatedDifferential base point chart.equation
  let pool : (Fin (r + 1) → L) →ₗ[L] (Fin n → L) :=
    LinearMap.pi fun i ↦
      evaluatedDifferential base point (chartAgreementRows chart domain received i)
  have hnormal : normal ≠ 0 := by
    intro hzero
    have hvalue := LinearMap.congr_fun hzero (Pi.single (Fin.last r) 1)
    change evaluatedDifferential base point chart.equation
        (Pi.single (Fin.last r) 1) = 0 at hvalue
    rw [hseparantDirection] at hvalue
    exact hseparant hvalue
  have hidentity : ∀ direction : normal.ker,
      selectedCoordinateMap pool positions direction =
        CMvPolynomial.eval₂ base point chart.denominator •
          directEvaluation (base chart.center) (mappedAgreeingPoints base domain positions)
            (coefficientDirections direction) := by
    intro direction
    funext i
    change evaluatedDifferential base point
        (chartAgreementRows chart domain received (positions i)) direction = _
    rw [evaluatedDifferential_chartAgreement_scaled chart base point domain received positions
      coefficients coefficientDirections hnumeratorDifferentials hagreements direction i]
    rfl
  have htangent : Function.Injective
      ((selectedCoordinateMap pool positions).comp normal.ker.subtype) :=
    tangent_agreements_injective (base chart.center)
      (mappedAgreeingPoints base domain positions) normal coefficientDirections
      (selectedCoordinateMap pool positions) (CMvPolynomial.eval₂ base point chart.denominator)
      hdenominator hretained hidentity
  have hdim : Module.finrank L (Fin (r + 1) → L) = r + 1 := by simp
  obtain ⟨selected, hcard, hrange, hmember, hzero, hinjective⟩ :=
    directSystems_contains_commonZero_capture_in_range chart.equation
      (chartAgreementRows chart domain received)
      (CMvPolynomial.eval₂ base point) positions normal pool hdim hnormal htangent hequation
      (eval_chartAgreement_eq_zero chart base point domain received positions coefficients
        hnumerators hagreements)
  refine ⟨selected, hcard, hrange, hmember, hzero, ?_⟩
  intro direction direction' hequal
  apply hinjective
  apply Prod.ext
  · exact congrFun hequal 0
  · funext j
    exact congrFun hequal j.succ

end ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian
