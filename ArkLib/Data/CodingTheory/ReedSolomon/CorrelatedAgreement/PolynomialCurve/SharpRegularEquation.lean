/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.RegularEquation
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.SharpTupleCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorBidegree
import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.BidegreeExcluded

/-!
# Sharp regular polynomial-curve bounds in orders zero and one

For a source equation of order zero or one, put

```text
a = ell + tau*h,
b = 1 + tau*(v-1),
```

Write `lambda1 = (n-L+1)/(A-L+1)`, `lambda2 = (n-k+1)/(L-k+1)`, and let
`eta` be the order-one joint factor. The two formulas exposed here are

```text
order zero: (h*b + v*a) * lambda1 + ell*(n-L)*v,
order one:  (h*b^2 + 2*v*a*b) * lambda1*eta + ell*(n-L)*v*(b*lambda2).
```

The temporary default `eta = lambda1` recovers the existing source-incidence theorem. The
dimension-sensitive theorem instantiates the independent direct ratio
`eta = (n-k+1)/(A-k+1)`.

The initial equation, separant, high Taylor cuts, and received-word cuts have the stated
bidegrees at every derivative order. The sharp degree specialization and exceptional-set
theorems below currently cover orders zero and one. The bidegree presentation applies sharp
incidence outside an excluded locus; its terminal condition is the existing symbolic-prime graph
recognition theorem.  The remaining graph locus is handled by sharp tuple counting, and the
exact polynomial root theorem contributes `ell*(n-L)` per retained tuple.  A common regular
Taylor center lifts the fixed-center result to every finite family of bad challenges, from
which the finite exceptional set is constructed.

The public results assume an algebraically closed extension field and the nonvanishing binomial
coefficients required by Taylor reconstruction.  Their quantifiers range over every received
polynomial curve and every regular close solution.  No whole-protocol accounting is performed
here.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 5.6, Theorem 5.14 and Corollary 5.15.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

private theorem sharp_source_initial_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceInitialEquation center Q) =
      aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceInitialEquation, aeval_optionEquivRight_symm,
    map_initialJetEquationOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem sharp_source_separant_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceSeparant, aeval_optionEquivRight_symm,
    map_initialJetSeparantOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem sharp_source_numerator_eval {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (K : ℕ) (l : Fin K)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceNumerator center Q K l) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l) := by
  rw [symbolicSourceNumerator, aeval_optionEquivRight_symm, eval_commonTaylorNumeratorOver]
  rfl

private theorem sharp_source_numerator_eval_of_exponent {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (l : Fin K)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        ((optionEquivRight E _).symm
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l (τ := τ)) := by
  rw [aeval_optionEquivRight_symm]
  simp only [Option.elim_none, Option.elim_some]
  rw [eval_commonTaylorNumeratorOver center z Q K l τ]

private theorem sharp_source_curveAgreement_eval_of_exponent {r : ℕ} (center z alpha : E)
    (values : Fin (ℓ + 1) → E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        (symbolicSourceCurveAgreement_of_exponent center Q K τ alpha values) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha
        (∑ t, z ^ t.val * values t) (τ := τ)) := by
  rw [symbolicSourceCurveAgreement_of_exponent, aeval_optionEquivRight_symm]
  simp only [Option.elim_none, Option.elim_some]
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ]
  have hc : φ (Polynomial.C center) = center := by simp [φ]
  have hx : φ (Polynomial.C alpha) = alpha := by simp [φ]
  have hy : φ (powerBatchedCoordinate values) = ∑ t, z ^ t.val * values t := by
    change (powerBatchedCoordinate values).eval z = _
    exact powerBatchedCoordinate_eval values z
  have he := map_taylorAgreementEquationOver_eq φ
    (Polynomial.C center) Q K (Polynomial.C alpha) (powerBatchedCoordinate values) τ
  rw [hφ, hc, hx] at he
  exact congrArg (MvPolynomial.aeval jet) (he.trans (congrArg
    (fun received ↦ taylorAgreementEquation center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha received (τ := τ))
    hy))

private theorem sharp_source_curveAgreement_eval {r : ℕ} (center z alpha : E)
    (values : Fin (ℓ + 1) → E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet)
        (symbolicSourceCurveAgreement center Q K alpha values) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha
        (∑ t, z ^ t.val * values t)) := by
  change aeval (fun i ↦ i.elim z jet)
      (symbolicSourceCurveAgreement_of_exponent center Q K (2 * K) alpha values) = _
  exact sharp_source_curveAgreement_eval_of_exponent center z alpha values Q K (2 * K) jet

private theorem span_singleton_ne_top_of_aeval_eq_zero {σ : Type*}
    (g : MvPolynomial σ E) (x : σ → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial σ E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

private theorem sharp_source_initial_ne_zero_of_regular {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_separant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquationOver (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- Challenge side of the sharp source-cut rectangle at common denominator exponent `τ`. -/
def sourceCurveCutChallengeDegree (ℓ K h : ℕ) (τ : ℕ := 2 * K) : ℕ := ℓ + τ * h

/-- Total-jet side of the sharp source-cut rectangle at common denominator exponent `τ`. -/
def sourceCurveCutJetDegree (K v : ℕ) (τ : ℕ := 2 * K) : ℕ := 1 + τ * (v - 1)

/-- Mixed affine degree of the pulled-back first-order initial hypersurface. -/
def sourceCurveInitialMixedDegreeTwo (ℓ K v h : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  h * sourceCurveCutJetDegree K v (τ := τ) ^ 2 +
    2 * v * sourceCurveCutChallengeDegree ℓ K h (τ := τ) *
      sourceCurveCutJetDegree K v (τ := τ)

/-- Mixed affine degree of the pulled-back order-zero initial hypersurface. -/
def sourceCurveInitialMixedDegreeOne (ℓ K v h : ℕ) (τ : ℕ := 2 * K) : ℕ :=
  h * sourceCurveCutJetDegree K v (τ := τ) +
    v * sourceCurveCutChallengeDegree ℓ K h (τ := τ)

/-- Sharp regular order-zero MCA budget: mixed source incidence plus exact tuple roots. -/
def regularSymbolicCurveMCASharpBoundOne
    (n ℓ K _k L A v h : ℕ) (τ : ℕ := 2 * K) : ℚ :=
  (sourceCurveInitialMixedDegreeOne ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ)

/-- Sharp regular first-order MCA budget: mixed source incidence plus exact tuple roots. -/
def regularSymbolicCurveMCASharpBoundTwo
    (n ℓ K k L A v h : ℕ) (τ : ℕ := 2 * K)
    (η : ℚ := ((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) : ℚ :=
  (sourceCurveInitialMixedDegreeTwo ℓ K v h (τ := τ) : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) * η +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      ((((n - k + 1) * sourceCurveCutJetDegree K v (τ := τ) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))

/-- The symbolic initial equation has its native `(h,v)` bidegree. -/
theorem symbolicSourceInitialEquation_mem_restrictBidegree
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (h v : ℕ)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceInitialEquation center Q ∈
      restrictBidegree (F := E) (σ := Fin (r + 1)) h v := by
  simpa only [symbolicSourceInitialEquation, flattenChallenge] using
    initialJetEquationOver_mem_restrictBidegree center Q h v hheight hjet

/-- The initial equation also fits the common source-cut rectangle. -/
theorem symbolicSourceInitialEquation_mem_sourceCurveCutBidegree
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v : ℕ)
    (hK : 0 < K) (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceInitialEquation center Q ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
      (sourceCurveCutChallengeDegree ℓ K h) (sourceCurveCutJetDegree K v) := by
  apply source_mem_restrictBidegree_mono
    (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
  · simp only [sourceCurveCutChallengeDegree]
    nlinarith
  · simp only [sourceCurveCutJetDegree]
    have hm : v - 1 ≤ 2 * K * (v - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The initial equation fits the source-cut rectangle for every positive common exponent. -/
theorem symbolicSourceInitialEquation_mem_sourceCurveCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v τ : ℕ)
    (hτpos : 0 < τ) (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceInitialEquation center Q ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
      (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
      (sourceCurveCutJetDegree K v (τ := τ)) := by
  apply source_mem_restrictBidegree_mono
    (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
  · simp only [sourceCurveCutChallengeDegree]
    have hh : h ≤ τ * h := Nat.le_mul_of_pos_left h hτpos
    omega
  · simp only [sourceCurveCutJetDegree]
    have hm : v - 1 ≤ τ * (v - 1) := Nat.le_mul_of_pos_left _ hτpos
    omega

/-- The symbolic separant fits the common source-cut rectangle. -/
theorem symbolicSourceSeparant_mem_sourceCurveCutBidegree
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v : ℕ)
    (hK : 0 < K) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceSeparant center Q ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
      (sourceCurveCutChallengeDegree ℓ K h) (sourceCurveCutJetDegree K v) := by
  have hs := initialJetSeparantOver_mem_restrictBidegree center Q h v hheight hjet
  apply source_mem_restrictBidegree_mono hs
  · simp only [sourceCurveCutChallengeDegree]
    nlinarith
  · simp only [sourceCurveCutJetDegree]
    have hm : v - 1 ≤ 2 * K * (v - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The symbolic separant fits the source-cut rectangle for every positive common exponent. -/
theorem symbolicSourceSeparant_mem_sourceCurveCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v τ : ℕ)
    (hτpos : 0 < τ) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceSeparant center Q ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
      (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
      (sourceCurveCutJetDegree K v (τ := τ)) := by
  have hs := initialJetSeparantOver_mem_restrictBidegree center Q h v hheight hjet
  apply source_mem_restrictBidegree_mono hs
  · simp only [sourceCurveCutChallengeDegree]
    have hh : h ≤ τ * h := Nat.le_mul_of_pos_left h hτpos
    omega
  · simp only [sourceCurveCutJetDegree]
    have hm : v - 1 ≤ τ * (v - 1) := Nat.le_mul_of_pos_left _ hτpos
    omega

/-- Every high Taylor equation fits the common source-cut rectangle. -/
theorem symbolicSourceNumerator_mem_sourceCurveCutBidegree
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v : ℕ)
    (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    symbolicSourceNumerator center Q K l ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
      (sourceCurveCutChallengeDegree ℓ K h) (sourceCurveCutJetDegree K v) := by
  have hl := commonTaylorNumeratorOver_mem_restrictBidegree
    center Q h v K hv hheight hjet l
  simpa only [symbolicSourceNumerator, flattenChallenge,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree] using
      source_mem_restrictBidegree_mono hl (Nat.le_add_left _ _) (le_refl _)

/-- A high numerator at a sufficient common exponent fits its exact source-cut rectangle. -/
theorem commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K h v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hv : 0 < v)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    (optionEquivRight E _).symm
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ)) ∈
      restrictBidegree (F := E) (σ := Fin (r + 1))
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) := by
  have hl := commonTaylorNumeratorOver_mem_restrictBidegree_of_exponent
    center Q h v K τ hτ hv hheight hjet l
  simpa only [flattenChallenge, sourceCurveCutChallengeDegree,
    sourceCurveCutJetDegree] using
      source_mem_restrictBidegree_mono hl (Nat.le_add_left _ _) (le_refl _)

/-- Every explicit high cut at exponent `τ` fits the same exact source rectangle. -/
theorem sourceCurveHighCuts_mem_sourceCurveCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r) (ℓ K k h v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hv : 0 < v)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ∀ f ∈ sourceCurveHighCuts_of_exponent center Q K k τ,
      f ∈ restrictBidegree (F := E) (σ := Fin (r + 1))
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) := by
  intro f hf
  simp only [sourceCurveHighCuts_of_exponent, List.mem_map, Finset.mem_toList] at hf
  obtain ⟨l, _, rfl⟩ := hf
  exact commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
    center Q ℓ K h v τ hτ hv hheight hjet l.val

/-- Every polynomial-curve agreement equation fits the common source-cut rectangle. -/
theorem symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree
    {r : ℕ} (center alpha : E) (values : Fin (ℓ + 1) → E)
    (Q : DifferentialPolynomial E[X] r) (K h v : ℕ)
    (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceCurveAgreement center Q K alpha values ∈
      restrictBidegree (F := E) (σ := Fin (r + 1))
        (sourceCurveCutChallengeDegree ℓ K h) (sourceCurveCutJetDegree K v) := by
  simpa only [symbolicSourceCurveAgreement, symbolicSourceCurveAgreement_of_exponent,
    flattenChallenge,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree] using
      taylorAgreementEquationOver_mem_restrictBidegree center alpha
        (powerBatchedCoordinate values) Q ℓ h v K
        (powerBatchedCoordinate_natDegree_le values) hv hheight hjet

/-- Every polynomial-curve agreement equation at a sufficient common exponent fits its exact
source-cut rectangle. -/
theorem symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree_of_exponent
    {r : ℕ} (center alpha : E) (values : Fin (ℓ + 1) → E)
    (Q : DifferentialPolynomial E[X] r) (K h v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hv : 0 < v)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    symbolicSourceCurveAgreement_of_exponent center Q K τ alpha values ∈
      restrictBidegree (F := E) (σ := Fin (r + 1))
        (sourceCurveCutChallengeDegree ℓ K h (τ := τ))
        (sourceCurveCutJetDegree K v (τ := τ)) := by
  simpa only [symbolicSourceCurveAgreement_of_exponent, flattenChallenge,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree] using
      taylorAgreementEquationOver_mem_restrictBidegree_of_exponent center alpha
        (powerBatchedCoordinate values) Q ℓ h v K τ hτ
        (powerBatchedCoordinate_natDegree_le values) hv hheight hjet

/-- Sharp off-tuple incidence for an order-zero source equation. -/
theorem finite_sourceCurve_points_off_tuples_card_le_sharp_one
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (K k L A v h : ℕ)
    (hK : 0 < K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (S : Finset (Option (Fin 1) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceCurveTupleLocus domain w iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement center Q K (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ sourceCurveInitialMixedDegreeOne ℓ K v h *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := symbolicSourceInitialEquation center Q
  let s := symbolicSourceSeparant center Q
  let high := sourceCurveHighCuts center Q K k
  let cuts : Fin n → MvPolynomial (Option (Fin 1)) E := fun i ↦
    symbolicSourceCurveAgreement center Q K (iota (domain i)) (fun t ↦ iota (w t i))
  have ha : 0 < sourceCurveCutChallengeDegree ℓ K h := by
    unfold sourceCurveCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      have : 0 < 2 * K * h := Nat.mul_pos (Nat.mul_pos (by omega) hK) hh
      omega
  have hb : 0 < sourceCurveCutJetDegree K v := by
    unfold sourceCurveCutJetDegree
    omega
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤ :=
    span_singleton_ne_top_of_aeval_eq_zero g x₀ (hS x₀ hx₀).1
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_one
    ha hb hLA hAn g s hinit hproper
      (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
      (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree
        center Q ℓ K h v hK hv hheight hjet)
      (symbolicSourceSeparant_mem_sourceCurveCutBidegree
        center Q ℓ K h v hK hheight hjet)
      high ?_ cuts ?_ (sourceCurveTupleLocus domain w iota center Q K k L) ?_ S ?_ ?_
  · intro f hf
    simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    exact symbolicSourceNumerator_mem_sourceCurveCutBidegree
      center Q ℓ K h v hv hheight hjet l.val
  · intro i
    exact symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree center
      (iota (domain i)) (fun t ↦ iota (w t i)) Q K h v hv hheight hjet
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_sourceCurveTupleLocus domain w iota center Q hK hkL J hJ
    · simpa only [s] using hsJ
    · simpa only [g] using hgJ
    · intro q hq
      exact hhighJ q (by simpa only [high] using hq)
    · exact hdJ
    · simpa only [cuts] using hcutsJ
  · intro x hx
    exact ⟨(hS x hx).1, (hS x hx).2.1, (by
      intro f hf
      simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
      obtain ⟨l, _, rfl⟩ := hf
      exact (hS x hx).2.2.1 l.val l.property), (hS x hx).2.2.2⟩
  · simpa only [cuts] using hA

/-- Sharp off-tuple incidence for a first-order source equation. -/
theorem finite_sourceCurve_points_off_tuples_card_le_sharp_two
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v h : ℕ)
    (hK : 1 < K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (S : Finset (Option (Fin 2) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceCurveTupleLocus domain w iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement center Q K (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ sourceCurveInitialMixedDegreeTwo ℓ K v h *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ 2 := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := symbolicSourceInitialEquation center Q
  let s := symbolicSourceSeparant center Q
  let high := sourceCurveHighCuts center Q K k
  let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
    symbolicSourceCurveAgreement center Q K (iota (domain i)) (fun t ↦ iota (w t i))
  have ha : 0 < sourceCurveCutChallengeDegree ℓ K h := by
    unfold sourceCurveCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      have hK' : 0 < K := by omega
      have : 0 < 2 * K * h := Nat.mul_pos (Nat.mul_pos (by omega) hK') hh
      omega
  have hb : 0 < sourceCurveCutJetDegree K v := by
    unfold sourceCurveCutJetDegree
    omega
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) E)) ≠ ⊤ :=
    span_singleton_ne_top_of_aeval_eq_zero g x₀ (hS x₀ hx₀).1
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_two
    ha hb hLA hAn g s hinit hproper
      (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
      (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree
        center Q ℓ K h v (by omega) hv hheight hjet)
      (symbolicSourceSeparant_mem_sourceCurveCutBidegree
        center Q ℓ K h v (by omega) hheight hjet)
      high ?_ cuts ?_ (sourceCurveTupleLocus domain w iota center Q K k L) ?_ S ?_ ?_
  · intro f hf
    simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    exact symbolicSourceNumerator_mem_sourceCurveCutBidegree
      center Q ℓ K h v hv hheight hjet l.val
  · intro i
    exact symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree center
      (iota (domain i)) (fun t ↦ iota (w t i)) Q K h v hv hheight hjet
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_sourceCurveTupleLocus domain w iota center Q hK hkL J hJ
    · simpa only [s] using hsJ
    · simpa only [g] using hgJ
    · intro q hq
      exact hhighJ q (by simpa only [high] using hq)
    · exact hdJ
    · simpa only [cuts] using hcutsJ
  · intro x hx
    exact ⟨(hS x hx).1, (hS x hx).2.1, (by
      intro f hf
      simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
      obtain ⟨l, _, rfl⟩ := hf
      exact (hS x hx).2.2.1 l.val l.property), (hS x hx).2.2.2⟩
  · simpa only [cuts] using hA

/-- Combine any source-point incidence estimate with sharp tuple counting and the exact
`ell * (n-L)` accidental-root bound.  The geometric source estimate is isolated in
`hsourceBound`; this partition and counting argument is independent of the source dimension. -/
theorem finite_sourceCurve_bad_challenges_card_le_of_source_bound_of_exponent
    {r : ℕ} [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (offBound : ℚ)
    (hsourceBound : ∀ S : Finset (Option (Fin (r + 1)) → E),
      (∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
        aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval x ((optionEquivRight E _).symm
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l
              (τ := τ))) = 0) ∧
        x ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ) →
      (∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
        symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
          (fun t ↦ iota (w t i))) x).card) →
      (S.card : ℚ) ≤ offBound)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz K l (τ := τ)) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
        ((((((n - k + 1) * sourceCurveCutJetDegree K v (τ := τ) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  classical
  let tuples := (polynomialTupleFamily domain w k).filter
    (IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ)
  have htuple (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (Finset.mem_filter.mp hP).2
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_exactPowerAgreement_family
    (k := k) (L := L) domain w iota tuples
      (fun P hP ↦ (htuple P hP).degree) (fun P hP ↦ (htuple P hP).common)
  let remaining := challenges \ exceptional
  let point : E → Option (Fin (r + 1)) → E := fun z i ↦ i.elim z (jet z)
  have hpointinj : Function.Injective point := by
    intro z z' heq
    exact congrFun heq none
  let S := remaining.image point
  have hcard : S.card = remaining.card := Finset.card_image_of_injective _ hpointinj
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    rintro ⟨P, hP, heq⟩
    have hjetEq : jet z = chartTupleJet iota center z P := by
      funext j
      exact congrFun heq (some j)
    have hs := (hchart z hzc).2.2.1
    have hregular :
        (chartTuplePullback iota center P (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      rw [chartTuplePullback, eval_polynomialGraphPullback]
      rw [← show point z = polynomialGraphPoint
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) z from heq]
      rw [sharp_source_separant_eval]
      exact hs
    have hrec := (hP.specialize hτ hkK z hregular).2.2.2
    have hw : witness z = powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hrec
    have hPmem : P ∈ tuples := by
      apply Finset.mem_filter.mpr
      exact ⟨mem_polynomialTupleFamily_of_commonAgreement domain w P k hP.degree
        (hkL.trans hP.common), hP⟩
    apply hbad z hzc
    rw [hw]
    exact hexact P hPmem z hze
  have hoffbound : (remaining.card : ℚ) ≤ offBound := by
    rw [← hcard]
    apply hsourceBound S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      refine ⟨?_, ?_, ?_, hoff z hz⟩
      · exact (sharp_source_initial_eval center z Q (jet z)).trans (hchart z hzc).2.1
      · rw [sharp_source_separant_eval]
        exact (hchart z hzc).2.2.1
      · intro l hl
        rw [sharp_source_numerator_eval_of_exponent]
        exact (hchart z hzc).2.2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, sharp_source_curveAgreement_eval_of_exponent,
        taylorAgreementEquation_eq_zero_iff_of_exponent _ _ _ τ hτ _
          (hchart z hzc).2.2.1,
        (hchart z hzc).2.2.2.2]
      exact (Finset.mem_filter.mp hi).2
  have htuplebound := admissibleChartTuples_card_le_sharp_of_exponent
    domain w iota center Q K k L v τ hτ hK hkK hk hkL (hLA.trans hAn) hjet tuples htuple
  have hexcbound : (exceptional.card : ℚ) ≤
      ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
        ((((((n - k + 1) * sourceCurveCutJetDegree K v (τ := τ) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
    have he : (exceptional.card : ℚ) ≤
        (tuples.card : ℚ) * ((ℓ * (n - L) : ℕ) : ℚ) := by
      exact_mod_cast hexc
    apply he.trans
    have hm := mul_le_mul_of_nonneg_right htuplebound
      (show (0 : ℚ) ≤ ((ℓ * (n - L) : ℕ) : ℚ) by positivity)
    simpa only [sourceCurveCutJetDegree, mul_assoc, mul_comm, mul_left_comm] using hm
  have hcover : challenges.card ≤ remaining.card + exceptional.card := by
    have he := Finset.card_sdiff_add_card_inter challenges exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      challenges ∩ exceptional ⊆ exceptional)
    dsimp only [remaining]
    omega
  have hcoverQ : (challenges.card : ℚ) ≤
      (remaining.card : ℚ) + (exceptional.card : ℚ) := by
    exact_mod_cast hcover
  exact hcoverQ.trans (add_le_add hoffbound hexcbound)

/-- Compatibility form of the source/tuple partition at exponent `2K`. -/
theorem finite_sourceCurve_bad_challenges_card_le_of_source_bound
    {r : ℕ} [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (offBound : ℚ)
    (hsourceBound : ∀ S : Finset (Option (Fin (r + 1)) → E),
      (∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
        aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
        x ∉ sourceCurveTupleLocus domain w iota center Q K k L) →
      (∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
        symbolicSourceCurveAgreement center Q K (iota (domain i))
          (fun t ↦ iota (w t i))) x).card) →
      (S.card : ℚ) ≤ offBound)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
        ((((((n - k + 1) * sourceCurveCutJetDegree K v : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  apply finite_sourceCurve_bad_challenges_card_le_of_source_bound_of_exponent
    domain w iota center Q K k L A v (2 * K) (taylorExponentSufficient_two_mul r K)
      hK hkK hk hkL hLA hAn hjet offBound
  · intro S hS hA
    apply hsourceBound S
    · intro x hx
      refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, ?_⟩
      · intro l hl
        simpa only [symbolicSourceNumerator] using (hS x hx).2.2.1 l hl
      · rw [← sourceCurveTupleLocus_of_exponent_two_mul_eq]
        exact (hS x hx).2.2.2
    · intro x hx
      simpa only [symbolicSourceCurveAgreement,
        symbolicSourceCurveAgreement_of_exponent] using hA x hx
  · exact hchart
  · exact hagree
  · exact hbad

/-- Exact fixed-center bad-challenge bound for an order-zero source equation. -/
theorem finite_sourceCurve_bad_challenges_card_le_sharp_one
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 0) (K k L A v h : ℕ)
    (hK : 0 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 1 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundOne n ℓ K k L A v h := by
  classical
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularSymbolicCurveMCASharpBoundOne
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := sharp_source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  simpa only [regularSymbolicCurveMCASharpBoundOne, pow_zero, mul_one] using
    (finite_sourceCurve_bad_challenges_card_le_of_source_bound
      domain w iota center Q K k L A v hK hkK hk hkL hLA hAn hjet
      ((sourceCurveInitialMixedDegreeOne ℓ K v h : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)))
      (fun S hS hA ↦ finite_sourceCurve_points_off_tuples_card_le_sharp_one
        domain w iota center Q K k L A v h hK hkL hLA hAn hD hv hinit
          hjet hheight S hS hA)
      challenges witness jet hchart hagree hbad)

/-- Exact fixed-center bad-challenge bound for a first-order source equation. -/
theorem finite_sourceCurve_bad_challenges_card_le_sharp_two
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v h : ℕ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundTwo n ℓ K k L A v h := by
  classical
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularSymbolicCurveMCASharpBoundTwo
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := sharp_source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  unfold regularSymbolicCurveMCASharpBoundTwo
  convert (finite_sourceCurve_bad_challenges_card_le_of_source_bound
      domain w iota center Q K k L A v hK hkK hk hkL hLA hAn hjet
      ((sourceCurveInitialMixedDegreeTwo ℓ K v h : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ 2)
      (fun S hS hA ↦ finite_sourceCurve_points_off_tuples_card_le_sharp_two
        domain w iota center Q K k L A v h hK hkL hLA hAn hD hv hinit
          hjet hheight S hS hA)
      challenges witness jet hchart hagree hbad) using 1
  ring

/-- Lift a fixed-center bad-challenge estimate to all regular symbolic solutions in a finite
challenge set.  The common Taylor center and selected witness polynomial may depend on that
finite set. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k A : ℕ)
    (hkK : k ≤ K)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (bound : ℚ)
    (hfixedCenter : ∀ (center : E) (challenges : Finset E)
      (witness : E → E[X]) (jet : E → Fin (r + 1) → E),
      (∀ z ∈ challenges,
        let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
        (witness z).degree < k ∧
          aeval (jet z) (initialJetEquation center Qz) = 0 ∧
          aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
          (∀ l : Fin K, k ≤ l.val →
            aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
          rationalTaylorPolynomial center Qz K (jet z) = witness z) →
      (∀ z ∈ challenges,
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card) →
      (∀ z ∈ challenges,
        ¬ HasExactPowerAgreement domain w iota k z (witness z)) →
      (challenges.card : ℚ) ≤ bound)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ bound := by
  classical
  let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
  have hw (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
  have hdeg (z : E) (hz : z ∈ S) : (witness z).degree < k := by
    simpa only [witness, dif_pos hz] using (hw z hz).1
  have hsol (z : E) (hz : z ∈ S) :
      differentialSpecialization (challengeSpecialization Q z) (witness z) = 0 := by
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.1
  have hsep (z : E) (hz : z ∈ S) : differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last r)) (witness z) ≠ 0 := by
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.2.1
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q S id witness hsep
  apply hfixedCenter center S witness (fun z ↦ polynomialJet center (witness z))
  · intro z hz
    have hs := hc z hz
    have hd : (witness z).degree < K := (hdeg z hz).trans_le (Nat.cast_le.mpr hkK)
    refine ⟨hdeg z hz, initialJetEquation_solution center _ _ (hsol z hz), ?_, ?_, ?_⟩
    · rwa [aeval_initialJetSeparant]
    · intro l hl
      change aeval (polynomialJet center (witness z))
        (commonTaylorNumerator center (challengeSpecialization Q z) K l) = 0
      rw [commonTaylorNumerator_solution center _ _ (hsol z hz) hs K hbin]
      have hcoeff : (Polynomial.taylor center (witness z)).coeff l.val = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simpa only [Polynomial.degree_taylor] using
          (hdeg z hz).trans_le (Nat.cast_le.mpr hl)
      rw [hcoeff, mul_zero]
    · apply symbolicWitnessPoint_reconstruction Q center z (witness z) K hd (hsol z hz)
      · exact (symbolicWitnessPoint_equations Q center z (witness z) K hd
          (hsol z hz) hs hbin).2.1
      · exact hbin
  · intro z hz
    simpa only [witness, dif_pos hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.2.2

/-- Every finite set of regular bad challenges for an order-zero equation satisfies the exact
mixed-bidegree and sharp-tuple budget. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_sharp_one
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (K k L A v h : ℕ)
    (hK : 0 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundOne n ℓ K k L A v h := by
  classical
  apply finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter
    domain w iota Q K k A hkK hbin
      (regularSymbolicCurveMCASharpBoundOne n ℓ K k L A v h) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_sourceCurve_bad_challenges_card_le_sharp_one
    domain w iota center Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight
      challenges witness jet hchart hagree hbad

/-- Every finite set of regular bad challenges for a first-order equation satisfies the exact
mixed-bidegree and sharp-tuple budget. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_sharp_two
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v h : ℕ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundTwo n ℓ K k L A v h := by
  classical
  apply finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter
    domain w iota Q K k A hkK hbin
      (regularSymbolicCurveMCASharpBoundTwo n ℓ K k L A v h) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_sourceCurve_bad_challenges_card_le_sharp_two
    domain w iota center Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight
      challenges witness jet hchart hagree hbad

private theorem set_finite_of_finset_card_le_rational {X : Type*} (T : Set X) (B : ℚ)
    (hbound : ∀ S : Finset X, ↑S ⊆ T → (S.card : ℚ) ≤ B) : T.Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := hbound S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- The full regular bad-challenge set for an order-zero equation is finite. -/
theorem regularSymbolicCurveBadChallenges_finite_sharp_one
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (K k L A v h : ℕ)
    (hK : 0 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0) :
    (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
  classical
  apply set_finite_of_finset_card_le_rational _
    (regularSymbolicCurveMCASharpBoundOne n ℓ K k L A v h)
  exact finite_regularSymbolicCurveBadChallenges_card_le_sharp_one
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin

/-- The full regular bad-challenge set for a first-order equation is finite. -/
theorem regularSymbolicCurveBadChallenges_finite_sharp_two
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v h : ℕ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0) :
    (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
  classical
  apply set_finite_of_finset_card_le_rational _
    (regularSymbolicCurveMCASharpBoundTwo n ℓ K k L A v h)
  exact finite_regularSymbolicCurveBadChallenges_card_le_sharp_two
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin

/-- A single sharply bounded exceptional set works for every regular order-zero solution. -/
theorem exists_exceptional_regularSymbolicCurveMCA_sharp_one
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (K k L A v h : ℕ)
    (hK : 0 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundOne n ℓ K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 0)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite := regularSymbolicCurveBadChallenges_finite_sharp_one
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le_sharp_one
      domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

/-- A single sharply bounded exceptional set works for every regular first-order solution. -/
theorem exists_exceptional_regularSymbolicCurveMCA_sharp_two
    [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v h : ℕ)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicCurveMCASharpBoundTwo n ℓ K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite := regularSymbolicCurveBadChallenges_finite_sharp_two
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le_sharp_two
      domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
