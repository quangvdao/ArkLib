/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ComponentDescent
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction

/-!
# Checked bounded shear projections

The input coordinates are `(Y,Z)` and the new coordinates are `(u,v)`. A trial substitutes
`Y=u-λv`, `Z=v`, scales by the computed leading scalar, and checks monicity, positive degree,
and the executed derivative gcd over the stored function field. Successful trials compute
the derivative resultant and its monic normalization. No normality or discriminant premise
is accepted as input.

The search remains explicitly partial: the missing bounded-grid existence theorem must show
that one of `λ=0,...,2B` passes under the paper's reducedness, coprimality, total-degree and
characteristic hypotheses. The outer-degree bound by the input total degree also remains
unproved here. Successful candidates have unconditional soundness proofs below.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection

open CompPoly CPolynomial CPoly
open BivariateReducedSupport

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

local instance : DecidableEq K := instDecidableEqOfLawfulBEq

/-- Executable coordinate substitution `Y=u-λv`, `Z=v`. -/
def shearHom (slope : K) : CMvPolynomial 2 K →+* CMvPolynomial 2 K :=
  CMvPolynomial.eval₂Hom TaylorReconstruction.coefficientConstant
    ![CMvPolynomial.X 0 - CMvPolynomial.C slope * CMvPolynomial.X 1, CMvPolynomial.X 1]

/-- Polynomial-ring interpretation of the same shear. -/
noncomputable def semanticShear (slope : K) :
    MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0 - MvPolynomial.C slope * MvPolynomial.X 1, MvPolynomial.X 1]

/-- The stored substitution computes exactly the stated coordinate map. -/
theorem shear_semantics (slope : K) (Q : CMvPolynomial 2 K) :
    fromCMvPolynomial (shearHom slope Q) = semanticShear slope (fromCMvPolynomial Q) := by
  rw [shearHom, CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv]
  change (CPoly.polyRingEquiv (n := 2) (R := K)).toRingHom _ = _
  rw [MvPolynomial.eval₂_comp_left]
  change MvPolynomial.eval₂ _ _ (fromCMvPolynomial Q) =
    MvPolynomial.eval₂ MvPolynomial.C
      ![MvPolynomial.X 0 - MvPolynomial.C slope * MvPolynomial.X 1, MvPolynomial.X 1]
      (fromCMvPolynomial Q)
  congr 1
  · apply RingHom.ext
    intro a
    change fromCMvPolynomial (CMvPolynomial.C a) = MvPolynomial.C a
    exact CMvPolynomial.fromCMvPolynomial_C a
  · funext i
    change fromCMvPolynomial _ = _
    fin_cases i
    · change (CPoly.polyRingEquiv (n := 2) (R := K)) (_ - _ * _) = _
      rw [_root_.map_sub, _root_.map_mul]
      change fromCMvPolynomial (CMvPolynomial.X 0) -
        fromCMvPolynomial (CMvPolynomial.C slope) *
        fromCMvPolynomial (CMvPolynomial.X 1) = _
      simp [CMvPolynomial.fromCMvPolynomial_C, CMvPolynomial.fromCMvPolynomial_X]
    · exact CMvPolynomial.fromCMvPolynomial_X 1

omit [BEq K] [LawfulBEq K] in
/-- The opposite shear is the inverse coordinate change. -/
theorem semanticShear_inverse (slope : K) :
    (semanticShear (-slope)).comp (semanticShear slope) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [semanticShear]
  · intro i
    fin_cases i <;> simp [semanticShear]

/-- Actual stored coordinate maps compose to the identity, not merely to a root-preserving map. -/
theorem shear_inverse (slope : K) (Q : CMvPolynomial 2 K) :
    shearHom (-slope) (shearHom slope Q) = Q := by
  apply fromCMvPolynomial_injective
  rw [shear_semantics, shear_semantics]
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K =>
    f (fromCMvPolynomial Q)) (semanticShear_inverse slope)

/-- The shear cannot erase a nonzero equation. -/
theorem shear_ne_zero (slope : K) {Q : CMvPolynomial 2 K} (hQ : Q ≠ 0) :
    shearHom slope Q ≠ 0 := by
  intro h
  have hi := shear_inverse slope Q
  rw [h, _root_.map_zero] at hi
  exact hQ hi.symm

/-- Materialize the transformed equation with `u` inner and `v` outer. -/
def transformed (slope : K) (Q : CMvPolynomial 2 K) : CBivariate K :=
  fromOrdinaryHom (shearHom slope Q)

/-- Computed scalar used to normalize the leading coefficient. -/
def scale (slope : K) (Q : CMvPolynomial 2 K) : K :=
  ((transformed slope Q).leadingCoeff.coeff 0)⁻¹

/-- Scalar normalization is performed before the monicity check. -/
def normalized (slope : K) (Q : CMvPolynomial 2 K) : CBivariate K :=
  CBivariate.CC (scale slope Q) * transformed slope Q

/-- Executed derivative-coprimality test over `K(u)`. -/
def derivativeCoprime (h : CBivariate K) : Bool :=
  FunctionFieldEuclid.gcd (ClearDenominators.embed h)
    (ClearDenominators.embed h).derivative == 1

/-- Runtime output of one successful trial. -/
structure Candidate (K : Type*) [Field K] [BEq K] [LawfulBEq K] where
  /-- Shear coefficient. -/
  slope : K
  /-- Nonzero scalar relating the equation to the original shear. -/
  scale : K
  /-- Monic equation in the new outer variable. -/
  equation : CBivariate K
  /-- Actual padded derivative resultant. -/
  resultant : CPolynomial K
  /-- Monic normalization of that resultant, a discriminant denominator. -/
  discriminant : CPolynomial K

/-- Try one coordinate shear; no desired geometric result is supplied to the checker. -/
def trySlope (slope : K) (Q : CMvPolynomial 2 K) : Option (Candidate K) :=
  let h := normalized slope Q
  if h.monic && decide (0 < h.natDegree) && derivativeCoprime h && scale slope Q != 0 then
    let r := RegularCenterObstruction.derivativeResultant h
    some ⟨slope, scale slope Q, h, r, CPolynomial.monicNormalize r⟩
  else none

/-- Search exactly the paper's bounded integer prefix, returning the first passing shear. -/
def search (bound : ℕ) (Q : CMvPolynomial 2 K) : Option (Candidate K) :=
  ((List.range (2 * bound + 1)).findSome? fun i : ℕ => trySlope (i : K) Q)

/-- Passing the stored Euclidean test proves derivative coprimality. -/
theorem derivativeCoprime_sound (h : CBivariate K) (hc : derivativeCoprime h = true) :
    IsCoprime (RegularCenterObstruction.functionFieldPolynomial h)
      (RegularCenterObstruction.functionFieldPolynomial h).derivative := by
  classical
  have hg := congrArg FunctionFieldEuclid.value (beq_iff_eq.mp hc)
  rw [FunctionFieldEuclid.value_gcd] at hg
  have hn : normalize (EuclideanDomain.gcd
      (FunctionFieldEuclid.value (ClearDenominators.embed h))
      (FunctionFieldEuclid.value (ClearDenominators.embed h).derivative)) = 1 := by
    simpa [FunctionFieldEuclid.value, CPolynomial.toPoly_one] using hg
  have hp := EuclideanDomain.gcd_isUnit_iff.mp (normalize_eq_one.mp hn)
  have hd : FunctionFieldEuclid.value (ClearDenominators.embed h).derivative =
      (FunctionFieldEuclid.value (ClearDenominators.embed h)).derivative := by
    simp [FunctionFieldEuclid.value, CPolynomial.derivative_toPoly,
      Polynomial.derivative_map]
  rw [hd, ClearDenominators.value_embed] at hp
  exact hp

/-- A checked monic stored equation is monic over the polynomial coefficient ring. -/
theorem monic_sound (h : CBivariate K) (hm : h.monic = true) :
    (CBivariate.toPoly h).Monic := by
  simpa [CBivariate.toPoly_eq_map] using
    ((CPolynomial.monic_toPoly_iff h).mp hm).map
      ((CPolynomial.ringEquiv (R := K)).toRingHom)

/-- Exact checked guarantees, without an integral-normality assertion. -/
structure Sound (Q : CMvPolynomial 2 K) (c : Candidate K) : Prop where
  /-- The recorded scalar is the one computed from the leading coefficient. -/
  scale_eq : c.scale = scale c.slope Q
  /-- This scalar is invertible. -/
  scale_ne_zero : c.scale ≠ 0
  /-- The returned equation is the scalar multiple of the actual shear. -/
  equation_eq : c.equation = normalized c.slope Q
  /-- The equation is monic. -/
  monic : (CBivariate.toPoly c.equation).Monic
  /-- The outer degree is positive. -/
  positive : 0 < c.equation.natDegree
  /-- The function-field equation is separable. -/
  separable : (RegularCenterObstruction.functionFieldPolynomial c.equation).Separable
  /-- The resultant is computed from the equation. -/
  resultant_eq : c.resultant = RegularCenterObstruction.derivativeResultant c.equation
  /-- The computed resultant is nonzero. -/
  resultant_ne_zero : c.resultant ≠ 0
  /-- The denominator is the monic associate of that resultant. -/
  discriminant_eq : c.discriminant = CPolynomial.monicNormalize c.resultant
  /-- The denominator is monic. -/
  discriminant_monic : c.discriminant.toPoly.Monic
  /-- In particular the denominator is nonzero. -/
  discriminant_ne_zero : c.discriminant ≠ 0

/-- Every successful trial has the stated guarantees. -/
theorem trySlope_sound (slope : K) (Q : CMvPolynomial 2 K) (c : Candidate K)
    (hc : trySlope slope Q = some c) : Sound Q c := by
  classical
  unfold trySlope at hc
  dsimp only at hc
  split at hc
  next hp =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hp
    obtain ⟨⟨⟨hm, hd⟩, hg⟩, hs⟩ := hp
    cases Option.some.inj hc
    have hmonic := monic_sound _ hm
    have hcoprime := derivativeCoprime_sound _ hg
    have hr := RegularCenterObstruction.derivativeResultant_ne_zero
      (⟨normalized slope Q, hmonic.isPrimitive, hd, hcoprime⟩ :
        RegularCenterObstruction.Input K)
    have hrp : (RegularCenterObstruction.derivativeResultant
        (normalized slope Q)).toPoly ≠ 0 := by
      intro hz
      exact hr (CPolynomial.toPoly_injective (hz.trans CPolynomial.toPoly_zero.symm))
    have hmnorm : (CPolynomial.monicNormalize
        (RegularCenterObstruction.derivativeResultant (normalized slope Q))).toPoly.Monic := by
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact Polynomial.monic_normalize hrp
    exact ⟨rfl, hs, rfl, hmonic, hd, hcoprime, rfl, hr, rfl, hmnorm,
      fun hz => hmnorm.ne_zero (by
        dsimp only at hz
        rw [hz, CPolynomial.toPoly_zero])⟩
  next => simp at hc

/-- The output records precisely the slope used in the trial. -/
theorem trySlope_slope (slope : K) (Q : CMvPolynomial 2 K) (c : Candidate K)
    (hc : trySlope slope Q = some c) : c.slope = slope := by
  unfold trySlope at hc
  dsimp only at hc
  split at hc
  · cases Option.some.inj hc
    rfl
  · simp at hc

/-- The recorded resultant has the standard polynomial resultant interpretation. -/
theorem Sound.resultant_toPoly {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) : c.resultant.toPoly =
      Polynomial.separableResultant (CBivariate.toPoly c.equation) c.equation.natDegree := by
  rw [hc.resultant_eq, RegularCenterObstruction.derivativeResultant_toPoly]

/-- Search outputs are sound and use an integer slope in the requested prefix. -/
theorem search_sound (bound : ℕ) (Q : CMvPolynomial 2 K) (c : Candidate K)
    (hc : search bound Q = some c) : Sound Q c ∧
      ∃ i : ℕ, i ≤ 2 * bound ∧ trySlope (i : K) Q = some c := by
  obtain ⟨i, hi, ht⟩ := List.exists_of_findSome?_eq_some hc
  exact ⟨trySlope_sound _ _ _ ht, i, by simpa using hi, ht⟩

/-- The precise remaining existence obligation for this executable search.
A geometric bounded-grid theorem must derive this predicate from the paper's hypotheses. -/
def HasPassingSlope (bound : ℕ) (Q : CMvPolynomial 2 K) : Prop :=
  ∃ i : ℕ, i ≤ 2 * bound ∧ (trySlope (i : K) Q).isSome

/-- Conditional success exposes exactly the missing existence obligation. -/
theorem search_success_iff (bound : ℕ) (Q : CMvPolynomial 2 K) :
    (search bound Q).isSome ↔ HasPassingSlope bound Q := by
  simp [search, HasPassingSlope, List.findSome?_isSome_iff]

end Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection
