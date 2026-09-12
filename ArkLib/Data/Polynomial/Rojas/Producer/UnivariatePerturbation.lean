/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.Univariate
public import ArkLib.Data.Polynomial.Rojas.PerturbationCoefficient
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Higher-degree univariate Rojas perturbations

For one equation, this module implements Definition 2 of J. Maurice Rojas,
*Solving Degenerate Sparse Polynomial Systems Faster*, J. Symbolic Computation
28 (1999), 155--186.  Given stored polynomials `f` and `fStar`, it constructs

`Res_x(f(x) - s fStar(x), t + u x)`

by the checked stored Sylvester determinant.  The executable code then scans
the resulting polynomial in `s` for its first nonzero coefficient.  Neither a
resultant nor a perturbation coefficient is accepted from the caller.

This is the univariate dense-support checkpoint.  It does not construct a
multivariate toric resultant or prove arbitrary isolated-root coverage.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.UnivariatePerturbation

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas ArkLib.Rojas.Producer.Univariate

variable {F : Type*} [CommRing F] [Nontrivial F] [BEq F] [LawfulBEq F]

/-- Executable coefficient map on stored canonical coefficient arrays. -/
def mapCoefficients {R S : Type*} [CommRing R] [CommRing S]
    [BEq R] [LawfulBEq R] [BEq S] [LawfulBEq S]
    (f : R →+* S) (p : CPolynomial R) : CPolynomial S :=
  CPolynomial.ofArray (p.val.map f)

/-- The stored array map is semantic polynomial base change. -/
theorem toPoly_mapCoefficients {R S : Type*} [CommRing R] [CommRing S]
    [BEq R] [LawfulBEq R] [BEq S] [LawfulBEq S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (p : CPolynomial R) :
    (mapCoefficients f p).toPoly = p.toPoly.map f := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly]
  change (CPolynomial.ofArray (p.val.map f)).coeff i = f (p.coeff i)
  rw [CPolynomial.coeff_ofArray]
  change (p.val.map f).getD i 0 = f (p.val.getD i 0)
  simp only [Array.getD, Array.size_map]
  split_ifs <;> simp

/-- Coefficients of the executable stored array map. -/
theorem coeff_mapCoefficients {R S : Type*} [CommRing R] [CommRing S]
    [BEq R] [LawfulBEq R] [BEq S] [LawfulBEq S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (p : CPolynomial R) (i : ℕ) :
    (mapCoefficients f p).coeff i = f (p.coeff i) := by
  rw [CPolynomial.coeff_toPoly, toPoly_mapCoefficients, Polynomial.coeff_map,
    ← CPolynomial.coeff_toPoly]

noncomputable def evalHom {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (x : R) : CPolynomial R →+* R :=
  (Polynomial.evalRingHom x).comp CPolynomial.toPolyRingHom

@[simp]
theorem evalHom_apply {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (x : R) (p : CPolynomial R) :
    evalHom x p = p.eval x := by
  rw [evalHom, RingHom.coe_comp, Function.comp_apply,
    CPolynomial.toPolyRingHom_apply, CPolynomial.eval_toPoly]
  rfl

/-- Ring-homomorphic specialization commutes with the stored Sylvester determinant. -/
theorem map_storedResultant {R S : Type*} [CommRing R] [CommRing S]
    [BEq R] [LawfulBEq R] [BEq S] [LawfulBEq S] [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (p q : CPolynomial R) (m n : ℕ) :
    f (storedResultant p q m n) =
      storedResultant (mapCoefficients f p) (mapCoefficients f q) m n := by
  rw [storedResultant_eq, storedResultant_eq, toPoly_mapCoefficients,
    toPoly_mapCoefficients, Polynomial.resultant_map_map]

/-- Embed a base-field coefficient as a constant in both `t` and `s`. -/
def scalarHom : F →+* CPolynomial (CPolynomial F) := CHom.comp CHom

@[simp]
theorem evalHom_zero_scalarHom (a : F) :
    evalHom (0 : CPolynomial F) (scalarHom a) = C a := by
  rw [evalHom_apply]
  change (C (C a) : CPolynomial (CPolynomial F)).eval 0 = C a
  rw [CPolynomial.eval_toPoly]
  simp [CPolynomial.C_toPoly]

/-- Regard a stored input polynomial as a polynomial in `x` over `F[t][s]`. -/
def liftInput (f : CPolynomial F) : CPolynomial (CPolynomial (CPolynomial F)) :=
  mapCoefficients (scalarHom (F := F)) f

/-- The Rojas deformation `f - s*fStar`, built from the two stored inputs. -/
def perturbedInput (f fStar : CPolynomial F) : CPolynomial (CPolynomial (CPolynomial F)) :=
  liftInput f -
    C (X : CPolynomial (CPolynomial F)) * liftInput fStar

/-- The dense univariate auxiliary form `t + u*x`. -/
def auxiliaryForm (u : F) : CPolynomial (CPolynomial (CPolynomial F)) :=
  C (C (X : CPolynomial F)) + C (C (C u)) * X

/-- The original equation over the single auxiliary-variable coefficient ring. -/
def liftAtT (f : CPolynomial F) : CPolynomial (CPolynomial F) :=
  mapCoefficients CHom f

/-- The auxiliary form after setting the perturbation parameter `s` to zero. -/
def auxiliaryAtT (u : F) : CPolynomial (CPolynomial F) :=
  C (X : CPolynomial F) + C (C u) * X

/-- The determinant at `s = 0`, computed directly from the original equation. -/
def baseCharacteristic (f : CPolynomial F) (u : F) (degreeBound : ℕ) :
    CPolynomial F :=
  storedResultant (liftAtT f) (auxiliaryAtT u) degreeBound 1

/-- At the canonical injective auxiliary form `t+x`, the input-derived factor polynomial. -/
def derivedFactor (f : CPolynomial F) (degreeBound : ℕ) : CPolynomial F :=
  (-1 : CPolynomial F) ^ degreeBound * (liftAtT f).eval (-X)

/-- The transformed stored input has the expected semantic substitution. -/
theorem toPoly_eval_liftAtT_negX (f : CPolynomial F) :
    ((liftAtT f).eval (-X)).toPoly = f.toPoly.comp (-Polynomial.X) := by
  rw [CPolynomial.eval_toPoly]
  rw [← CPolynomial.toPolyRingHom_apply]
  rw [← Polynomial.eval₂_at_apply
    (p := (liftAtT f).toPoly) CPolynomial.toPolyRingHom (-X)]
  rw [Polynomial.eval₂_eq_eval_map, liftAtT, toPoly_mapCoefficients,
    Polynomial.map_map]
  simp only [CPolynomial.toPolyRingHom_apply, CPolynomial.toPoly_neg,
    CPolynomial.X_toPoly]
  have hhom : (CPolynomial.toPolyRingHom (R := F)).comp
      (CHom (R := F)) = (Polynomial.C : F →+* Polynomial F) := by
    ext a
    simp [CPolynomial.toPolyRingHom_apply, CPolynomial.C_toPoly]
  rw [hhom]
  rw [Polynomial.eval_map]
  rfl

theorem specialize_perturbedInput_zero (f fStar : CPolynomial F) :
    mapCoefficients (evalHom (0 : CPolynomial F)) (perturbedInput f fStar) =
      liftAtT f := by
  apply CPolynomial.toPoly_injective
  rw [toPoly_mapCoefficients, perturbedInput, CPolynomial.toPoly_sub,
    CPolynomial.toPoly_mul, CPolynomial.C_toPoly, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C]
  simp only [liftInput, liftAtT, toPoly_mapCoefficients]
  rw [Polynomial.map_map, Polynomial.map_map]
  have hscalar : (evalHom (0 : CPolynomial F)).comp (scalarHom (F := F)) = CHom := by
    apply RingHom.ext
    intro a
    exact evalHom_zero_scalarHom a
  have hX : (X : CPolynomial (CPolynomial F)).coeff 0 = 0 := by rfl
  rw [hscalar, evalHom_apply, CPolynomial.eval_zero_eq_coeff_zero,
    hX, Polynomial.C_0]
  ring

theorem specialize_auxiliaryForm_zero (u : F) :
    mapCoefficients (evalHom (0 : CPolynomial F)) (auxiliaryForm u) =
      auxiliaryAtT u := by
  apply CPolynomial.toPoly_injective
  simp [toPoly_mapCoefficients, auxiliaryForm, auxiliaryAtT, evalHom,
    CPolynomial.toPoly_add, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]

/-- Compute the generalized characteristic by the checked stored determinant. -/
def characteristic? (f fStar : CPolynomial F) (u : F) (degreeBound : ℕ) :
    Option (CPolynomial (CPolynomial F)) :=
  checkedResultant (perturbedInput f fStar) (auxiliaryForm u) degreeBound 1

/-- Compute the first prescribed nonzero `s`-coefficient of the actual characteristic. -/
def perturbation? (f fStar : CPolynomial F) (u : F) (degreeBound : ℕ) :
    Option (CPolynomial F) := do
  let characteristic ← characteristic? f fStar u degreeBound
  toricPerturbationCoefficient? characteristic

/-- Successful execution refines the exact resultant of the two stored inputs. -/
theorem characteristic?_eq_some_iff (f fStar : CPolynomial F) (u : F)
    (degreeBound : ℕ) (characteristic : CPolynomial (CPolynomial F)) :
    characteristic? f fStar u degreeBound = some characteristic ↔
      (perturbedInput f fStar).toPoly.natDegree ≤ degreeBound ∧
      (auxiliaryForm u).toPoly.natDegree ≤ 1 ∧
      Polynomial.resultant (perturbedInput f fStar).toPoly
        (auxiliaryForm u).toPoly degreeBound 1 = characteristic := by
  simpa [characteristic?] using checkedResultant_eq_some_iff
    (perturbedInput f fStar) (auxiliaryForm u) degreeBound 1 characteristic

/-- The constant `s` coefficient of the computed characteristic is the
resultant built from the original equation itself. -/
theorem coeff_zero_of_characteristic
    (f fStar : CPolynomial F) (u : F) (degreeBound : ℕ)
    (characteristic : CPolynomial (CPolynomial F))
    (hcharacteristic : characteristic? f fStar u degreeBound = some characteristic) :
    characteristic.coeff 0 = baseCharacteristic f u degreeBound := by
  have hresult := (characteristic?_eq_some_iff f fStar u degreeBound characteristic).mp
    hcharacteristic
  have hstored : storedResultant (perturbedInput f fStar) (auxiliaryForm u)
      degreeBound 1 = characteristic := by
    rw [storedResultant_eq]
    exact hresult.2.2
  have hmapped := congrArg (evalHom (0 : CPolynomial F)) hstored
  rw [map_storedResultant, specialize_perturbedInput_zero,
    specialize_auxiliaryForm_zero, evalHom_apply,
    CPolynomial.eval_zero_eq_coeff_zero] at hmapped
  exact hmapped.symm

/-- With `u = 1`, the original resultant is the explicit transformed input
`(-1)^d f(-t)`.  This is derived from `f`, not supplied as a factorization. -/
theorem baseCharacteristic_one_eq_derivedFactor (f : CPolynomial F)
    (degreeBound : ℕ) (hdegree : f.toPoly.natDegree ≤ degreeBound) :
    baseCharacteristic f 1 degreeBound = derivedFactor f degreeBound := by
  rw [baseCharacteristic, storedResultant_eq]
  have hlift : (liftAtT f).toPoly.natDegree ≤ degreeBound := by
    rw [liftAtT, toPoly_mapCoefficients]
    exact (Polynomial.natDegree_map_le).trans hdegree
  have haux : (auxiliaryAtT (1 : F)).toPoly =
      Polynomial.X + Polynomial.C (X : CPolynomial F) := by
    have hone : (C (1 : F) : CPolynomial F) = 1 := by
      apply CPolynomial.toPoly_injective
      simp [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
    simp only [auxiliaryAtT, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]
    rw [hone, Polynomial.C_1, one_mul]
    ring
  rw [haux, Polynomial.resultant_X_add_C_right
    (f := (liftAtT f).toPoly) (m := degreeBound) (X : CPolynomial F) hlift]
  simp [derivedFactor, CPolynomial.eval_toPoly]

variable [NoZeroDivisors F]

/-- Exact positive degree makes the input-derived factor nonzero. -/
theorem derivedFactor_ne_zero (f : CPolynomial F) (degreeBound : ℕ)
    (hf : f ≠ 0) : derivedFactor f degreeBound ≠ 0 := by
  intro hzero
  have hpoly := congrArg CPolynomial.toPoly hzero
  rw [derivedFactor, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
    CPolynomial.toPoly_neg, CPolynomial.toPoly_one,
    toPoly_eval_liftAtT_negX, CPolynomial.toPoly_zero] at hpoly
  have hcomp : f.toPoly.comp (-Polynomial.X) = 0 := by
    exact (mul_eq_zero.mp hpoly).resolve_left (by simp)
  have hfpoly : f.toPoly = 0 := Polynomial.comp_neg_X_eq_zero_iff.mp hcomp
  apply hf
  apply CPolynomial.toPoly_injective
  rw [hfpoly, CPolynomial.toPoly_zero]

/-- Once the checked determinant succeeds, the scanner returns its constant
coefficient, which is the input-derived factor at the canonical auxiliary form. -/
theorem perturbation?_eq_some_derivedFactor
    (f fStar : CPolynomial F) (degreeBound : ℕ)
    (characteristic : CPolynomial (CPolynomial F))
    (hdegree : f.toPoly.natDegree ≤ degreeBound) (hf : f ≠ 0)
    (hcharacteristic : characteristic? f fStar 1 degreeBound = some characteristic) :
    perturbation? f fStar 1 degreeBound = some (derivedFactor f degreeBound) := by
  rw [perturbation?, hcharacteristic]
  apply toricPerturbationCoefficient?_eq_some_iff.mpr
  have hfactor : characteristic.coeff 0 = derivedFactor f degreeBound := by
    rw [coeff_zero_of_characteristic f fStar 1 degreeBound characteristic hcharacteristic,
      baseCharacteristic_one_eq_derivedFactor f degreeBound hdegree]
  have hnonzero := derivedFactor_ne_zero f degreeBound hf
  refine ⟨hnonzero, 0, ?_, hfactor, by omega⟩
  by_contra hsize
  have hcoefficient := coeff_eq_zero_of_size_le characteristic (i := 0) (by omega)
  exact hnonzero (hfactor.symm.trans hcoefficient)

/-- Observable output of one successful canonical auxiliary specialization. -/
structure Output where
  auxiliary : F
  characteristic : CPolynomial (CPolynomial F)
  perturbation : CPolynomial F
  factor : CPolynomial F

/-- Why one deterministic auxiliary candidate did not produce an output. -/
inductive AttemptResult where
  | rejectedAuxiliary
  | rejectedDegreeBounds
  | zeroPerturbation
  | success (output : Output (F := F))

/-- Try one auxiliary slope.  In one affine variable the canonical projection
`x ↦ x` is injective, so this bounded checkpoint prescribes slope `u=1`. -/
def attempt (f fStar : CPolynomial F) (degreeBound : ℕ) (u : F) :
    AttemptResult (F := F) :=
  if u != 1 then
    .rejectedAuxiliary
  else
    match characteristic? f fStar u degreeBound with
    | none => .rejectedDegreeBounds
    | some characteristic =>
        match toricPerturbationCoefficient? characteristic with
        | none => .zeroPerturbation
        | some perturbation => .success
            { auxiliary := u
              characteristic
              perturbation
              factor := derivedFactor f degreeBound }

/-- Scan in caller order and return the first successful computed specialization. -/
def selectAuxiliary? (f fStar : CPolynomial F) (degreeBound : ℕ) :
    List F → Option (Output (F := F))
  | [] => none
  | u :: candidates =>
      match attempt f fStar degreeBound u with
      | .success output => some output
      | _ => selectAuxiliary? f fStar degreeBound candidates

/-- Explicit top-level failures for the higher-degree univariate contract. -/
inductive ProducerError where
  | degreeBelowThree
  | zeroEquation
  | constantEquation
  | undersizedDegreeBound
  | noSuccessfulAuxiliary
  deriving BEq

/-- Higher-degree univariate Rojas producer with explicit degeneration policy. -/
def run (f fStar : CPolynomial F) (degreeBound : ℕ) (candidates : List F) :
    Except ProducerError (Output (F := F)) :=
  if degreeBound < 3 then
    .error .degreeBelowThree
  else if f == 0 then
    .error .zeroEquation
  else if f.natDegree == 0 then
    .error .constantEquation
  else if degreeBound < f.natDegree || degreeBound < fStar.natDegree then
    .error .undersizedDegreeBound
  else match selectAuxiliary? f fStar degreeBound candidates with
    | none => .error .noSuccessfulAuxiliary
    | some output => .ok output

/-- A successful attempt stores only values computed by the determinant and
coefficient scan. -/
def Output.Correct (f fStar : CPolynomial F) (degreeBound : ℕ)
    (output : Output (F := F)) : Prop :=
  output.auxiliary = 1 ∧
  characteristic? f fStar output.auxiliary degreeBound = some output.characteristic ∧
  perturbation? f fStar output.auxiliary degreeBound = some output.perturbation ∧
  output.factor = derivedFactor f degreeBound

omit [NoZeroDivisors F] in
theorem attempt_success_correct {f fStar : CPolynomial F} {degreeBound : ℕ} {u : F}
    {output : Output (F := F)} (h : attempt f fStar degreeBound u = .success output) :
    output.Correct f fStar degreeBound := by
  unfold attempt at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hnot characteristicOption characteristic hcharacteristic
    perturbationOption perturbation hperturbation
  cases h
  have huone : u = 1 := by simpa [bne_iff_ne] using hnot
  subst u
  have hcharacteristicOne : characteristic? f fStar 1 degreeBound = some characteristic := by
    exact hcharacteristic
  refine ⟨rfl, ?_, ?_, rfl⟩
  · exact hcharacteristicOne
  · change perturbation? f fStar 1 degreeBound = some perturbation
    rw [perturbation?, hcharacteristicOne]
    exact hperturbation

omit [NoZeroDivisors F] in
/-- Every result returned by the deterministic candidate scan comes from a
successful checked determinant and coefficient scan. -/
theorem selectAuxiliary?_eq_some_correct {f fStar : CPolynomial F}
    {degreeBound : ℕ} {candidates : List F} {output : Output (F := F)}
    (h : selectAuxiliary? f fStar degreeBound candidates = some output) :
    output.Correct f fStar degreeBound := by
  induction candidates with
  | nil => simp [selectAuxiliary?] at h
  | cons u candidates ih =>
      simp only [selectAuxiliary?] at h
      cases hattempt : attempt f fStar degreeBound u with
      | rejectedAuxiliary => rw [hattempt] at h; exact ih h
      | rejectedDegreeBounds => rw [hattempt] at h; exact ih h
      | zeroPerturbation => rw [hattempt] at h; exact ih h
      | success found =>
          rw [hattempt] at h
          cases h
          exact attempt_success_correct hattempt

omit [NoZeroDivisors F] in
/-- Successful top-level execution refines the actual checked characteristic
and its first nonzero coefficient. -/
theorem run_eq_ok_correct {f fStar : CPolynomial F} {degreeBound : ℕ}
    {candidates : List F} {output : Output (F := F)}
    (h : run f fStar degreeBound candidates = .ok output) :
    output.Correct f fStar degreeBound := by
  unfold run at h
  split at h
  · contradiction
  split at h
  · contradiction
  split at h
  · contradiction
  split at h
  · contradiction
  split at h
  · contradiction
  rename_i hselection
  cases h
  exact selectAuxiliary?_eq_some_correct hselection

/-- On a nonzero input within its degree bound, success identifies the scanned
perturbation with the independently derived factor polynomial. -/
theorem Output.perturbation_eq_factor {f fStar : CPolynomial F} {degreeBound : ℕ}
    (output : Output (F := F)) (hcorrect : output.Correct f fStar degreeBound)
    (hdegree : f.toPoly.natDegree ≤ degreeBound) (hf : f ≠ 0) :
    output.perturbation = output.factor := by
  rcases hcorrect with ⟨haux, hcharacteristic, hperturbation, hfactor⟩
  rw [haux] at hcharacteristic hperturbation
  rw [perturbation?_eq_some_derivedFactor f fStar degreeBound output.characteristic
    hdegree hf hcharacteristic] at hperturbation
  exact Option.some.inj hperturbation |>.symm.trans hfactor.symm

end ArkLib.Rojas.Producer.UnivariatePerturbation
