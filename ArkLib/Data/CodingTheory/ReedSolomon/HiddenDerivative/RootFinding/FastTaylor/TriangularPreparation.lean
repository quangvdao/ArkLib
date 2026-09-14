/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Validity
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Global.Residual
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularRecurrence

/-!
# Preparing the original equation for finite Taylor recurrence

Substitution maps the independent variable to the center plus its displacement and maps
coefficients into the supplied commutative algebra. It uses no factorials or divisions,
including when the independent-variable degree reaches the characteristic.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.TriangularPreparation

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.TruncatedSeries

variable {E A : Type*} [Field E] [BEq E] [LawfulBEq E]
  [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A] {r : ℕ}

/-- The original independent variable is translated; jet variables retain their indices. -/
def shiftedVariables (center : A) : Fin (r + 2) → CMvPolynomial (r + 2) A :=
  Fin.cases (CMvPolynomial.X 0 + CMvPolynomial.C center)
    (fun j => CMvPolynomial.X j.succ)

/-- Executable division-free shift and coefficient transport of the original equation. -/
def shiftEquation (base : E →+* A) (center : E) (T : CMvPolynomial (r + 2) E) :
    CMvPolynomial (r + 2) A :=
  T.eval₂ (coefficientConstant.comp base) (shiftedVariables (base center))

omit [BEq E] [LawfulBEq E] [Nontrivial A] in
/-- Semantic substitution for the computed shift, before any residual evaluation. -/
theorem shiftEquation_semantics (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) :
    fromCMvPolynomial (shiftEquation base center T) =
      MvPolynomial.eval₂ (MvPolynomial.C.comp base)
        (Fin.cases (MvPolynomial.X 0 + MvPolynomial.C (base center))
          (fun j : Fin (r + 1) => MvPolynomial.X j.succ)) (fromCMvPolynomial T) := by
  rw [shiftEquation, CPoly.eval₂_equiv]
  change (polyRingEquiv (n := r + 2) (R := A)).toRingHom _ = _
  rw [MvPolynomial.hom_eval₂]
  congr 1
  · apply RingHom.ext
    intro c
    exact CMvPolynomial.fromCMvPolynomial_C (base c)
  · funext i
    change fromCMvPolynomial (shiftedVariables (base center) i) = _
    cases i using Fin.cases <;>
      simp [shiftedVariables, CPoly.map_add, CMvPolynomial.fromCMvPolynomial_C,
        CMvPolynomial.fromCMvPolynomial_X]

omit [BEq E] [LawfulBEq E] [Nontrivial A] in
/-- Evaluating the shifted equation evaluates the original at the translated independent point. -/
theorem eval_shiftEquation {B : Type*} [CommRing B]
    (base : E →+* A) (center : E) (T : CMvPolynomial (r + 2) E)
    (f : A →+* B) (point : Fin (r + 2) → B) :
    (shiftEquation base center T).eval₂ f point =
      T.eval₂ (f.comp base)
        (Fin.cases (point 0 + f (base center)) (fun j : Fin (r + 1) => point j.succ)) := by
  rw [CPoly.eval₂_equiv, shiftEquation_semantics]
  change MvPolynomial.eval₂Hom f point _ = _
  rw [MvPolynomial.hom_eval₂]
  rw [CPoly.eval₂_equiv]
  congr 1
  · ext c
    simp
  · funext i
    cases i using Fin.cases <;> simp

omit [BEq E] [LawfulBEq E] in
/-- The shifted finite residual is the original equation's differential residual at the center. -/
theorem residual_shiftEquation (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (known : List A) :
    (TriangularResidual.residual (shiftEquation base center T) known).toPoly =
      Global.ringResidual base center (TriangularResidual.polynomial known).toPoly
        (semanticEquation T) := by
  rw [TriangularResidual.residual, eval_shiftEquation]
  rw [← CPolynomial.toPolyRingHom_apply, CPoly.eval₂_equiv, MvPolynomial.hom_eval₂]
  rw [Global.ringResidual, semanticEquation, MvPolynomial.eval₂Hom_rename]
  change MvPolynomial.eval₂ _ _ (fromCMvPolynomial T) =
    MvPolynomial.eval₂ _ _ (fromCMvPolynomial T)
  congr 1
  · ext c
    simp [CPolynomial.CHom, CPolynomial.C_toPoly]
  · funext i
    cases i using Fin.cases with
    | zero =>
      simp [TriangularResidual.jet, CPolynomial.toPolyRingHom_apply,
        CPolynomial.toPoly_add, CPolynomial.X_toPoly, CPolynomial.CHom,
        CPolynomial.C_toPoly, finToJetVariable, add_comm]
    | succ j =>
      simpa [finToJetVariable, CPolynomial.toPolyRingHom_apply] using
        TriangularResidual.jet_toPoly (r := r) known j.succ


omit [BEq E] [LawfulBEq E] [BEq A] [LawfulBEq A] in
private theorem pderiv_substitution (base : E →+* A) (center : E)
    (P : MvPolynomial (Fin (r + 2)) E) (j : Fin (r + 1)) :
    MvPolynomial.pderiv j.succ
      (MvPolynomial.eval₂ (MvPolynomial.C.comp base)
        (Fin.cases (MvPolynomial.X 0 + MvPolynomial.C (base center))
          (fun i : Fin (r + 1) => MvPolynomial.X i.succ)) P) =
      MvPolynomial.eval₂ (MvPolynomial.C.comp base)
        (Fin.cases (MvPolynomial.X 0 + MvPolynomial.C (base center))
          (fun i : Fin (r + 1) => MvPolynomial.X i.succ)) (MvPolynomial.pderiv j.succ P) := by
  classical
  let v : Fin (r + 2) → MvPolynomial (Fin (r + 2)) A :=
    Fin.cases (MvPolynomial.X 0 + MvPolynomial.C (base center))
      (fun i : Fin (r + 1) => MvPolynomial.X i.succ)
  have hv (i : Fin (r + 2)) : MvPolynomial.pderiv j.succ (v i) =
      MvPolynomial.eval₂ (MvPolynomial.C.comp base) v
        (MvPolynomial.pderiv j.succ (MvPolynomial.X i)) := by
    cases i using Fin.cases <;> simp [v, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  change MvPolynomial.pderiv j.succ (MvPolynomial.eval₂ _ v P) =
    MvPolynomial.eval₂ _ v (MvPolynomial.pderiv j.succ P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hp hq => simp [MvPolynomial.eval₂_add, hp, hq]
  | mul_X P i hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.pderiv_mul,
      MvPolynomial.eval₂_add, hp, hv]

/-- Translation in the independent variable commutes with every jet partial derivative. -/
theorem partialDerivative_shiftEquation (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (j : Fin (r + 1)) :
    CMvPolynomial.partialDerivative j.succ (shiftEquation base center T) =
      shiftEquation base center (CMvPolynomial.partialDerivative j.succ T) := by
  apply eq_iff_fromCMvPolynomial.mpr
  rw [CMvPolynomial.fromCMvPolynomial_partialDerivative, shiftEquation_semantics,
    shiftEquation_semantics, CMvPolynomial.fromCMvPolynomial_partialDerivative]
  exact pderiv_substitution base center _ j

/-- The prepared separant is the actual original highest partial at the initial coordinates. -/
theorem separant_shiftEquation (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (known : List A) :
    TriangularResidual.separant (shiftEquation base center T) known =
      (CMvPolynomial.partialDerivative (Fin.last (r + 1)) T).eval₂ base
        (Fin.cases (base center) (fun j : Fin (r + 1) => known.getD j.val 0)) := by
  unfold TriangularResidual.separant
  rw [show Fin.last (r + 1) = (Fin.last r).succ from rfl,
    partialDerivative_shiftEquation, eval_shiftEquation]
  simp

omit [BEq E] [LawfulBEq E] in
/-- The prepared initial-root check evaluates the original equation at its actual center. -/
theorem initial_residual_shiftEquation (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) :
    (TriangularResidual.residual (shiftEquation base center T) (List.ofFn coordinates)).coeff 0 =
      T.eval₂ base (Fin.cases (base center) coordinates) := by
  rw [TriangularResidual.residual_constant, eval_shiftEquation]
  simp only [RingHom.id_comp, RingHom.id_apply, Fin.cases_zero, zero_add, Fin.cases_succ]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    change (List.ofFn coordinates).getD j.val 0 = coordinates j
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]


/-- Derive every used binomial unit from actual characteristic evidence and the precision guard. -/
def binomialUnit (p r k : ℕ) [CharP E p] (base : E →+* A)
    (hrk : r < k) (hkp : k ≤ p) (n : Fin k) : Aˣ :=
  if hn : r < n.val then
    Units.map base.toMonoidHom (Units.mk0 (n.val.choose r : E) (by
      have hp : 0 < p := (Nat.zero_lt_of_lt hrk).trans_le hkp
      exact Polynomial.natCast_choose_ne_zero_of_lt_charP
        (CharP.char_prime_of_ne_zero E hp.ne') (n.isLt.trans_le hkp) hn.le))
  else 1

omit [BEq E] [LawfulBEq E] [BEq A] [LawfulBEq A] [Nontrivial A] in
/-- The derived unit contains the actual binomial coefficient. -/
theorem binomialUnit_value (p r k : ℕ) [CharP E p] (base : E →+* A)
    (hrk : r < k) (hkp : k ≤ p) (n : Fin k) (hn : r < n.val) :
    (binomialUnit p r k base hrk hkp n : A) = (n.val.choose r : A) := by
  simp [binomialUnit, hn]

variable [DecidableEq A]

/-- Check the initial root and a supplied separant inverse before producing recurrence input.
The inverse is normally the output of the chart's existing local inverse computation. -/
def prepare? (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A) :
    Option (TriangularRecurrence.Input A r k) :=
  if hg : r < k ∧ k ≤ p then
    let equation := shiftEquation base center T
    let initial := List.ofFn coordinates
    let s := TriangularResidual.separant equation initial
    if hs : s * inverse = 1 then
      if hz : (TriangularResidual.residual equation initial).coeff 0 = 0 then
        some {
          equation := equation
          coordinates := coordinates
          order_lt := hg.1
          separantUnit := ⟨s, inverse, hs, by rw [mul_comm]; exact hs⟩
          separant_value := rfl
          binomialUnits := binomialUnit p r k base hg.1 hg.2
          binomial_values := binomialUnit_value p r k base hg.1 hg.2
          initial_zero := hz }
      else none
    else none
  else none

omit [BEq E] [LawfulBEq E] in
/-- Checked preparation retains the shifted equation and every initial coordinate. -/
theorem prepare?_data (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A)
    (P : TriangularRecurrence.Input A r k)
    (hP : prepare? p r k base center T coordinates inverse = some P) :
    P.equation = shiftEquation base center T ∧ P.coordinates = coordinates := by
  unfold prepare? at hP
  split at hP
  · dsimp only at hP
    split at hP
    · split at hP
      · cases hP
        exact ⟨rfl, rfl⟩
      · simp at hP
    · simp at hP
  · simp at hP

omit [BEq E] [LawfulBEq E] in
/-- Actual root and inverse identities make the executable preparation check succeed. -/
theorem prepare?_exists (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A)
    (hg : r < k ∧ k ≤ p)
    (hs : TriangularResidual.separant (shiftEquation base center T)
      (List.ofFn coordinates) * inverse = 1)
    (hz : T.eval₂ base (Fin.cases (base center) coordinates) = 0) :
    ∃ P, prepare? p r k base center T coordinates inverse = some P := by
  have hzero := (initial_residual_shiftEquation base center T coordinates).trans hz
  simp only [prepare?, dif_pos hg, dif_pos hs, dif_pos hzero]
  exact ⟨_, rfl⟩

omit [BEq E] [LawfulBEq E] in
/-- The prepared run solves the original equation at precisely the finite residual precision. -/
theorem prepare?_run_residual (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A)
    (P : TriangularRecurrence.Input A r k)
    (hP : prepare? p r k base center T coordinates inverse = some P) :
    ∀ m < k - r,
      (Global.ringResidual base center (TriangularResidual.polynomial P.run).toPoly
        (semanticEquation T)).coeff m = 0 := by
  intro m hm
  rw [← residual_shiftEquation, ← CPolynomial.coeff_toPoly,
    ← (prepare?_data p r k base center T coordinates inverse P hP).1]
  simpa only [CPolynomial.coeff_zero] using P.run_residual m hm

omit [BEq E] [LawfulBEq E] in
/-- Every accepted preparation satisfies the characteristic and precision guards. -/
theorem prepare?_guards (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A)
    (P : TriangularRecurrence.Input A r k)
    (hP : prepare? p r k base center T coordinates inverse = some P) : r < k ∧ k ≤ p := by
  unfold prepare? at hP
  split at hP
  · assumption
  · simp at hP

omit [BEq E] [LawfulBEq E] in
/-- Literal clearing provenance for the executed recurrence over the supplied algebra. -/
theorem prepare?_run_provenance (p r k : ℕ) [CharP E p] (base : E →+* A) (center : E)
    (T : CMvPolynomial (r + 2) E) (coordinates : Fin (r + 1) → A) (inverse : A)
    (P : TriangularRecurrence.Input A r k)
    (hP : prepare? p r k base center T coordinates inverse = some P) (j : Fin k) :
    MvPolynomial.eval₂ base coordinates
      (commonTaylorNumerator center (semanticEquation T) k j) =
      MvPolynomial.eval₂ base coordinates (initialJetSeparant center (semanticEquation T)) ^
        (2 * k) * P.run.getD j.val 0 := by
  obtain ⟨hrk, hkp⟩ := prepare?_guards p r k base center T coordinates inverse P hP
  have hp : 0 < p := (Nat.zero_lt_of_lt hrk).trans_le hkp
  have hbin : ∀ l < k, r < l → (l.choose r : E) ≠ 0 := by
    intro l hl hr
    exact Polynomial.natCast_choose_ne_zero_of_lt_charP
      (CharP.char_prime_of_ne_zero E hp.ne') (hl.trans_le hkp) hr.le
  have hzero : ∀ l < k, r < l →
      (Global.ringResidual base center (TriangularResidual.polynomial P.run).toPoly
        (semanticEquation T)).coeff (l - r) = 0 := by
    intro l hl hr
    exact prepare?_run_residual p r k base center T coordinates inverse P hP (l - r) (by omega)
  have he := Global.commonTaylorNumerator_of_ringResidual base center
    (TriangularResidual.polynomial P.run).toPoly (semanticEquation T) k hbin hzero j
  have hc : (fun i : Fin (r + 1) =>
      (TriangularResidual.polynomial P.run).toPoly.coeff i.val) = coordinates := by
    funext i
    rw [← CPolynomial.coeff_toPoly, TriangularResidual.coeff_polynomial, P.run_initial,
      (prepare?_data p r k base center T coordinates inverse P hP).2]
  rw [hc, ← CPolynomial.coeff_toPoly, TriangularResidual.coeff_polynomial] at he
  exact he

end ReedSolomon.HiddenDerivative.FastTaylor.TriangularPreparation
