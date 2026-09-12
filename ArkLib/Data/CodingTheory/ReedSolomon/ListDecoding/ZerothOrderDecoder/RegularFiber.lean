/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.CenterSearch
public import Mathlib.RingTheory.Localization.FractionRing
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv

/-!
# Characteristic-free decoding at an already checked regular fiber

The initial fiber is monically normalized directly, then lifted by ordinary quotient Newton
and consumed by arbitrary-base agreement recovery. The exactness theorem is an intermediate
adapter: normalization of the global equation and production of a good center remain upstream.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.RegularFiber

open CompPoly Polynomial ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

variable {E : Type*} [Field E]

private theorem derivative_eval₂_section (center : E) (Q : MvPolynomial (Fin 2) E) :
    (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C center, Polynomial.X] Q).derivative =
      MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C center, Polynomial.X]
        (MvPolynomial.pderiv 1 Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [MvPolynomial.coe_eval₂Hom] at hP hQ ⊢
      simp [hP, hQ]
  | mul_X P i hP =>
      simp only [MvPolynomial.coe_eval₂Hom] at hP ⊢
      fin_cases i <;> simp [Polynomial.derivative_mul, hP, mul_comm]

variable [BEq E] [LawfulBEq E]

/-- The computed slope is the derivative of the literal initial fiber. -/
theorem slope_toPoly (Q : CPoly.CMvPolynomial 2 E) (center : E) :
    (slope Q center).toPoly = (sectionPolynomial Q center).toPoly.derivative := by
  have hsection : (sectionPolynomial Q center).toPoly =
      MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C center, Polynomial.X]
        (CPoly.fromCMvPolynomial Q) := by
    change CPolynomial.toPolyRingHom (sectionPolynomial Q center) = _
    rw [sectionPolynomial, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
    simp only [MvPolynomial.coe_eval₂Hom]
    congr 1
    · ext a
      simp [CPolynomial.C_toPoly]
    · funext i
      fin_cases i <;> simp [CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  rw [hsection, derivative_eval₂_section]
  let L := FractionRing (Polynomial E)
  let φ : Polynomial E →+* L := algebraMap (Polynomial E) L
  let base : E →+* L := φ.comp Polynomial.C
  have he : Polynomial.eval₂RingHom base (φ Polynomial.X) = φ := by
    ext a <;> simp [base]
  apply IsFractionRing.injective (Polynomial E) L
  change φ _ = φ _
  rw [← he, Polynomial.coe_eval₂RingHom, eval₂_slope]
  rw [← Polynomial.coe_eval₂RingHom, he, MvPolynomial.map_eval₂Hom]
  congr 1
  funext i
  fin_cases i <;> simp [base]

/-- Normalize only by the nonzero leading scalar; no support extraction or root enumeration. -/
def modulus (Q : CPoly.CMvPolynomial 2 E) (center : E) : CPolynomial E :=
  CPolynomial.monicNormalize (sectionPolynomial Q center)

/-- A checked fiber already has all three properties needed by ordinary lifting and recovery. -/
theorem modulus_properties (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hgood : goodCenter Q center = true) :
    (modulus Q center).toPoly.Monic ∧ Squarefree (modulus Q center).toPoly ∧
      IsCoprime (slope Q center).toPoly (modulus Q center).toPoly := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  obtain ⟨hne, _, hinv⟩ := (goodCenter_iff Q center).mp hgood
  have hc := (CPolynomial.inverseMod_exists_iff_coprime _ _).mp hinv
  have hs : Squarefree (sectionPolynomial Q center).toPoly := by
    apply Polynomial.Separable.squarefree
    rw [Polynomial.separable_def, ← slope_toPoly]
    exact hc.symm
  have hd : (modulus Q center).toPoly ∣ (sectionPolynomial Q center).toPoly := by
    rw [modulus, CPolynomial.monicNormalize_toPoly_eq_normalize]
    exact (normalize_associated _).dvd
  refine ⟨?_, hs.squarefree_of_dvd hd, hc.of_isCoprime_of_dvd_right hd⟩
  rw [modulus, CPolynomial.monicNormalize_toPoly_eq_normalize]
  exact Polynomial.monic_normalize ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hne)

/-- Reject an unchecked center explicitly; otherwise execute ordinary quotient Newton. -/
def representations? (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ) :
    Option (List (FiniteRepresentation E)) :=
  if goodCenter Q center then
    (newtonLift? Q center (modulus Q center) k).map fun series =>
      [materialize (modulus Q center) center k series]
  else none

/-- At a checked center the actual inverse guard and representation producer both succeed. -/
theorem representations?_success (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ)
    (hgood : goodCenter Q center = true) :
    ∃ series, newtonLift? Q center (modulus Q center) k = some series ∧
      representations? Q center k = some [materialize (modulus Q center) center k series] := by
  obtain ⟨series, hs⟩ := newtonLift_exists Q center (modulus Q center) k
    (modulus_properties Q center hgood).2.2
  exact ⟨series, hs, by simp [representations?, hgood, hs]⟩

/-- All emitted data satisfy the recovery contract, even when no graph premise is supplied. -/
theorem representations?_wellFormed {Q : CPoly.CMvPolynomial 2 E} {center : E} {k : ℕ}
    {rs : List (FiniteRepresentation E)} (hrun : representations? Q center k = some rs) :
    ∀ rep ∈ rs, rep.WellFormed k := by
  unfold representations? at hrun
  split at hrun
  · rename_i hg
    cases hn : newtonLift? Q center (modulus Q center) k with
    | none => simp [hn] at hrun
    | some series =>
      simp only [hn, Option.map_some, Option.some.injEq] at hrun
      subst rs
      intro rep hrep
      simp only [List.mem_singleton] at hrep
      subst rep
      have hp := modulus_properties Q center hg
      exact materialize_wellFormed _ center k _ hp.1 hp.2.1
  · simp at hrun

/-- Run arbitrary-base agreement recovery on the actual emitted representation. -/
def run? {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (Q : CPoly.CMvPolynomial 2 E) (center : E) : Option (List (List F)) :=
  (representations? Q center k).map (AgreementRecovery.decode base domain received k A)

/-- Scalar normalization retains every geometric root of the original section. -/
theorem modulus_root_of_section_root {L : Type*} [Field L] (ι : E →+* L) (value : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hroot : (sectionPolynomial Q center).toPoly.eval₂ ι value = 0) :
    (modulus Q center).toPoly.eval₂ ι value = 0 := by
  let : DecidableEq E := instDecidableEqOfLawfulBEq
  rw [modulus, CPolynomial.monicNormalize_toPoly_eq_normalize, normalize_apply,
    Polynomial.eval₂_mul, hroot, zero_mul]

/-- A checked center gives one executed representation covering every degree-bounded solution. -/
theorem representation_covers_solution {L : Type*} [Field L] (ι : E →+* L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ)
    (hgood : goodCenter Q center = true) (series : Series E)
    (hrun : newtonLift? Q center (modulus Q center) k = some series)
    (P : Polynomial L) (hdegree : P.degree < k)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P]
      (CPoly.fromCMvPolynomial Q) = 0) :
    (materialize (modulus Q center) center k series).Represents ι (P.eval (ι center)) P := by
  apply newtonLifted_represents_solution ι Q center _
    (modulus_properties Q center hgood).1 k series hrun P hdegree _ hsolution
  apply modulus_root_of_section_root
  rw [eval₂_sectionPolynomial]
  exact solution_at_center ι (CPoly.fromCMvPolynomial Q) P (ι center) hsolution

/-- Intermediate exact-output adapter for a supplied normalized equation and checked center.
The equation graph premise is an upstream normalization obligation, not a completed decoder. -/
theorem run?_exact {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hgood : goodCenter Q center = true)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial Q) = 0) :
    ∃ output, run? base domain received k A Q center = some output ∧
      ExactOutput domain received k A output := by
  obtain ⟨series, hs, hr⟩ := representations?_success Q center k hgood
  let rs := [materialize (modulus Q center) center k series]
  refine ⟨AgreementRecovery.decode base domain received k A rs, by simp [run?, hr, rs], ?_⟩
  apply AgreementRecovery.decode_exact_of_coverage base (RingHom.id E) domain received k A hAk
    rs (representations?_wellFormed hr)
  intro P hP
  refine ⟨materialize (modulus Q center) center k series, by simp [rs],
    (P.map base).eval center, ?_⟩
  have hd : (P.map base).degree < k := by
    simpa only [Polynomial.degree_map_eq_of_injective base.injective] using hP.1
  simpa using representation_covers_solution (RingHom.id E) Q center k hgood series hs
    (P.map base) hd (by simpa using hsolutions P hP.1 hP.2)

end ReedSolomon.ListDecoding.ZerothOrderDecoder.RegularFiber
