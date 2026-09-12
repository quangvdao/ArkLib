/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization
public import Mathlib.RingTheory.Polynomial.Radical
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Multiplicity certificates for saturated ordinary normalization

This file gives the proof-facing interface for one executed saturation step.  The certificate is
tied to the result returned by `OrdinaryNormalization.saturate`; its radical statement lives over
`F(X)[Y]`, where the executed gcds are computed.  Factorizations remain noncomputable proof data
and are never supplied to the executable normalizer.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity

open CompPoly CPolynomial CPoly
open UniqueFactorizationMonoid
open OrdinaryNormalization

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- Polynomial radical with the proof-only normalization choice hidden from clients. -/
noncomputable def polynomialRadical {K : Type*} [Field K] (f : Polynomial K) : Polynomial K := by
  letI : DecidableEq K := Classical.decEq K
  exact UniqueFactorizationMonoid.radical f

/-- The repeated-factor quotient with the same hidden Euclidean normalization choice as
`polynomialRadical`. -/
noncomputable def polynomialDivRadical {K : Type*} [Field K]
    (f : Polynomial K) : Polynomial K := by
  letI : DecidableEq K := Classical.decEq K
  exact EuclideanDomain.divRadical f

/-- Global radical over `F[X][Y]`, with its proof-only UFD normalization kept local. -/
noncomputable def globalRadical (f : Polynomial (Polynomial F)) : Polynomial (Polynomial F) := by
  letI : StrongNormalizationMonoid (Polynomial (Polynomial F)) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  exact UniqueFactorizationMonoid.radical f

/-- The repeated-factor quotient divides the output of every derivation.  This is the
derivation-independent form of the usual fact that `f / radical f` divides `f'`. -/
theorem divRadical_dvd_derivation {K : Type*} [Field K] [DecidableEq K]
    (D : Derivation ℤ (Polynomial K) (Polynomial K)) (f : Polynomial K) :
    EuclideanDomain.divRadical f ∣ D f := by
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun g : Polynomial K => EuclideanDomain.divRadical g ∣ D g)
    f ?_ ?_ ?_ ?_
  · simp
  · intro u hu
    exact (EuclideanDomain.divRadical_isUnit hu).dvd
  · intro q i hq
    cases i with
    | zero => simp
    | succ i =>
        rw [← mul_dvd_mul_iff_left UniqueFactorizationMonoid.radical_ne_zero,
          EuclideanDomain.radical_mul_divRadical,
          UniqueFactorizationMonoid.radical_pow_of_prime hq (Nat.succ_ne_zero i),
          Derivation.leibniz_pow]
        have hbase : q ^ i * q ∣ q ^ i * normalize q :=
          mul_dvd_mul_left _ (normalize_associated q).symm.dvd
        simpa [Nat.add_sub_cancel, nsmul_eq_mul, pow_succ, mul_assoc, mul_comm,
          mul_left_comm] using hbase.mul_right ((i + 1 : Polynomial K) * D q)
  · intro a b hab ha hb
    have hc : IsCoprime a b :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨ha0, hb0⟩ => not_isUnit_zero (hab (zero_dvd_iff.mpr ha0)
          (zero_dvd_iff.mpr hb0)))
        fun q hq _ hqa hqb => hq (hab hqa hqb)
    rw [EuclideanDomain.divRadical_mul hc, Derivation.leibniz]
    simpa [mul_comm, add_comm] using dvd_add
      (mul_dvd_mul (EuclideanDomain.divRadical_dvd_self a) hb)
      (mul_dvd_mul ha (EuclideanDomain.divRadical_dvd_self b))

/-- A factor of order `n` in an input has order at least `n - 1` after applying any
derivation.  This is the local multiplicity inequality behind both partial derivatives. -/
theorem pow_sub_one_dvd_derivation_of_pow_dvd {R : Type*} [CommRing R]
    (D : Derivation ℤ R R) {q f : R} {n : ℕ} (h : q ^ n ∣ f) :
    q ^ (n - 1) ∣ D f := by
  cases n with
  | zero => simp
  | succ n =>
      obtain ⟨g, rfl⟩ := h
      rw [Derivation.leibniz, Derivation.leibniz_pow]
      apply dvd_add
      · exact dvd_mul_of_dvd_left (pow_dvd_pow q (Nat.le_succ n)) _
      · apply dvd_mul_of_dvd_right
        refine ⟨(n + 1 : R) * D q, ?_⟩
        simp only [Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring

/-- If the repeated-factor quotient of `A` is already contained in a divisor `C`, then the
complementary factor `V` in `A ∼ V * C` is supported on the radical of `A`. -/
theorem dvd_radical_of_divRadical_dvd_complement {K : Type*} [Field K] [DecidableEq K]
    {A V C : Polynomial K} (hA : A ≠ 0) (hVC : Associated (V * C) A)
    (hrepeated : EuclideanDomain.divRadical A ∣ C) :
    V ∣ UniqueFactorizationMonoid.radical A := by
  obtain ⟨t, ht⟩ := hrepeated
  have hassoc : Associated
      (EuclideanDomain.divRadical A * (V * t))
      (EuclideanDomain.divRadical A * UniqueFactorizationMonoid.radical A) := by
    have hfactor : Associated (V * C)
        (UniqueFactorizationMonoid.radical A * EuclideanDomain.divRadical A) :=
      hVC.trans (Associated.of_eq EuclideanDomain.radical_mul_divRadical).symm
    simpa [ht, mul_comm, mul_left_comm, mul_assoc] using hfactor
  have hcancel : Associated (V * t) (UniqueFactorizationMonoid.radical A) :=
    Associated.of_mul_left hassoc Associated.rfl
      (EuclideanDomain.divRadical_ne_zero hA)
  exact (dvd_mul_right V t).trans hcancel.dvd

/-- The complementary factor in the preceding lemma is squarefree. -/
theorem squarefree_of_divRadical_dvd_complement {K : Type*} [Field K] [DecidableEq K]
    {A V C : Polynomial K} (hA : A ≠ 0) (hVC : Associated (V * C) A)
    (hrepeated : EuclideanDomain.divRadical A ∣ C) : Squarefree V :=
  UniqueFactorizationMonoid.squarefree_radical.squarefree_of_dvd
    (dvd_radical_of_divRadical_dvd_complement hA hVC hrepeated)

/-- In a UFD, every quotient left after removing one copy of each irreducible factor divides
the output of any derivation.  The quotient is supplied by its exact product identity, so this
lemma also applies in non-Euclidean UFDs such as `F[X][Y]`. -/
theorem radical_complement_dvd_derivation {R : Type*} [CommRing R] [IsDomain R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R]
    (D : Derivation ℤ R R) (f d : R)
    (hfd : UniqueFactorizationMonoid.radical f * d = f) : d ∣ D f := by
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun g : R => ∀ e, UniqueFactorizationMonoid.radical g * e = g → e ∣ D g)
    f ?_ ?_ ?_ ?_ d hfd
  · intro e he
    simp only [UniqueFactorizationMonoid.radical_zero, one_mul] at he
    subst e
    simp
  · intro u hu e he
    rw [UniqueFactorizationMonoid.radical_of_isUnit hu, one_mul] at he
    subst e
    exact hu.dvd
  · intro q i hq e he
    cases i with
    | zero =>
        simp only [pow_zero, UniqueFactorizationMonoid.radical_one, one_mul] at he
        subst e
        simp
    | succ i =>
        rw [UniqueFactorizationMonoid.radical_pow_of_prime hq (Nat.succ_ne_zero i)] at he
        have heassoc : Associated e (q ^ i) := by
          have hmul : Associated (normalize q * e) (q * q ^ i) :=
            Associated.of_eq (by simpa [pow_succ', mul_comm] using he)
          exact Associated.of_mul_left hmul (normalize_associated q)
            (normalize_eq_zero.not.mpr hq.ne_zero)
        exact heassoc.dvd.trans
          (pow_sub_one_dvd_derivation_of_pow_dvd D (dvd_refl (q ^ (i + 1))))
  · intro a b hab ha hb e he
    obtain ⟨da, hda⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := a)
    obtain ⟨db, hdb⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := b)
    have hdaD : da ∣ D a := ha da hda.symm
    have hdbD : db ∣ D b := hb db hdb.symm
    have heassoc : Associated e (da * db) := by
      rw [UniqueFactorizationMonoid.radical_mul hab] at he
      have heq :
          (UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b) * e =
            (UniqueFactorizationMonoid.radical a * UniqueFactorizationMonoid.radical b) *
              (da * db) := by
        calc
          _ = a * b := he
          _ = (UniqueFactorizationMonoid.radical a * da) *
              (UniqueFactorizationMonoid.radical b * db) :=
            congrArg₂ (fun x y : R => x * y) hda hdb
          _ = _ := by ring
      exact Associated.of_mul_left (Associated.of_eq heq) Associated.rfl
        (mul_ne_zero UniqueFactorizationMonoid.radical_ne_zero
          UniqueFactorizationMonoid.radical_ne_zero)
    have hdvdA : da ∣ a := ⟨UniqueFactorizationMonoid.radical a, by
      simpa [mul_comm] using hda⟩
    have hdvdB : db ∣ b := ⟨UniqueFactorizationMonoid.radical b, by
      simpa [mul_comm] using hdb⟩
    rw [Derivation.leibniz]
    exact heassoc.dvd.trans (dvd_add (mul_dvd_mul hdvdA hdbD)
      (by simpa [mul_comm] using mul_dvd_mul hdaD hdvdB))

/-- Coefficientwise `X` differentiation as a derivation of the global ring `F[X][Y]`. -/
noncomputable def partialDerivXDerivation :
    Derivation ℤ (Polynomial (Polynomial F)) (Polynomial (Polynomial F)) := by
  let inner : Derivation ℤ (Polynomial F) (Polynomial F) :=
    Polynomial.derivative'.restrictScalars ℤ
  exact PolynomialModule.equivPolynomialSelf.compDer inner.mapCoeffs

/-- Outer-variable `Y` differentiation as a derivation of the global ring `F[X][Y]`. -/
noncomputable def partialDerivYDerivation :
    Derivation ℤ (Polynomial (Polynomial F)) (Polynomial (Polynomial F)) :=
  Polynomial.derivative'.restrictScalars ℤ

theorem partialDerivXDerivation_apply (H : CBivariate F) :
    partialDerivXDerivation (F := F) (CBivariate.toPoly H) =
      CBivariate.toPoly (CBivariate.partialDerivX H) := by
  apply Polynomial.ext
  intro j
  rw [CBivariate.partialDerivX_toPoly]
  rfl

theorem partialDerivYDerivation_apply (H : CBivariate F) :
    partialDerivYDerivation (F := F) (CBivariate.toPoly H) =
      CBivariate.toPoly (CBivariate.partialDerivY H) := by
  change Polynomial.derivative (CBivariate.toPoly H) = _
  exact (CBivariate.partialDerivY_toPoly H).symm

/-- A nonzero coefficientwise X derivative strictly lowers the bivariate X degree. -/
theorem degreeX_partialDerivX_lt {R : CBivariate F}
    (hpartial : CBivariate.partialDerivX R ≠ 0) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly (CBivariate.partialDerivX R)) <
      Polynomial.Bivariate.degreeX (CBivariate.toPoly R) := by
  classical
  let Q := CBivariate.toPoly (CBivariate.partialDerivX R)
  let P := CBivariate.toPoly R
  have hQ : Q ≠ 0 := by
    intro hz
    apply hpartial
    calc
      CBivariate.partialDerivX R = CBivariate.ofPoly Q :=
        (CBivariate.toPoly_ofPoly (CBivariate.partialDerivX R)).symm
      _ = CBivariate.ofPoly 0 := congrArg CBivariate.ofPoly hz
      _ = 0 := CBivariate.ofPoly_zero
  have hsupp : Q.support.Nonempty := by
    exact ⟨Q.natDegree, Polynomial.natDegree_mem_support_of_nonzero hQ⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (s := Q.support) hsupp
    (fun n => (Q.coeff n).natDegree)
  have hcoeffQ : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hderivative : Polynomial.derivative (P.coeff j) ≠ 0 := by
    simpa only [Q, P, CBivariate.partialDerivX_toPoly] using hcoeffQ
  have hdegreeCoeff : (P.coeff j).natDegree ≠ 0 := by
    intro hz
    exact hderivative (Polynomial.derivative_of_natDegree_zero hz)
  have hcoeffEq : Q.coeff j = Polynomial.derivative (P.coeff j) := by
    exact CBivariate.partialDerivX_toPoly R j
  have hlt : (Q.coeff j).natDegree < (P.coeff j).natDegree := by
    rw [hcoeffEq]
    exact Polynomial.natDegree_derivative_lt hdegreeCoeff
  have hjP : j ∈ P.support := by
    rw [Polynomial.mem_support_iff]
    intro hz
    apply hderivative
    rw [hz, Polynomial.derivative_zero]
  have hle : (P.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX P := by
    unfold Polynomial.Bivariate.degreeX
    exact Finset.le_sup (f := fun n => (P.coeff n).natDegree) hjP
  change Polynomial.Bivariate.degreeX Q < Polynomial.Bivariate.degreeX P
  unfold Polynomial.Bivariate.degreeX
  rw [hmax]
  exact hlt.trans_le hle

/-- Consequently a bivariate polynomial cannot divide its nonzero X derivative. -/
theorem not_dvd_partialDerivX_of_ne_zero {R : CBivariate F}
    (hpartial : CBivariate.partialDerivX R ≠ 0) :
    ¬CBivariate.toPoly R ∣ CBivariate.toPoly (CBivariate.partialDerivX R) := by
  intro hdvd
  have hle := Polynomial.Bivariate.degreeX_le_of_dvd hdvd (by
    intro hz
    apply hpartial
    calc
      CBivariate.partialDerivX R =
          CBivariate.ofPoly (CBivariate.toPoly (CBivariate.partialDerivX R)) :=
        (CBivariate.toPoly_ofPoly (CBivariate.partialDerivX R)).symm
      _ = CBivariate.ofPoly 0 := congrArg CBivariate.ofPoly hz
      _ = 0 := CBivariate.ofPoly_zero)
  exact (Nat.not_le_of_lt (degreeX_partialDerivX_lt hpartial)) hle


/-- Multiplicity in a gcd is the minimum of the two multiplicities.  The extended-valued
statement also covers a zero derivative, whose multiplicity is infinite. -/
theorem emultiplicity_gcd_eq_min {R : Type*} [CommMonoidWithZero R] [GCDMonoid R]
    (q a b : R) :
    emultiplicity q (gcd a b) = min (emultiplicity q a) (emultiplicity q b) := by
  apply le_antisymm
  · exact le_min
      (emultiplicity_le_emultiplicity_of_dvd_right (gcd_dvd_left a b))
      (emultiplicity_le_emultiplicity_of_dvd_right (gcd_dvd_right a b))
  · by_cases hab : emultiplicity q a ≤ emultiplicity q b
    · rw [min_eq_left hab, emultiplicity_le_emultiplicity_iff]
      intro n hn
      exact dvd_gcd hn
        (pow_dvd_of_le_emultiplicity
          ((le_emultiplicity_of_pow_dvd hn).trans hab))
    · have hba : emultiplicity q b ≤ emultiplicity q a := le_of_not_ge hab
      rw [min_eq_right hba, emultiplicity_le_emultiplicity_iff]
      intro n hn
      exact dvd_gcd
        (pow_dvd_of_le_emultiplicity
          ((le_emultiplicity_of_pow_dvd hn).trans hba)) hn

/-- A primitive squarefree polynomial over `F[X]` remains squarefree over `F(X)`. -/
theorem squarefree_fraction_map {S : Polynomial (Polynomial F)}
    (hprimitive : S.IsPrimitive) (hsquarefree : Squarefree S) :
    Squarefree (S.map (algebraMap (Polynomial F) (RatFunc F))) := by
  classical
  intro d hdsq
  by_cases hdzero : d = 0
  · subst d
    exfalso
    have hmapzero : S.map (algebraMap (Polynomial F) (RatFunc F)) = 0 := by
      simpa only [MulZeroClass.zero_mul, zero_dvd_iff] using hdsq
    exact (Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr
      hprimitive.ne_zero hmapzero
  let A : Polynomial (Polynomial F) :=
    IsLocalization.integerNormalization (nonZeroDivisors (Polynomial F)) d
  let P : Polynomial (Polynomial F) := A.primPart
  obtain ⟨c, hc, hAmap⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial F)) d
  rw [Algebra.smul_def] at hAmap
  have hscalar : algebraMap (Polynomial F) (Polynomial (RatFunc F)) c =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) (RatFunc F)
      (Polynomial (RatFunc F))]
    rfl
  rw [hscalar] at hAmap
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hCunit : IsUnit
      (Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (RatFunc.algebraMap_ne_zero hc0))
  have hA : A ≠ 0 := by
    intro hz
    change A.map (algebraMap (Polynomial F) (RatFunc F)) =
      Polynomial.C (algebraMap (Polynomial F) (RatFunc F) c) * d at hAmap
    rw [hz, Polynomial.map_zero] at hAmap
    exact hdzero (mul_eq_zero.mp hAmap.symm |>.resolve_left
      (Polynomial.C_ne_zero.mpr (RatFunc.algebraMap_ne_zero hc0)))
  have hcontent : A.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hA
  have hcontentUnit : IsUnit
      (Polynomial.C (algebraMap (Polynomial F) (RatFunc F) A.content)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (RatFunc.algebraMap_ne_zero hcontent))
  have hPA : Associated
      (P.map (algebraMap (Polynomial F) (RatFunc F)))
      (A.map (algebraMap (Polynomial F) (RatFunc F))) := by
    have heq := congrArg
      (Polynomial.map (algebraMap (Polynomial F) (RatFunc F)))
      A.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, Polynomial.map_C] at heq
    exact (associated_unit_mul_left _ _ hcontentUnit).symm.trans
      (Associated.of_eq heq.symm)
  have hAd : Associated (A.map (algebraMap (Polynomial F) (RatFunc F))) d :=
    (Associated.of_eq hAmap).trans (associated_unit_mul_left d _ hCunit)
  have hPd : Associated (P.map (algebraMap (Polynomial F) (RatFunc F))) d := hPA.trans hAd
  have hPPmap : (P * P).map (algebraMap (Polynomial F) (RatFunc F)) ∣
      S.map (algebraMap (Polynomial F) (RatFunc F)) := by
    rw [Polynomial.map_mul]
    exact (hPd.mul_mul hPd).dvd.trans hdsq
  have hPP : P * P ∣ S :=
    (Polynomial.isPrimitive_primPart A).mul (Polynomial.isPrimitive_primPart A)
      |>.dvd_of_fraction_map_dvd_fraction_map hPPmap
  have hPunit : IsUnit P := hsquarefree P hPP
  exact hPd.isUnit (hPunit.map
    (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F))))

/-- Localization commutes with the element radical up to a unit for primitive global
polynomials. -/
theorem radical_fraction_map_associated {S : Polynomial (Polynomial F)}
    (hprimitive : S.IsPrimitive) :
    Associated
      ((globalRadical S).map
        (algebraMap (Polynomial F) (RatFunc F)))
      (polynomialRadical
        (S.map (algebraMap (Polynomial F) (RatFunc F)))) := by
  classical
  let r := globalRadical S
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hS0 : S ≠ 0 := hprimitive.ne_zero
  have hrDvd : r ∣ S := by
    unfold r globalRadical
    exact UniqueFactorizationMonoid.radical_dvd_self
  have hrprimitive : r.IsPrimitive := Polynomial.isPrimitive_of_dvd hprimitive hrDvd
  have hrsquarefree : Squarefree r := by
    unfold r globalRadical
    exact UniqueFactorizationMonoid.squarefree_radical
  have hmapSquarefree : Squarefree (r.map φ) :=
    squarefree_fraction_map hrprimitive hrsquarefree
  have hmapRadical : IsRadical (r.map φ) := hmapSquarefree.isRadical
  have hr0 : r ≠ 0 := by
    unfold r globalRadical
    exact UniqueFactorizationMonoid.radical_ne_zero
  have hmapr0 : r.map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr hr0
  have hmapS0 : S.map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr hS0
  have hmaprDvdMapS : r.map φ ∣ S.map φ := by
    obtain ⟨d, hd⟩ := hrDvd
    refine ⟨d.map φ, ?_⟩
    simpa only [Polynomial.map_mul] using congrArg (Polynomial.map φ) hd
  have hrMapDvd : r.map φ ∣ polynomialRadical (S.map φ) := by
    unfold polynomialRadical
    exact (UniqueFactorizationMonoid.dvd_radical_iff hmapRadical hmapS0).mpr hmaprDvdMapS
  have hradDvdMap : polynomialRadical (S.map φ) ∣ r.map φ := by
    have hpow : ∃ n, S ∣ r ^ n := by
      unfold r globalRadical
      exact UniqueFactorizationMonoid.exists_dvd_radical_self_pow hS0
    obtain ⟨n, hn⟩ := hpow
    have hmapped : S.map φ ∣ (r.map φ) ^ n := by
      obtain ⟨t, ht⟩ := hn
      refine ⟨t.map φ, ?_⟩
      simpa only [Polynomial.map_mul, Polynomial.map_pow] using
        congrArg (Polynomial.map φ) ht
    have hlocalRadicalDvdMapS : polynomialRadical (S.map φ) ∣ S.map φ := by
      unfold polynomialRadical
      exact UniqueFactorizationMonoid.radical_dvd_self
    have hlocalRadicalPow : polynomialRadical (S.map φ) ∣ (r.map φ) ^ n :=
      hlocalRadicalDvdMapS.trans hmapped
    have hlocalRadical0 : polynomialRadical (S.map φ) ≠ 0 := by
      unfold polynomialRadical
      exact UniqueFactorizationMonoid.radical_ne_zero
    have hradRadicalDvd :
        UniqueFactorizationMonoid.radical (polynomialRadical (S.map φ)) ∣ r.map φ :=
      (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hlocalRadical0).mp
        ⟨n, hlocalRadicalPow⟩
    have hlocalIsRadical : IsRadical (polynomialRadical (S.map φ)) := by
      unfold polynomialRadical
      exact UniqueFactorizationMonoid.isRadical_radical
    exact (hlocalIsRadical.dvd_radical hlocalRadical0).trans hradRadicalDvd
  exact associated_of_dvd_dvd hrMapDvd hradDvdMap

/-- Mathematical polynomial represented by a stored bivariate polynomial after localization in
the coefficient variable. -/
noncomputable abbrev localized (H : CBivariate F) : Polynomial (RatFunc F) :=
  ClearDenominators.valueGlobal H

/-- Radical in the localized polynomial ring. -/
noncomputable def localizedRadical (H : CBivariate F) : Polynomial (RatFunc F) :=
  polynomialRadical (localized H)

/-- The repeated-factor quotient of a primitive input divides the actual nested gcd computed by
the saturation stage.  Both partial derivatives are handled globally before localization. -/
theorem localized_divRadical_dvd_saturationCommon (H : CBivariate F) (_hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive) :
    polynomialDivRadical (localized H) ∣
      localized (globalGcd H (globalGcd (CBivariate.partialDerivX H)
        (CBivariate.partialDerivY H))) := by
  classical
  let f := CBivariate.toPoly H
  let r := globalRadical f
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hradDvd : r ∣ f := by
    unfold r globalRadical
    exact UniqueFactorizationMonoid.radical_dvd_self
  obtain ⟨d, hd⟩ := hradDvd
  have hdx : d ∣ CBivariate.toPoly (CBivariate.partialDerivX H) := by
    rw [← partialDerivXDerivation_apply]
    exact radical_complement_dvd_derivation (partialDerivXDerivation (F := F)) f d hd.symm
  have hdy : d ∣ CBivariate.toPoly (CBivariate.partialDerivY H) := by
    rw [← partialDerivYDerivation_apply]
    exact radical_complement_dvd_derivation (partialDerivYDerivation (F := F)) f d hd.symm
  have hmapdx : d.map φ ∣ localized (CBivariate.partialDerivX H) := by
    obtain ⟨t, ht⟩ := hdx
    refine ⟨t.map φ, ?_⟩
    change (CBivariate.toPoly (CBivariate.partialDerivX H)).map φ = _
    rw [ht, Polynomial.map_mul]
  have hmapdy : d.map φ ∣ localized (CBivariate.partialDerivY H) := by
    obtain ⟨t, ht⟩ := hdy
    refine ⟨t.map φ, ?_⟩
    change (CBivariate.toPoly (CBivariate.partialDerivY H)).map φ = _
    rw [ht, Polynomial.map_mul]
  have hinner : d.map φ ∣ localized
      (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) := by
    apply (globalGcd_associated (CBivariate.partialDerivX H)
      (CBivariate.partialDerivY H)).dvd_iff_dvd_right.mpr
    exact EuclideanDomain.dvd_gcd hmapdx hmapdy
  have hmapH : d.map φ ∣ localized H := by
    refine ⟨(r.map φ), ?_⟩
    change f.map φ = d.map φ * r.map φ
    rw [hd, Polynomial.map_mul]
    ring
  have hcommon : d.map φ ∣ localized
      (globalGcd H (globalGcd (CBivariate.partialDerivX H)
        (CBivariate.partialDerivY H))) := by
    apply (globalGcd_associated H
      (globalGcd (CBivariate.partialDerivX H)
        (CBivariate.partialDerivY H))).dvd_iff_dvd_right.mpr
    exact EuclideanDomain.dvd_gcd hmapH hinner
  have hrAssoc : Associated (r.map φ) (localizedRadical H) := by
    change Associated (r.map φ) (polynomialRadical (f.map φ))
    exact radical_fraction_map_associated hprimitive
  have hprod : Associated
      (r.map φ * d.map φ)
      (localizedRadical H * polynomialDivRadical (localized H)) := by
    have hmapped : r.map φ * d.map φ = f.map φ := by
      simpa only [Polynomial.map_mul] using congrArg (Polynomial.map φ) hd.symm
    apply (Associated.of_eq hmapped).trans
    unfold localizedRadical polynomialRadical polynomialDivRadical
    exact (Associated.of_eq EuclideanDomain.radical_mul_divRadical).symm
  have hdAssoc : Associated (d.map φ) (polynomialDivRadical (localized H)) :=
    Associated.of_mul_left hprod hrAssoc
      ((Polynomial.map_ne_zero_iff (RatFunc.algebraMap_injective F)).mpr
        (by unfold r globalRadical; exact UniqueFactorizationMonoid.radical_ne_zero))
  exact hdAssoc.symm.dvd.trans hcommon

/-- A bounded squarefree support is coprime to the quotient left after the bounded gcd. -/
theorem boundedGcd_coprime {K : Type*} [Field K] [DecidableEq K]
    {ell : ℕ} {A V G R : Polynomial K}
    (hA : A ≠ 0) (hVdvdA : V ∣ A)
    (hmult : ∀ q : Polynomial K, Prime q → q ∣ A → multiplicity q A ≤ ell)
    (hG : Associated G (EuclideanDomain.gcd A (V ^ ell)))
    (hfactor : Associated (R * G) A) : IsCoprime V R := by
  have hV0 : V ≠ 0 := ne_zero_of_dvd_ne_zero hA hVdvdA
  apply EuclideanDomain.isCoprime_of_dvd
    (fun hzero => hV0 hzero.1)
  intro z hzNonunit hz0 hzV hzR
  obtain ⟨q, hqIrreducible, hqz⟩ :=
    WfDvdMonoid.exists_irreducible_factor hzNonunit hz0
  have hq : Prime q := irreducible_iff_prime.mp hqIrreducible
  have hqV : q ∣ V := hqz.trans hzV
  have hqR : q ∣ R := hqz.trans hzR
  let n := multiplicity q A
  have hqA : q ∣ A := hqV.trans hVdvdA
  have hnle : n ≤ ell := hmult q hq hqA
  have hqnA : q ^ n ∣ A := pow_multiplicity_dvd q A
  have hqnVell : q ^ n ∣ V ^ ell :=
    (pow_dvd_pow q hnle).trans (pow_dvd_pow_of_dvd hqV ell)
  have hqnG : q ^ n ∣ G :=
    hG.dvd_iff_dvd_right.mpr (EuclideanDomain.dvd_gcd hqnA hqnVell)
  have hqsuccRG : q ^ (n + 1) ∣ R * G := by
    simpa only [pow_succ, mul_comm q (q ^ n)] using mul_dvd_mul hqR hqnG
  have hqsuccA : q ^ (n + 1) ∣ A := hfactor.dvd_iff_dvd_right.mp hqsuccRG
  exact (FiniteMultiplicity.of_prime_left hq hA).not_pow_dvd_of_multiplicity_lt
    (Nat.lt_succ_self n) hqsuccA

/-- The bounded gcd removes exactly the support carried by `V`. -/
theorem boundedGcd_radical_split {K : Type*} [Field K] [DecidableEq K]
    {ell : ℕ} {A V G R : Polynomial K}
    (hA : A ≠ 0) (hVsf : Squarefree V) (hVdvdA : V ∣ A)
    (hmult : ∀ q : Polynomial K, Prime q → q ∣ A → multiplicity q A ≤ ell)
    (hG : Associated G (EuclideanDomain.gcd A (V ^ ell)))
    (hfactor : Associated (R * G) A) :
    IsCoprime V R ∧
      Associated (UniqueFactorizationMonoid.radical A)
        (V * UniqueFactorizationMonoid.radical R) := by
  have hcoprime := boundedGcd_coprime hA hVdvdA hmult hG hfactor
  have hV0 : V ≠ 0 := ne_zero_of_dvd_ne_zero hA hVdvdA
  have hRG0 : R * G ≠ 0 := by
    intro hz
    exact hA (hfactor.eq_zero_iff.mp hz)
  have hR0 : R ≠ 0 := left_ne_zero_of_mul hRG0
  have hG0 : G ≠ 0 := right_ne_zero_of_mul hRG0
  have hVunit_of_ell_zero : ell = 0 → IsUnit V := by
    intro hell
    by_contra hVunit
    obtain ⟨q, hqIrreducible, hqV⟩ :=
      WfDvdMonoid.exists_irreducible_factor hVunit hV0
    have hq : Prime q := irreducible_iff_prime.mp hqIrreducible
    have hqA : q ∣ A := hqV.trans hVdvdA
    have hpositive : 0 < multiplicity q A := multiplicity_pos_of_dvd hqA
    have hle := hmult q hq hqA
    omega
  have hVdvdPow : V ∣ V ^ ell := by
    cases ell with
    | zero => simpa only [pow_zero] using (hVunit_of_ell_zero rfl).dvd
    | succ n =>
      simpa only [pow_one] using
        (pow_dvd_pow V (Nat.succ_le_succ (Nat.zero_le n)))
  have hVdvdG : V ∣ G :=
    (EuclideanDomain.dvd_gcd hVdvdA hVdvdPow).trans hG.dvd'
  have hGdvdVpow : G ∣ V ^ ell :=
    hG.dvd.trans (EuclideanDomain.gcd_dvd_right A (V ^ ell))
  have hRGcoprime : IsCoprime R G :=
    (hcoprime.symm.pow_right).of_isCoprime_of_dvd_right hGdvdVpow
  have hVdvdRadG : V ∣ UniqueFactorizationMonoid.radical G :=
    (UniqueFactorizationMonoid.dvd_radical_iff hVsf.isRadical hG0).mpr hVdvdG
  have hRadGdvdV : UniqueFactorizationMonoid.radical G ∣ V := by
    cases ell with
    | zero =>
      have hGunit : IsUnit G := isUnit_iff_dvd_one.mpr hGdvdVpow
      rw [UniqueFactorizationMonoid.radical_of_isUnit hGunit]
      exact one_dvd V
    | succ n =>
      have hradDvd : UniqueFactorizationMonoid.radical G ∣
          UniqueFactorizationMonoid.radical (V ^ (n + 1)) :=
        UniqueFactorizationMonoid.radical_dvd_radical hGdvdVpow
          (pow_ne_zero _ hV0)
      rw [UniqueFactorizationMonoid.radical_pow V (Nat.succ_ne_zero n)] at hradDvd
      exact hradDvd.trans UniqueFactorizationMonoid.radical_dvd_self
  have hRadGAssocV : Associated (UniqueFactorizationMonoid.radical G) V :=
    associated_of_dvd_dvd hRadGdvdV hVdvdRadG
  have hRadProduct :
      UniqueFactorizationMonoid.radical (R * G) =
        UniqueFactorizationMonoid.radical R * UniqueFactorizationMonoid.radical G :=
    UniqueFactorizationMonoid.radical_mul hRGcoprime.isRelPrime
  refine ⟨hcoprime, ?_⟩
  have hAassocRG : Associated (UniqueFactorizationMonoid.radical A)
      (UniqueFactorizationMonoid.radical (R * G)) :=
    Associated.of_eq (UniqueFactorizationMonoid.radical_eq_of_associated hfactor).symm
  have hRGassoc : Associated (UniqueFactorizationMonoid.radical (R * G))
      (V * UniqueFactorizationMonoid.radical R) :=
    (Associated.of_eq hRadProduct).trans
      (((Associated.refl _).mul_mul hRadGAssocV).trans (Associated.of_eq (mul_comm _ _)))
  exact hAassocRG.trans hRGassoc

/-- The multiplicity of a prime factor of a nonzero polynomial over a field is bounded by the
polynomial's degree. -/
theorem prime_multiplicity_le_natDegree {K : Type*} [Field K]
    {A q : Polynomial K} (hA : A ≠ 0) (hq : Prime q) :
    multiplicity q A ≤ A.natDegree := by
  classical
  have hpow : q ^ multiplicity q A ∣ A := pow_multiplicity_dvd q A
  have hdeg := Polynomial.natDegree_le_of_dvd hpow hA
  rw [Polynomial.natDegree_pow] at hdeg
  exact (Nat.le_mul_of_pos_right _ (Irreducible.natDegree_pos hq.irreducible)).trans hdeg


/-- Full proof contract for one successful call of the executable saturation stage.

`visible` contains the factors whose multiplicities are detected by at least one partial
derivative.  `residual` contains the characteristic-divisible multiplicities.  The last three
fields are the recursive Radical interface: the two pieces are coprime, their radicals reconstruct
the radical of the input, and a nonconstant residual forces the characteristic below the supplied
degree bound. -/
structure SaturationCertificate (p ell : ℕ) [CharP F p] (inverse : F → F)
    (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) : Prop where
  execution : OrdinaryNormalization.saturate ell H = .ok step
  input_ne_zero : H ≠ 0
  input_primitive : (CBivariate.toPoly H).IsPrimitive
  degree_le : (CBivariate.toPoly H).natDegree ≤ ell
  inverse_law : p ≤ ell → ∀ a, inverse a ^ p = a
  visible_ne_zero : step.visible ≠ 0
  visible_squarefree : Squarefree (localized step.visible)
  residual_ne_zero : step.residual ≠ 0
  residual_partials : CBivariate.partialDerivX step.residual = 0 ∧
    CBivariate.partialDerivY step.residual = 0
  visible_coprime_residual : IsCoprime (localized step.visible) (localized step.residual)
  radical_split : Associated (localizedRadical H)
    (localized step.visible * localizedRadical step.residual)
  p_le_ell_of_residual_nonconstant :
    0 < (CBivariate.toPoly step.residual).natDegree → p ≤ ell

/-- An executed primitive quotient of a nonzero dividend is nonzero.  This is a global statement:
the proof uses the checked cross-product identity, so it remains valid before localization. -/
theorem quotientPrimitive_output_ne_zero (A B R : CBivariate F)
    (hA : A ≠ 0) (h : quotientPrimitive A B = some R) : R ≠ 0 := by
  classical
  obtain ⟨scale, content, hscale, _hcontent, hid⟩ :=
    quotientPrimitive_global_identity A B R h
  intro hR
  subst R
  simp only [CPolynomial.mul_zero] at hid
  have hglobalA : localized A ≠ 0 := by
    intro hzero
    apply hA
    apply CBivariate.ringEquiv.injective
    apply Polynomial.map_injective _ (RatFunc.algebraMap_injective F)
    change localized A = localized 0
    simpa only [ClearDenominators.valueGlobal_zero] using hzero
  have hscaleMap : algebraMap (Polynomial F) (RatFunc F) scale.toPoly ≠ 0 :=
    RatFunc.algebraMap_ne_zero hscale
  have hvalue := congrArg (ClearDenominators.valueGlobal (F := F)) hid
  rw [ClearDenominators.valueGlobal_zero, ClearDenominators.valueGlobal_mul,
    ClearDenominators.valueGlobal_C] at hvalue
  exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hscaleMap) hglobalA) hvalue.symm

/-- After localization, an executed primitive quotient is the exact quotient up to a unit. -/
theorem quotientPrimitive_localized_mul_associated (A B R : CBivariate F)
    (h : quotientPrimitive A B = some R) :
    Associated (localized R * localized B) (localized A) := by
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    have hprimitive := ClearDenominators.clear_primitive_associated q
    have hdivision := ((FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq).2
    rw [ClearDenominators.value_embed, ClearDenominators.value_embed] at hdivision
    exact (hprimitive.mul_right (localized B)).trans (Associated.of_eq hdivision)

/-- A primitive quotient that is locally coprime to its divisor inherits divisibility by its
own derivative from divisibility by the derivative of the dividend.  The proof differentiates
the global clearing identity, cancels the clearing scalar only after localization, and descends
the result by Gauss's lemma. -/
theorem quotientPrimitive_derivation_dvd_self
    (D : Derivation ℤ (Polynomial (Polynomial F)) (Polynomial (Polynomial F)))
    (A B R : CBivariate F) (hquot : quotientPrimitive A B = some R)
    (hR : R ≠ 0) (hcoprime : IsCoprime (localized R) (localized B))
    (hinput : CBivariate.toPoly R ∣ D (CBivariate.toPoly A)) :
    CBivariate.toPoly R ∣ D (CBivariate.toPoly R) := by
  classical
  let r := CBivariate.toPoly R
  let a := CBivariate.toPoly A
  let b := CBivariate.toPoly B
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hr0 : r ≠ 0 := by
    intro hr
    apply hR
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly R = CBivariate.toPoly 0
    simpa only [r, CBivariate.toPoly_zero] using hr
  have hrprimitive : r.IsPrimitive :=
    quotientPrimitive_isPrimitive A B R hquot hR
  have hrA : r ∣ a := quotientPrimitive_dvd_left_global A B R hquot hR
  obtain ⟨scale, content, hscale, hcontent, hid⟩ :=
    quotientPrimitive_global_identity A B R hquot
  let c := CBivariate.toPoly (CPolynomial.C content : CBivariate F)
  let s := CBivariate.toPoly (CPolynomial.C scale : CBivariate F)
  have hidpoly : c * b * r = s * a := by
    have hp := congrArg CBivariate.toPoly hid
    rw [CBivariate.toPoly_mul, CBivariate.toPoly_mul, CBivariate.toPoly_mul] at hp
    simpa only [c, b, r, s, a] using hp
  have htotal : r ∣ D (c * b * r) := by
    rw [hidpoly, Derivation.leibniz]
    exact dvd_add
      (by simpa only [smul_eq_mul] using dvd_mul_of_dvd_right hinput s)
      (by simpa only [smul_eq_mul, mul_comm] using dvd_mul_of_dvd_right hrA (D s))
  have hfirst : r ∣ D (c * b) * r := dvd_mul_left _ _
  have hlast : r ∣ (c * b) * D r := by
    rw [Derivation.leibniz] at htotal
    have hdiff := dvd_sub htotal hfirst
    convert hdiff using 1
    all_goals ring
  have hmapLast : r.map φ ∣ (c.map φ * b.map φ) * (D r).map φ := by
    obtain ⟨t, ht⟩ := hlast
    refine ⟨t.map φ, ?_⟩
    simpa only [Polynomial.map_mul] using congrArg (Polynomial.map φ) ht
  have hcEq : c.map φ = Polynomial.C (algebraMap (Polynomial F) (RatFunc F) content.toPoly) := by
    simp only [c, CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, Polynomial.map_C]
    congr 1
    exact congrArg φ (CPolynomial.ringEquiv_apply content)
  have hcUnit : IsUnit (c.map φ) := by
    rw [hcEq]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (RatFunc.algebraMap_ne_zero hcontent))
  have hlocalCop : IsCoprime (r.map φ) (c.map φ * b.map φ) := by
    apply (isCoprime_mul_unit_left_right hcUnit (r.map φ) (b.map φ)).mpr
    exact hcoprime
  have hmapSelf : r.map φ ∣ (D r).map φ :=
    hlocalCop.dvd_of_dvd_mul_left hmapLast
  exact hrprimitive.dvd_of_fraction_map_dvd_fraction_map hmapSelf

/-- Localization preserves powers of stored bivariate polynomials. -/
theorem localized_pow (A : CBivariate F) (n : ℕ) : localized (A ^ n) = localized A ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    change ClearDenominators.valueGlobal (1 : CBivariate F) = 1
    unfold ClearDenominators.valueGlobal
    rw [CBivariate.toPoly_one, Polynomial.map_one]
  | succ n ih =>
    rw [pow_succ]
    change ClearDenominators.valueGlobal (A ^ n * A) = localized A ^ (n + 1)
    rw [ClearDenominators.valueGlobal_mul,
      show ClearDenominators.valueGlobal (A ^ n) = localized A ^ n from ih, pow_succ]

/-- A nonzero polynomial divides the `natDegree`-th power of its radical.  This is the fixed
exponent version of `exists_dvd_radical_self_pow` needed by the bounded Radical invariant. -/
theorem polynomial_dvd_radical_pow_natDegree {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) :
    f ∣ polynomialRadical f ^ f.natDegree := by
  classical
  unfold polynomialRadical
  refine UniqueFactorizationMonoid.induction_on_coprime
    (P := fun g : Polynomial K =>
      g ≠ 0 → g ∣ UniqueFactorizationMonoid.radical g ^ g.natDegree)
    f ?_ ?_ ?_ ?_ hf
  · intro hzero
    contradiction
  · intro u hu _hu0
    exact hu.dvd
  · intro q i hq _hqi
    by_cases hi : i = 0
    · subst i
      simp
    rw [UniqueFactorizationMonoid.radical_pow_of_prime hq hi,
      Polynomial.natDegree_pow]
    apply pow_dvd_pow_of_dvd_of_le (normalize_associated q).symm.dvd
    exact Nat.le_mul_of_pos_right i (Irreducible.natDegree_pos hq.irreducible)
  · intro f g hcoprime hfInd hgInd hfg
    have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg
    have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg
    rw [UniqueFactorizationMonoid.radical_mul hcoprime,
      Polynomial.natDegree_mul hf0 hg0, mul_pow]
    exact mul_dvd_mul
      ((hfInd hf0).trans (pow_dvd_pow _ (Nat.le_add_right _ _)))
      ((hgInd hg0).trans (pow_dvd_pow _ (Nat.le_add_left _ _)))

/-- A nonzero stored input of `Y` degree at most `ell` divides the `ell`-th power of its
localized radical.  In particular this covers primitive inputs and their pure-`X` content edge. -/
theorem localized_dvd_localizedRadical_pow (ell : ℕ) (H : CBivariate F) (hH : H ≠ 0)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell) :
    localized H ∣ localizedRadical H ^ ell := by
  have hlocal : localized H ≠ 0 := by
    intro hz
    apply hH
    apply CBivariate.ringEquiv.injective
    apply Polynomial.map_injective _ (RatFunc.algebraMap_injective F)
    change localized H = localized 0
    simpa only [ClearDenominators.valueGlobal_zero] using hz
  have hlocalizedDegree : (localized H).natDegree ≤ ell := by
    unfold localized ClearDenominators.valueGlobal
    rw [Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective F)]
    exact hdegree
  change localized H ∣ polynomialRadical (localized H) ^ ell
  exact (polynomial_dvd_radical_pow_natDegree (localized H) hlocal).trans
    (pow_dvd_pow (polynomialRadical (localized H)) hlocalizedDegree)

/-- Successful saturation exposes the two exact quotient calls made by the program. -/
theorem saturate_provenance (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F)
    (h : saturate ell H = .ok step) :
    step.common = globalGcd H
        (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) ∧
      quotientPrimitive H step.common = some step.visible ∧
      step.removed = globalGcd H (step.visible ^ ell) ∧
      quotientPrimitive H step.removed = some step.residual := by
  unfold saturate at h
  dsimp only at h
  cases hvisible : quotientPrimitive H
      (globalGcd H (globalGcd (CBivariate.partialDerivX H)
        (CBivariate.partialDerivY H))) with
  | none => rw [hvisible] at h; contradiction
  | some visible =>
    rw [hvisible] at h
    dsimp only at h
    cases hresidual : quotientPrimitive H (globalGcd H (visible ^ ell)) with
    | none => rw [hresidual] at h; contradiction
    | some residual =>
      rw [hresidual] at h
      change Except.ok
        { common := globalGcd H (globalGcd (CBivariate.partialDerivX H)
            (CBivariate.partialDerivY H)),
          visible := visible, removed := globalGcd H (visible ^ ell),
          residual := residual } = Except.ok step at h
      injection h with hstep
      subst step
      exact ⟨rfl, hvisible, rfl, hresidual⟩

/-- Both quotients returned by a successful saturation of a nonzero input are nonzero. -/
theorem saturate_outputs_ne_zero (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (hH : H ≠ 0)
    (h : saturate ell H = .ok step) : step.visible ≠ 0 ∧ step.residual ≠ 0 := by
  have hp := saturate_provenance ell H step h
  exact ⟨quotientPrimitive_output_ne_zero H step.common step.visible hH hp.2.1,
    quotientPrimitive_output_ne_zero H step.removed step.residual hH hp.2.2.2⟩

/-- The two saturation outputs divide the original polynomial globally. -/
theorem saturate_outputs_dvd (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (hH : H ≠ 0)
    (h : saturate ell H = .ok step) :
    CBivariate.toPoly step.visible ∣ CBivariate.toPoly H ∧
      CBivariate.toPoly step.residual ∣ CBivariate.toPoly H := by
  have hp := saturate_provenance ell H step h
  have hn := saturate_outputs_ne_zero ell H step hH h
  exact ⟨quotientPrimitive_dvd_left_global H step.common step.visible hp.2.1 hn.1,
    quotientPrimitive_dvd_left_global H step.removed step.residual hp.2.2.2 hn.2⟩

/-- Exact localized quotient and gcd identities exposed by a successful saturation call. -/
theorem saturate_localized_identities (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (h : saturate ell H = .ok step) :
    Associated (localized step.visible * localized step.common) (localized H) ∧
      Associated (localized step.residual * localized step.removed) (localized H) := by
  have hp := saturate_provenance ell H step h
  exact ⟨quotientPrimitive_localized_mul_associated H step.common step.visible hp.2.1,
    quotientPrimitive_localized_mul_associated H step.removed step.residual hp.2.2.2⟩

/-- The second gcd in an executed saturation removes exactly the derivative-visible support.
This packages the squarefreeness, coprimality, and radical partition used by recursion. -/
theorem saturate_localized_classification (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    (hexec : saturate ell H = .ok step) :
    Squarefree (localized step.visible) ∧
      IsCoprime (localized step.visible) (localized step.residual) ∧
      Associated (localizedRadical H)
        (localized step.visible * localizedRadical step.residual) := by
  classical
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  have hids := saturate_localized_identities ell H step hexec
  have hprov := saturate_provenance ell H step hexec
  have hne := saturate_outputs_ne_zero ell H step hH hexec
  have hA0 : localized H ≠ 0 := by
    intro hz
    apply hH
    apply CBivariate.ringEquiv.injective
    apply Polynomial.map_injective _ (RatFunc.algebraMap_injective F)
    change localized H = localized 0
    simpa only [ClearDenominators.valueGlobal_zero] using hz
  have hrepeat : polynomialDivRadical (localized H) ∣ localized step.common := by
    rw [hprov.1]
    exact localized_divRadical_dvd_saturationCommon H hH hprimitive
  have hvisibleDvd : localized step.visible ∣ localized H :=
    (dvd_mul_right (localized step.visible) (localized step.common)).trans hids.1.dvd
  have hvisibleSf : Squarefree (localized step.visible) := by
    unfold polynomialDivRadical at hrepeat
    exact squarefree_of_divRadical_dvd_complement hA0 hids.1 hrepeat
  have hremovedGcd : Associated (localized step.removed)
      (EuclideanDomain.gcd (localized H) (localized step.visible ^ ell)) := by
    rw [hprov.2.2.1]
    simpa only [localized_pow] using globalGcd_associated H (step.visible ^ ell)
  have hmult : ∀ q : Polynomial (RatFunc F), Prime q → q ∣ localized H →
      multiplicity q (localized H) ≤ ell := by
    intro q hq _hqA
    exact (prime_multiplicity_le_natDegree hA0 hq).trans (by
      unfold localized ClearDenominators.valueGlobal
      rw [Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective F)]
      exact hdegree)
  have hsplit := boundedGcd_radical_split hA0 hvisibleSf hvisibleDvd hmult
    hremovedGcd hids.2
  refine ⟨hvisibleSf, hsplit.1, ?_⟩
  unfold localizedRadical polynomialRadical
  exact hsplit.2

/-- The residual returned by an executed saturation is killed by both global partial
derivatives.  Cancellation is performed in the global primitive quotient identity, so the
coefficient-variable derivative is sound despite localization units depending on `X`. -/
theorem saturate_residual_partials (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    (hexec : saturate ell H = .ok step) :
    CBivariate.partialDerivX step.residual = 0 ∧
      CBivariate.partialDerivY step.residual = 0 := by
  classical
  let _ : DecidableEq (RatFunc F) := Classical.decEq _
  have hclass := saturate_localized_classification ell H step hH hprimitive hdegree hexec
  have hids := saturate_localized_identities ell H step hexec
  have hprov := saturate_provenance ell H step hexec
  have hne := saturate_outputs_ne_zero ell H step hH hexec
  have hremovedDvdPow : localized step.removed ∣ localized step.visible ^ ell := by
    have hg := globalGcd_associated H (step.visible ^ ell)
    rw [← hprov.2.2.1] at hg
    have hd : localized step.removed ∣ localized (step.visible ^ ell) :=
      hg.dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
    simpa only [localized_pow] using hd
  have hresidualCoprimeRemoved :
      IsCoprime (localized step.residual) (localized step.removed) :=
    (hclass.2.1.symm.pow_right).of_isCoprime_of_dvd_right hremovedDvdPow
  have hresidualDvdH : localized step.residual ∣ localized H :=
    (dvd_mul_right (localized step.residual) (localized step.removed)).trans hids.2.dvd
  have hresidualDvdVisibleCommon : localized step.residual ∣
      localized step.visible * localized step.common :=
    hresidualDvdH.trans hids.1.symm.dvd
  have hresidualDvdCommon : localized step.residual ∣ localized step.common :=
    hclass.2.1.symm.dvd_of_dvd_mul_left hresidualDvdVisibleCommon
  have hcommonDvdInner : localized step.common ∣
      localized (globalGcd (CBivariate.partialDerivX H)
        (CBivariate.partialDerivY H)) := by
    rw [hprov.1]
    exact (globalGcd_associated H
      (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H))).dvd.trans
        (EuclideanDomain.gcd_dvd_right _ _)
  have hinnerDvdX : localized
      (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) ∣
      localized (CBivariate.partialDerivX H) :=
    (globalGcd_associated (CBivariate.partialDerivX H)
      (CBivariate.partialDerivY H)).dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hinnerDvdY : localized
      (globalGcd (CBivariate.partialDerivX H) (CBivariate.partialDerivY H)) ∣
      localized (CBivariate.partialDerivY H) :=
    (globalGcd_associated (CBivariate.partialDerivX H)
      (CBivariate.partialDerivY H)).dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hlocalX : localized step.residual ∣ localized (CBivariate.partialDerivX H) :=
    hresidualDvdCommon.trans (hcommonDvdInner.trans hinnerDvdX)
  have hlocalY : localized step.residual ∣ localized (CBivariate.partialDerivY H) :=
    hresidualDvdCommon.trans (hcommonDvdInner.trans hinnerDvdY)
  have hresPrimitive : (CBivariate.toPoly step.residual).IsPrimitive :=
    quotientPrimitive_isPrimitive H step.removed step.residual hprov.2.2.2 hne.2
  have hglobalX : CBivariate.toPoly step.residual ∣
      CBivariate.toPoly (CBivariate.partialDerivX H) := by
    apply hresPrimitive.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F)
    change (CBivariate.toPoly step.residual).map
      (algebraMap (Polynomial F) (RatFunc F)) ∣
        (CBivariate.toPoly (CBivariate.partialDerivX H)).map
          (algebraMap (Polynomial F) (RatFunc F))
    exact hlocalX
  have hglobalY : CBivariate.toPoly step.residual ∣
      CBivariate.toPoly (CBivariate.partialDerivY H) := by
    apply hresPrimitive.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc F)
    change (CBivariate.toPoly step.residual).map
      (algebraMap (Polynomial F) (RatFunc F)) ∣
        (CBivariate.toPoly (CBivariate.partialDerivY H)).map
          (algebraMap (Polynomial F) (RatFunc F))
    exact hlocalY
  have hselfX : CBivariate.toPoly step.residual ∣
      CBivariate.toPoly (CBivariate.partialDerivX step.residual) := by
    rw [← partialDerivXDerivation_apply]
    exact quotientPrimitive_derivation_dvd_self (partialDerivXDerivation (F := F))
      H step.removed step.residual hprov.2.2.2 hne.2 hresidualCoprimeRemoved
      (by rw [partialDerivXDerivation_apply]; exact hglobalX)
  have hselfY : CBivariate.toPoly step.residual ∣
      CBivariate.toPoly (CBivariate.partialDerivY step.residual) := by
    rw [← partialDerivYDerivation_apply]
    exact quotientPrimitive_derivation_dvd_self (partialDerivYDerivation (F := F))
      H step.removed step.residual hprov.2.2.2 hne.2 hresidualCoprimeRemoved
      (by rw [partialDerivYDerivation_apply]; exact hglobalY)
  constructor
  · by_contra hx
    exact not_dvd_partialDerivX_of_ne_zero hx hselfX
  · apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly (CBivariate.partialDerivY step.residual) = CBivariate.toPoly 0
    rw [CBivariate.toPoly_zero, CBivariate.partialDerivY_toPoly]
    exact Polynomial.eq_zero_of_dvd_of_degree_lt
      (by simpa only [CBivariate.partialDerivY_toPoly] using hselfY)
      (Polynomial.degree_derivative_lt (by
        intro hz
        apply hne.2
        calc
          step.residual = CBivariate.ofPoly (CBivariate.toPoly step.residual) :=
            (CBivariate.toPoly_ofPoly step.residual).symm
          _ = CBivariate.ofPoly 0 := congrArg CBivariate.ofPoly hz
          _ = 0 := CBivariate.ofPoly_zero))

/-- Each irreducible factor of a primitive global input has positive `Y` degree. -/
theorem normalizedFactor_natDegree_pos
    [NormalizationMonoid (Polynomial (Polynomial F))] (H : CBivariate F)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    {q : Polynomial (Polynomial F)}
    (hq : q ∈ normalizedFactors (CBivariate.toPoly H)) : 0 < q.natDegree := by
  have hqirr := irreducible_of_normalized_factor q hq
  by_contra hpos
  have hdeg : q.natDegree = 0 := Nat.eq_zero_of_not_pos hpos
  have hqdvd : q ∣ CBivariate.toPoly H := dvd_of_mem_normalizedFactors hq
  have hqprimitive := Polynomial.isPrimitive_of_dvd hprimitive hqdvd
  have hunitCoeff : IsUnit (q.coeff 0) := hqprimitive (q.coeff 0) ⟨1, by
    simpa only [mul_one] using Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hqirr
  exact hqirr.not_isUnit (Polynomial.isUnit_C.mpr hunitCoeff)

/-- The multiplicity of every normalized irreducible factor of a primitive input is at most its
outer degree, hence at most the Radical budget `ell`. -/
theorem normalizedFactor_multiplicity_le
    [NormalizationMonoid (Polynomial (Polynomial F))] (ell : ℕ) (H : CBivariate F)
    (hH : H ≠ 0) (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    {q : Polynomial (Polynomial F)}
    (hq : q ∈ normalizedFactors (CBivariate.toPoly H)) :
    multiplicity q (CBivariate.toPoly H) ≤ ell := by
  have hpoly : CBivariate.toPoly H ≠ 0 := by
    intro hz
    apply hH
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly H = CBivariate.toPoly 0
    simpa only [CBivariate.toPoly_zero] using hz
  have hqirr := irreducible_of_normalized_factor q hq
  have hpow : q ^ multiplicity q (CBivariate.toPoly H) ∣ CBivariate.toPoly H :=
    pow_multiplicity_dvd q (CBivariate.toPoly H)
  have hpow0 : q ^ multiplicity q (CBivariate.toPoly H) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hpoly hpow
  have hdegq : 0 < q.natDegree := normalizedFactor_natDegree_pos H hprimitive hq
  have hdegPow := Polynomial.natDegree_le_of_dvd hpow hpoly
  rw [Polynomial.natDegree_pow q] at hdegPow
  exact (Nat.le_mul_of_pos_right _ hdegq).trans (hdegPow.trans hdegree)

/-- A successful saturation inherits the input degree bound on both returned quotients. -/
theorem saturate_output_degree_le (ell : ℕ) (H : CBivariate F)
    (step : OrdinaryNormalization.Saturation F) (hH : H ≠ 0)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    (h : saturate ell H = .ok step) :
    (CBivariate.toPoly step.visible).natDegree ≤ ell ∧
      (CBivariate.toPoly step.residual).natDegree ≤ ell := by
  have hp := saturate_provenance ell H step h
  exact ⟨(quotientPrimitive_natDegree_le H step.common step.visible hp.2.1 hH).trans hdegree,
    (quotientPrimitive_natDegree_le H step.removed step.residual hp.2.2.2 hH).trans hdegree⟩

/-- If a nonzero polynomial in characteristic `p` has zero `Y` derivative and positive `Y`
degree, then `p` is at most that degree. -/
theorem char_le_natDegree_of_partialDerivY_eq_zero (p : ℕ) [Fact p.Prime] [CharP F p]
    (R : CBivariate F) (hR : R ≠ 0) (hpos : 0 < (CBivariate.toPoly R).natDegree)
    (hderiv : CBivariate.partialDerivY R = 0) :
    p ≤ (CBivariate.toPoly R).natDegree := by
  let n := (CBivariate.toPoly R).natDegree - 1
  have hn : n + 1 = (CBivariate.toPoly R).natDegree := Nat.sub_add_cancel hpos
  have hcoeff := Polynomial.coeff_derivative (CBivariate.toPoly R) n
  rw [← CBivariate.partialDerivY_toPoly, hderiv, CBivariate.toPoly_zero,
    Polynomial.coeff_zero, hn, Polynomial.coeff_natDegree, ← Nat.cast_one,
    ← Nat.cast_add, hn] at hcoeff
  have hcast : ((CBivariate.toPoly R).natDegree : Polynomial F) = 0 := by
    exact (mul_eq_zero.mp hcoeff.symm).resolve_left (Polynomial.leadingCoeff_ne_zero.mpr (by
    intro hz
    apply hR
    apply CBivariate.ringEquiv.injective
    change CBivariate.toPoly R = CBivariate.toPoly 0
    simpa only [CBivariate.toPoly_zero] using hz))
  have hdvd : p ∣ (CBivariate.toPoly R).natDegree :=
    (CharP.cast_eq_zero_iff (Polynomial F) p _).mp hcast
  exact Nat.le_of_dvd hpos hdvd

/-- The characteristic guard needed by recursive Radical follows from the actual residual,
its zero `Y` derivative, and the original degree bound. -/
theorem p_le_ell_of_saturated_residual (p ell : ℕ) [Fact p.Prime] [CharP F p]
    (H : CBivariate F) (step : OrdinaryNormalization.Saturation F)
    (hH : H ≠ 0) (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    (hexec : saturate ell H = .ok step)
    (hpartialY : CBivariate.partialDerivY step.residual = 0)
    (hpos : 0 < (CBivariate.toPoly step.residual).natDegree) : p ≤ ell := by
  exact (char_le_natDegree_of_partialDerivY_eq_zero p step.residual
    (saturate_outputs_ne_zero ell H step hH hexec).2 hpos hpartialY).trans
      (saturate_output_degree_le ell H step hH hdegree hexec).2

/-- Build the complete saturation certificate directly from a successful execution and the
input invariants.  All factor-classification conclusions are derived from the two executed gcds
and the primitive quotient identities. -/
theorem saturationCertificate (p ell : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (H : CBivariate F) (step : OrdinaryNormalization.Saturation F)
    (hexecution : saturate ell H = .ok step) (hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ ell)
    (hinverse : p ≤ ell → ∀ a, inverse a ^ p = a) :
    SaturationCertificate p ell inverse H step := by
  have hne := saturate_outputs_ne_zero ell H step hH hexecution
  have hclass := saturate_localized_classification ell H step hH hprimitive hdegree hexecution
  have hpartials := saturate_residual_partials ell H step hH hprimitive hdegree hexecution
  exact
    { execution := hexecution
      input_ne_zero := hH
      input_primitive := hprimitive
      degree_le := hdegree
      inverse_law := hinverse
      visible_ne_zero := hne.1
      visible_squarefree := hclass.1
      residual_ne_zero := hne.2
      residual_partials := hpartials
      visible_coprime_residual := hclass.2.1
      radical_split := hclass.2.2
      p_le_ell_of_residual_nonconstant := fun hpos ↦
        p_le_ell_of_saturated_residual p ell H step hH hdegree hexecution
          hpartials.2 hpos }

/-- The fixed-exponent divisibility invariant available from every saturation certificate. -/
theorem SaturationCertificate.input_dvd_radical_pow {p ell : ℕ} [CharP F p]
    {inverse : F → F} {H : CBivariate F} {step : OrdinaryNormalization.Saturation F}
    (cert : SaturationCertificate p ell inverse H step) :
    localized H ∣ localizedRadical H ^ ell :=
  localized_dvd_localizedRadical_pow ell H cert.input_ne_zero cert.degree_le

/-- Both actual returned pieces divide the input globally. -/
theorem SaturationCertificate.outputs_dvd {p ell : ℕ} [CharP F p]
    {inverse : F → F} {H : CBivariate F} {step : OrdinaryNormalization.Saturation F}
    (cert : SaturationCertificate p ell inverse H step) :
    CBivariate.toPoly step.visible ∣ CBivariate.toPoly H ∧
      CBivariate.toPoly step.residual ∣ CBivariate.toPoly H :=
  saturate_outputs_dvd ell H step cert.input_ne_zero cert.execution

end Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity
