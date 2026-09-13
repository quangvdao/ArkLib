/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GCDSplit
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Powered polynomial split arithmetic

The agreeing factor is computed against a residual raised to the fiber degree.
This retains multiplicities, including when that degree exceeds the characteristic.
The definitions here are the scalar arithmetic specification for dynamic tower splitting.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

omit [BEq F] [LawfulBEq F] in
/-- A power bounded below by the parent degree removes every primary factor shared with the
residual. This algebraic statement has no restriction on the characteristic. -/
theorem quotient_isCoprime_residual_of_common_divisors
    {H E S D Q : Polynomial F} {b : ℕ}
    (hH : H ≠ 0) (hb : H.natDegree ≤ b)
    (hcommon : ∀ p : Polynomial F, p ∣ H → p ∣ E ^ b → p ∣ S)
    (hD : ∀ p : Polynomial F, p ∣ H → p ∣ S → p ∣ D) (hfactor : D * Q = H) :
    IsCoprime Q E := by
  classical
  apply IsRelPrime.isCoprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
    (right_ne_zero_of_mul (hfactor ▸ hH))).mpr
  intro p hpQ hpE hp
  obtain ⟨m, a, hpa, hHa⟩ := WfDvdMonoid.max_power_factor hH hp.irreducible
  have hpowH : p ^ m ∣ H := ⟨a, hHa⟩
  have hm : m ≤ b := by
    have hdeg := Polynomial.natDegree_le_of_dvd hpowH hH
    rw [Polynomial.natDegree_pow] at hdeg
    have hpdeg := hp.irreducible.natDegree_pos
    exact (Nat.le_mul_of_pos_right m hpdeg).trans (hdeg.trans hb)
  have hpowE : p ^ m ∣ E ^ b :=
    (pow_dvd_pow_of_dvd hpE m).trans (pow_dvd_pow E hm)
  have hpowD : p ^ m ∣ D :=
    hD _ hpowH (hcommon _ hpowH hpowE)
  have hmore : p ^ m * p ∣ H := by
    rw [← hfactor]
    exact mul_dvd_mul hpowD hpQ
  rw [hHa] at hmore
  exact hpa ((mul_dvd_mul_iff_left (pow_ne_zero m hp.ne_zero)).mp hmore)

omit [BEq F] [LawfulBEq F] in
/-- Quotienting by the gcd with a sufficiently large residual power leaves a unit residual. -/
theorem quotient_isCoprime_residual [DecidableEq F] {H E D Q : Polynomial F} {b : ℕ}
    (hH : H ≠ 0) (hb : H.natDegree ≤ b)
    (hD : Associated D (EuclideanDomain.gcd H (E ^ b))) (hfactor : D * Q = H) :
    IsCoprime Q E :=
  quotient_isCoprime_residual_of_common_divisors hH hb (fun _ _ he => he)
    (fun _ hpH hpE => hD.dvd_iff_dvd_right.mpr (EuclideanDomain.dvd_gcd hpH hpE)) hfactor

omit [BEq F] [LawfulBEq F] in
/-- Removing a divisor of the residual power preserves every multiplicity of every irreducible
factor coprime to the residual. -/
theorem primary_power_dvd_quotient_iff {H E D Q p : Polynomial F} {b : ℕ}
    (hfactor : D * Q = H) (hD : D ∣ E ^ b)
    (hp : Irreducible p) (hpE : ¬p ∣ E) (m : ℕ) :
    p ^ m ∣ Q ↔ p ^ m ∣ H := by
  have hcop : IsCoprime (p ^ m) (E ^ b) :=
    ((hp.isRelPrime_iff_not_dvd.mpr hpE).isCoprime.pow_left).pow_right
  constructor
  · intro hq
    rw [← hfactor]
    exact dvd_mul_of_dvd_right hq _
  · intro hh
    rw [← hfactor] at hh
    exact (hcop.of_isCoprime_of_dvd_right hD).dvd_of_dvd_mul_left hh

/-- The residual power used to retain complete primary components. -/
def poweredResidual (h e : CPolynomial F) : CPolynomial F :=
  (e ^ h.natDegree).modByMonic h

/-- The agreeing factor, with its original multiplicities. -/
def nilFactor (h e : CPolynomial F) : CPolynomial F :=
  gcdFactor h (poweredResidual h e)

/-- The complementary factor computed by exact monic division. -/
def unitFactor (h e : CPolynomial F) : CPolynomial F :=
  gcdComplement h (poweredResidual h e)

/-- Reducing the power modulo the fiber does not change its gcd. -/
theorem nilFactor_eq (h e : CPolynomial F) (hh : h.monic) :
    nilFactor h e = gcdFactor h (e ^ h.natDegree) :=
  gcdFactor_modByMonic h (e ^ h.natDegree) hh

/-- Reducing the power also preserves the exact complementary factor. -/
theorem unitFactor_eq (h e : CPolynomial F) (hh : h.monic) :
    unitFactor h e = gcdComplement h (e ^ h.natDegree) :=
  gcdComplement_modByMonic h (e ^ h.natDegree) hh

/-- The actual computed factors multiply to the parent, including repeated factors. -/
theorem factor_product (h e : CPolynomial F) (hh : h ≠ 0) :
    nilFactor h e * unitFactor h e = h :=
  gcdFactor_mul_gcdComplement hh

/-- The agreeing factor remains monic. -/
theorem nilFactor_monic (h e : CPolynomial F) (hh : h ≠ 0) :
    (nilFactor h e).monic := gcdFactor_monic hh

/-- The complementary factor remains monic. -/
theorem unitFactor_monic (h e : CPolynomial F) (hh : h.monic) :
    (unitFactor h e).monic := gcdComplement_monic hh

/-- The residual is nilpotent modulo the agreeing factor, with exponent the fiber degree. -/
theorem nilFactor_dvd_power (h e : CPolynomial F) (hh : h.monic) :
    (nilFactor h e).toPoly ∣ (e ^ h.natDegree).toPoly := by
  rw [nilFactor_eq h e hh]
  exact gcdFactor_dvd_right _ _

/-- The complementary quotient is coprime to the original residual. -/
theorem unitFactor_isCoprime_residual (h e : CPolynomial F) (hh : h.monic) :
    IsCoprime (unitFactor h e).toPoly e.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hn : h ≠ 0 := (toPoly_eq_zero_iff h).not.mp ((monic_toPoly_iff h).mp hh).ne_zero
  apply quotient_isCoprime_residual
    ((monic_toPoly_iff h).mp hh).ne_zero (b := h.natDegree) (D := (nilFactor h e).toPoly)
  · exact (natDegree_toPoly h).symm.le
  · rw [nilFactor_eq h e hh, gcdFactor_toPoly, toPoly_pow]
    exact normalize_associated _
  · simpa only [toPoly_mul] using congrArg CPolynomial.toPoly (factor_product h e hn)

/-- The agreeing and complementary factors are coprime, even for a nonreduced parent. -/
theorem factors_isCoprime (h e : CPolynomial F) (hh : h.monic) :
    IsCoprime (nilFactor h e).toPoly (unitFactor h e).toPoly := by
  have hc : IsCoprime (unitFactor h e).toPoly (e.toPoly ^ h.natDegree) :=
    (unitFactor_isCoprime_residual h e hh).pow_right
  apply IsRelPrime.isCoprime
  intro d hdN hdU
  apply hc.isRelPrime hdU
  have hd := hdN.trans (nilFactor_dvd_power h e hh)
  simpa only [toPoly_pow] using hd

/-- Algebra dimensions are conserved before constant factors are discarded. -/
theorem degree_conservation (h e : CPolynomial F) (hh : h ≠ 0) :
    (nilFactor h e).toPoly.natDegree + (unitFactor h e).toPoly.natDegree =
      h.toPoly.natDegree := natDegree_gcdFactor_add_gcdComplement hh

/-- Over every extension field, the agreeing factor detects exactly the agreeing parent roots. -/
theorem nilFactor_root_iff {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (h e : CPolynomial F) (hh : h.monic) (hpos : 0 < h.natDegree) :
    (nilFactor h e).toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ e.toPoly.eval₂ phi x = 0 := by
  rw [nilFactor_eq h e hh, eval₂_gcdFactor_eq_zero_iff_left_right]
  simp only [toPoly_pow, Polynomial.eval₂_pow, pow_eq_zero_iff hpos.ne']

/-- Every power of an agreeing irreducible factor is retained exactly when it divides the parent.
Thus agreeing primary components keep all of their original multiplicity. -/
theorem primary_power_dvd_nilFactor_iff (h e : CPolynomial F) (hh : h.monic)
    {p : Polynomial F} (hp : Irreducible p) (hpe : p ∣ e.toPoly) (m : ℕ) :
    p ^ m ∣ (nilFactor h e).toPoly ↔ p ^ m ∣ h.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  constructor
  · exact fun hd => hd.trans (gcdFactor_dvd_left h (poweredResidual h e))
  · intro hd
    have hdeg := Polynomial.natDegree_le_of_dvd hd ((monic_toPoly_iff h).mp hh).ne_zero
    rw [Polynomial.natDegree_pow, ← natDegree_toPoly h] at hdeg
    have hm : m ≤ h.natDegree := (Nat.le_mul_of_pos_right m hp.natDegree_pos).trans hdeg
    rw [nilFactor_eq h e hh, gcdFactor_toPoly, dvd_normalize_iff, toPoly_pow]
    exact EuclideanDomain.dvd_gcd hd
      ((pow_dvd_pow_of_dvd hpe m).trans (pow_dvd_pow e.toPoly hm))

/-- The complementary factor contains precisely the nonagreeing parent roots over any field. -/
theorem unitFactor_root_iff {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (h e : CPolynomial F) (hh : h.monic) (hpos : 0 < h.natDegree) :
    (unitFactor h e).toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ e.toPoly.eval₂ phi x ≠ 0 := by
  have hn : h ≠ 0 := (toPoly_eq_zero_iff h).not.mp ((monic_toPoly_iff h).mp hh).ne_zero
  have hprod := congrArg (fun q : CPolynomial F => q.toPoly.eval₂ phi x)
    (factor_product h e hn)
  simp only [toPoly_mul, Polynomial.eval₂_mul] at hprod
  constructor
  · intro hu
    refine ⟨by simpa [hu] using hprod.symm, ?_⟩
    intro he
    obtain ⟨a, b, hab⟩ := unitFactor_isCoprime_residual h e hh
    have hc := congrArg (Polynomial.eval₂ phi x) hab
    simp [hu, he] at hc
  · rintro ⟨hroot, he⟩
    have hnroot : (nilFactor h e).toPoly.eval₂ phi x ≠ 0 :=
      fun hz => he ((nilFactor_root_iff phi x h e hh hpos).mp hz).2
    exact (mul_eq_zero.mp (hprod.trans hroot)).resolve_left hnroot

end ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit
