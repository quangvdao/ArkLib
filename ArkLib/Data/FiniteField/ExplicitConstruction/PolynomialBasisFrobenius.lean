/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import all CompPoly.Univariate.ToPoly.Equiv

public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
public import CompPoly.Univariate.Roots.Correctness
public import Mathlib.FieldTheory.Perfect

/-!
# Inverse Frobenius in a supplied polynomial basis

For a supplied presentation `F_p[t] / f`, this module implements the
small-characteristic inverse Frobenius algorithm used by the decoder. It groups
coefficients by their residue modulo `p`, computes the actual monic gcd with
`Z ^ p - theta`, extracts `beta` from the negative constant coefficient of that
gcd, and evaluates regrouped input coefficients using precomputed powers of
`beta`.

The bound argument records the decoder branch on which this routine is used.
The executable construction itself always uses the supplied prime `p`, which is
the proved characteristic of the quotient field.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

open CompPoly CompPoly.CPolynomial PolynomialQuotient

variable (p : Nat) [Fact p.Prime]
variable (f : CPolynomial (ZMod p)) [Fact f.monic]
variable [Fact (Irreducible f.toPoly)]

/-- The polynomial-basis generator `theta`, represented by `t` modulo `f`. -/
def frobeniusTheta : Carrier f := canonical f X

/-- The stored coefficient polynomial whose exponents are congruent to `r` modulo `p`. -/
def residuePolynomial (g : CPolynomial (ZMod p)) (r : Nat) : CPolynomial (ZMod p) :=
  CPolynomial.ofArray <| Array.ofFn fun j : Fin (g.natDegree / p + 1) =>
    g.coeff (p * j.val + r)

/-- The coefficient polynomial with indices congruent to `r` modulo `p`,
evaluated at `theta` in the supplied quotient. -/
def regroupCoefficient (g : CPolynomial (ZMod p)) (r : Nat) : Carrier f :=
  canonical f (residuePolynomial p g r)

/-- Group a polynomial's coefficients by exponent modulo the characteristic. -/
def regroupPolynomial (g : CPolynomial (ZMod p)) : CPolynomial (Carrier f) :=
  CPolynomial.ofArray <| Array.ofFn fun r : Fin p => regroupCoefficient p f g r.val

/-- The degree-`p` polynomial `Z ^ p - theta`. -/
def frobeniusRootPolynomial : CPolynomial (Carrier f) :=
  X ^ p - C (frobeniusTheta p f)

/-- The actual computed monic gcd used to recover the root of `theta`. -/
def frobeniusRootGCD : CPolynomial (Carrier f) :=
  CPolynomial.gcdMonic (regroupPolynomial p f f) (frobeniusRootPolynomial p f)

/-- The root recovered from the negative constant coefficient of the computed gcd. -/
def frobeniusBeta : Carrier f := -(frobeniusRootGCD p f).coeff 0

/-- The first `p` powers of the computed root, prepared once for regrouped evaluation. -/
def frobeniusBetaPowers : Array (Carrier f) :=
  Array.ofFn fun r : Fin p => frobeniusBeta p f ^ r.val

/-- Evaluate the regrouped coefficient vector using the precomputed powers of `beta`. -/
def inverseFrobenius (a : Carrier f) : Carrier f :=
  let powers := frobeniusBetaPowers p f
  (List.ofFn fun r : Fin p =>
    powers[r.val]'(by simp [powers, frobeniusBetaPowers]) *
      regroupCoefficient p f a.val r.val).sum

/-- Construct the same inverse callback once the decoder has discharged its
small-characteristic guard. -/
def boundedInverseFrobenius (B : Nat) (_hpB : p ≤ B) : Carrier f → Carrier f :=
  inverseFrobenius p f

/-- A one-time certificate that ties the decoder bound to the supplied field's
actual characteristic and carries the inverse law for the callback. -/
structure InverseFrobeniusCertificate (B : Nat) where
  inverse : Carrier f → Carrier f
  characteristic_le : p ≤ B
  inverse_pow_characteristic : ∀ a, inverse a ^ p = a

@[simp] theorem residuePolynomial_coeff (g : CPolynomial (ZMod p)) (r j : Nat) :
    (residuePolynomial p g r).coeff j =
      if _h : j < g.natDegree / p + 1 then g.coeff (p * j + r) else 0 := by
  rw [residuePolynomial, CPolynomial.coeff_ofArray]
  simp [Array.getD]

omit [Fact (Irreducible f.toPoly)] in
@[simp] theorem regroupPolynomial_coeff (g : CPolynomial (ZMod p)) (r : Nat) :
    (regroupPolynomial p f g).coeff r =
      if _h : r < p then regroupCoefficient p f g r else 0 := by
  rw [regroupPolynomial, CPolynomial.coeff_ofArray]
  simp [Array.getD]

theorem zmod_coeff_pow_characteristic (g : CPolynomial (ZMod p)) (n : Nat) :
    (g.toPoly ^ p).coeff n =
      if p ∣ n then g.coeff (n / p) else 0 := by
  rw [← Polynomial.map_frobenius_expand p]
  rw [Polynomial.coeff_map, Polynomial.coeff_expand (Fact.out : p.Prime).pos]
  have hfrob : ∀ x : ZMod p, frobenius (ZMod p) p x = x := by
    intro x
    change x ^ p = x
    exact ZMod.pow_card x
  rw [hfrob]
  by_cases hdvd : p ∣ n
  · rw [if_pos hdvd, if_pos hdvd]
    exact (CPolynomial.coeff_toPoly g (n / p)).symm
  · rw [if_neg hdvd, if_neg hdvd]

/-- Coefficient grouping reconstructs the original polynomial after the
`p`-th powers have restored the omitted exponent digits. -/
theorem sum_residue_pow_mul_X_eq (g : CPolynomial (ZMod p)) :
    (∑ r : Fin p, residuePolynomial p g r.val ^ p * X ^ r.val) = g := by
  apply CPolynomial.toPoly_injective
  have hmap := map_sum (CPolynomial.ringEquiv (R := ZMod p))
    (fun r : Fin p => residuePolynomial p g r.val ^ p * X ^ r.val) Finset.univ
  simp only [CPolynomial.ringEquiv_apply] at hmap
  rw [hmap]
  apply Polynomial.ext
  intro n
  change (Polynomial.lcoeff (ZMod p) n)
      (∑ r : Fin p, (residuePolynomial p g r.val ^ p * X ^ r.val).toPoly) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow]
  have hX : (X : CPolynomial (ZMod p)).toPoly = Polynomial.X :=
    CPolynomial.Raw.toPoly_X
  rw [hX]
  simp only [Polynomial.coeff_mul_X_pow', zmod_coeff_pow_characteristic]
  let r0 : Fin p := ⟨n % p, Nat.mod_lt n (Fact.out : p.Prime).pos⟩
  rw [Finset.sum_eq_single r0]
  · dsimp [r0]
    rw [if_pos (Nat.mod_le n p), if_pos (Nat.dvd_sub_mod (n := p) n)]
    have hsub : n - n % p = p * (n / p) := by
      have := Nat.mod_add_div n p
      omega
    have hnDiv : (n - n % p) / p = n / p := by
      rw [hsub, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos]
    have hindex : p * ((n - n % p) / p) + n % p = n := by
      rw [hnDiv]
      have := Nat.mod_add_div n p
      omega
    rw [residuePolynomial_coeff]
    split
    · rw [hindex, CPolynomial.coeff_toPoly]
    · rw [hnDiv] at *
      have hdegree : g.natDegree < n := by
        by_contra hle
        have := Nat.div_le_div_right (Nat.le_of_not_gt hle) (c := p)
        omega
      symm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (CPolynomial.natDegree_toPoly g ▸ hdegree)
  · intro r _hr hr
    by_cases hrn : r.val ≤ n
    · rw [if_pos hrn]
      by_cases hdvd : p ∣ n - r.val
      · exfalso
        apply hr
        apply Fin.ext
        have hrlt := r.isLt
        have hmodeq : r.val ≡ n [MOD p] := (Nat.modEq_iff_dvd' hrn).2 hdvd
        exact hmodeq.trans (Nat.mod_modEq n p).symm |>.eq_of_lt_of_lt hrlt
          (Nat.mod_lt n (Fact.out : p.Prime).pos)
      · rw [if_neg hdvd]
    · rw [if_neg hrn]
  · simp

/-- Canonical projection evaluates a stored polynomial at the quotient generator. -/
theorem canonical_eq_eval₂_at_theta (g : CPolynomial (ZMod p)) :
    canonical f g = g.toPoly.eval₂ (embedding f) (frobeniusTheta p f) := by
  let lhs : Polynomial (ZMod p) →+* Carrier f :=
    (projection f).comp CPolynomial.ringEquiv.symm.toRingHom
  let rhs : Polynomial (ZMod p) →+* Carrier f :=
    Polynomial.eval₂RingHom (embedding f) (frobeniusTheta p f)
  have hhom : lhs = rhs := by
    apply Polynomial.ringHom_ext
    · intro a
      have hC : CPolynomial.ringEquiv.symm (Polynomial.C a) = CPolynomial.C a := by
        apply (Equiv.symm_apply_eq
          (CPolynomial.ringEquiv (R := ZMod p)).toEquiv).2
        change Polynomial.C a = (CPolynomial.C a).toPoly
        exact (CPolynomial.C_toPoly a).symm
      simp [lhs, rhs, hC, projection, embedding, frobeniusTheta]
    · have hX : CPolynomial.ringEquiv.symm Polynomial.X =
          (CPolynomial.X : CPolynomial (ZMod p)) := by
        apply (Equiv.symm_apply_eq
          (CPolynomial.ringEquiv (R := ZMod p)).toEquiv).2
        change Polynomial.X = (CPolynomial.X : CPolynomial (ZMod p)).toPoly
        exact CPolynomial.X_toPoly.symm
      simp [lhs, rhs, hX, projection, frobeniusTheta]
  have happ := DFunLike.congr_fun hhom g.toPoly
  have hinv : CPolynomial.ringEquiv.symm g.toPoly = g :=
    CPolynomial.ringEquiv.symm_apply_apply g
  simpa [lhs, rhs, hinv, projection] using happ

/-- Regrouped coefficients reconstruct a quotient element after taking their
`p`-th powers and restoring the residue digit with powers of `theta`. -/
theorem sum_regroup_pow_mul_theta_eq (g : CPolynomial (ZMod p)) :
    (∑ r : Fin p, regroupCoefficient p f g r.val ^ p *
      frobeniusTheta p f ^ r.val) = canonical f g := by
  have h := congrArg (projection f) (sum_residue_pow_mul_X_eq p g)
  simp only [map_sum, map_mul, map_pow] at h
  simpa [regroupCoefficient, frobeniusTheta, projection] using h

omit [Fact f.monic] [Fact (Irreducible f.toPoly)] in
/-- Differentiating coefficient reconstruction removes the characteristic-`p`
powers and differentiates only the residue monomials. -/
theorem sum_residue_pow_mul_derivative_eq :
    (∑ r : Fin p, (residuePolynomial p f r.val).toPoly ^ p *
      (Polynomial.C (r.val : ZMod p) * Polynomial.X ^ (r.val - 1))) =
        f.toPoly.derivative := by
  have h :
      (∑ r : Fin p, Polynomial.derivative
        (residuePolynomial p f r.val ^ p * CPolynomial.X ^ r.val).toPoly) =
          f.toPoly.derivative := by
    rw [← map_sum]
    congr 1
    rw [← CPolynomial.toPoly_sum, sum_residue_pow_mul_X_eq]
  simp only [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, Polynomial.derivative_mul, Polynomial.derivative_pow,
    ZMod.natCast_self, Polynomial.C_0] at h
  simpa using h

/-- Evaluation of the stored regrouped polynomial is the prescribed residue sum. -/
theorem eval_regroupPolynomial (g : CPolynomial (ZMod p)) (z : Carrier f) :
    CPolynomial.eval z (regroupPolynomial p f g) =
      ∑ r : Fin p, regroupCoefficient p f g r.val * z ^ r.val := by
  rw [CPolynomial.eval_toPoly]
  have hdegree : (regroupPolynomial p f g).toPoly.degree < p := by
    simpa [regroupPolynomial, coefficientPolynomial] using
      (coefficientPolynomial_degree
        (v := fun r : Fin p => regroupCoefficient p f g r.val))
  have hnatDegree : (regroupPolynomial p f g).toPoly.natDegree < p := by
    by_cases hz : (regroupPolynomial p f g).toPoly = 0
    · rw [hz, Polynomial.natDegree_zero]
      exact (Fact.out : p.Prime).pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hdegree
  rw [Polynomial.eval_eq_sum_range' hnatDegree]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← CPolynomial.coeff_toPoly, regroupPolynomial_coeff, dif_pos r.isLt]

/-- The derivative of a regrouped polynomial evaluates as the expected
coefficient-weighted residue sum. -/
theorem eval_derivative_regroupPolynomial (g : CPolynomial (ZMod p)) (z : Carrier f) :
    (regroupPolynomial p f g).toPoly.derivative.eval z =
      ∑ r : Fin p, regroupCoefficient p f g r.val * (r.val : Carrier f) *
        z ^ (r.val - 1) := by
  have hdegree : (regroupPolynomial p f g).toPoly.degree < p := by
    simpa [regroupPolynomial, coefficientPolynomial] using
      (coefficientPolynomial_degree
        (v := fun r : Fin p => regroupCoefficient p f g r.val))
  have hnatDegree : (regroupPolynomial p f g).toPoly.natDegree < p := by
    by_cases hz : (regroupPolynomial p f g).toPoly = 0
    · rw [hz, Polynomial.natDegree_zero]
      exact (Fact.out : p.Prime).pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 hdegree
  rw [Polynomial.derivative_eval]
  rw [Polynomial.sum_over_range' _ (by intro; simp) p hnatDegree]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← CPolynomial.coeff_toPoly, regroupPolynomial_coeff, dif_pos r.isLt]

omit [Fact (Irreducible f.toPoly)] in
/-- The supplied modulus itself represents zero in its quotient. -/
@[simp] theorem canonical_modulus_eq_zero : canonical f f = 0 := by
  apply ExplicitConstruction.ext
  apply CPolynomial.toPoly_injective
  change (reduce f f).toPoly = (reduce f 0).toPoly
  rw [reduce, reduce]
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out]
  let hm := (CPolynomial.monic_toPoly_iff f).mp Fact.out
  calc
    f.toPoly %ₘ f.toPoly = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hm).2 dvd_rfl
    _ = 0 %ₘ f.toPoly :=
      ((Polynomial.modByMonic_eq_zero_iff_dvd hm).2 (dvd_zero f.toPoly)).symm

/-- The derivative of the supplied irreducible modulus remains nonzero in the
quotient because its degree is strictly smaller than the modulus degree. -/
theorem canonical_derivative_ne_zero :
    canonical f (CPolynomial.ringEquiv.symm f.toPoly.derivative) ≠ 0 := by
  intro hzero
  have hval := congrArg Subtype.val hzero
  have hpoly := congrArg CPolynomial.toPoly hval
  change (reduce f (CPolynomial.ringEquiv.symm f.toPoly.derivative)).toPoly =
    (reduce f 0).toPoly at hpoly
  rw [reduce, reduce,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ Fact.out] at hpoly
  have hinv : (CPolynomial.ringEquiv.symm f.toPoly.derivative).toPoly =
      f.toPoly.derivative := by
    rw [← CPolynomial.ringEquiv_apply]
    exact CPolynomial.ringEquiv.right_inv _
  rw [hinv] at hpoly
  simp only [CPolynomial.toPoly_zero, Polynomial.zero_modByMonic] at hpoly
  have hfne : f.toPoly ≠ 0 := (Fact.out : Irreducible f.toPoly).ne_zero
  have hm : f.toPoly.Monic := (CPolynomial.monic_toPoly_iff f).mp Fact.out
  have hrem : f.toPoly.derivative %ₘ f.toPoly = f.toPoly.derivative :=
    (Polynomial.modByMonic_eq_self_iff hm).2 (Polynomial.degree_derivative_lt hfne)
  rw [hrem] at hpoly
  have hderiv : f.toPoly.derivative ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero
      (Fact.out : Irreducible f.toPoly)).1
        (PerfectField.separable_of_irreducible (Fact.out : Irreducible f.toPoly))
  exact hderiv (by simpa using hpoly)

/-- Projecting differentiated coefficient reconstruction into the supplied
quotient evaluates the residue monomials at `theta`. -/
theorem sum_regroup_pow_mul_derivative_theta_eq :
    (∑ r : Fin p, regroupCoefficient p f f r.val ^ p *
      ((r.val : Carrier f) * frobeniusTheta p f ^ (r.val - 1))) =
        canonical f (CPolynomial.ringEquiv.symm f.toPoly.derivative) := by
  have h := congrArg
    (Polynomial.eval₂RingHom (embedding f) (frobeniusTheta p f))
    (sum_residue_pow_mul_derivative_eq p f)
  have hinv : (CPolynomial.ringEquiv.symm f.toPoly.derivative).toPoly =
      f.toPoly.derivative := by
    rw [← CPolynomial.ringEquiv_apply]
    exact CPolynomial.ringEquiv.right_inv _
  rw [canonical_eq_eval₂_at_theta, hinv]
  simpa [regroupCoefficient, canonical_eq_eval₂_at_theta,
    Polynomial.eval₂_pow] using h

/-- Proof-side name for the unique Frobenius preimage of `theta`. It is used
only to establish the identity of the computed gcd. -/
noncomputable instance suppliedCarrierFinite : Finite (Carrier f) :=
  Finite.of_equiv (Fin f.natDegree → ZMod p) (quotientCoefficientsEquiv f).symm

noncomputable def frobeniusReferenceBeta : Carrier f :=
  (frobeniusEquiv (Carrier f) p).symm (frobeniusTheta p f)

theorem frobeniusReferenceBeta_pow :
    frobeniusReferenceBeta p f ^ p = frobeniusTheta p f := by
  exact frobeniusEquiv_symm_pow_p (Carrier f) p (frobeniusTheta p f)

theorem carrier_natCast_pow_characteristic (n : Nat) :
    (n : Carrier f) ^ p = (n : Carrier f) := by
  rw [← map_natCast (embedding f) n]
  rw [← map_pow, ZMod.pow_card]

/-- The proof-side Frobenius preimage is a root of the computed regrouped modulus. -/
theorem eval_regroupPolynomial_referenceBeta_eq_zero :
    CPolynomial.eval (frobeniusReferenceBeta p f) (regroupPolynomial p f f) = 0 := by
  have hsum := sum_regroup_pow_mul_theta_eq p f f
  rw [canonical_modulus_eq_zero] at hsum
  rw [eval_regroupPolynomial]
  apply (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp
  rw [sum_pow_char]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [mul_pow]
  congr 1
  calc
    (frobeniusReferenceBeta p f ^ r.val) ^ p =
        frobeniusReferenceBeta p f ^ (r.val * p) := (pow_mul _ _ _).symm
    _ = frobeniusReferenceBeta p f ^ (p * r.val) := by rw [Nat.mul_comm]
    _ = (frobeniusReferenceBeta p f ^ p) ^ r.val := pow_mul _ _ _
    _ = frobeniusTheta p f ^ r.val := by rw [frobeniusReferenceBeta_pow]

/-- The reference root is simple: a repeated root would force the derivative
of the supplied irreducible modulus to vanish in its quotient. -/
theorem eval_derivative_regroupPolynomial_referenceBeta_ne_zero :
    (regroupPolynomial p f f).toPoly.derivative.eval
      (frobeniusReferenceBeta p f) ≠ 0 := by
  intro hzero
  apply canonical_derivative_ne_zero p f
  rw [← sum_regroup_pow_mul_derivative_theta_eq]
  have hpzero := congrArg (· ^ p) hzero
  rw [eval_derivative_regroupPolynomial] at hpzero
  rw [sum_pow_char] at hpzero
  simp only [zero_pow (Fact.out : p.Prime).ne_zero] at hpzero
  have hsum :
      (∑ r : Fin p, regroupCoefficient p f f r.val ^ p *
        ((r.val : Carrier f) * frobeniusTheta p f ^ (r.val - 1))) = 0 := by
    rw [← hpzero]
    apply Finset.sum_congr rfl
    intro r _hr
    have hbetaPower :
        (frobeniusReferenceBeta p f ^ (r.val - 1)) ^ p =
          frobeniusTheta p f ^ (r.val - 1) := by
      calc
      (frobeniusReferenceBeta p f ^ (r.val - 1)) ^ p =
          frobeniusReferenceBeta p f ^ ((r.val - 1) * p) :=
            (pow_mul _ _ _).symm
      _ = frobeniusReferenceBeta p f ^ (p * (r.val - 1)) := by
            rw [Nat.mul_comm]
      _ = (frobeniusReferenceBeta p f ^ p) ^ (r.val - 1) := pow_mul _ _ _
      _ = frobeniusTheta p f ^ (r.val - 1) := by rw [frobeniusReferenceBeta_pow]
    rw [mul_pow, mul_pow, carrier_natCast_pow_characteristic, hbetaPower]
    ring
  exact hsum

/-- An actual computed monic gcd against `X ^ p - theta` is the linear root
factor when the other input has that root with nonzero derivative. -/
theorem gcdMonic_eq_X_sub_C_of_simple_root
    {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (p : Nat) [Fact p.Prime] [CharP K p]
    (R : CPolynomial K) (theta beta : K)
    (hbeta : beta ^ p = theta)
    (hroot : R.toPoly.eval beta = 0)
    (hsimple : R.toPoly.derivative.eval beta ≠ 0) :
    CPolynomial.gcdMonic R (CPolynomial.X ^ p - CPolynomial.C theta) =
      CPolynomial.X - CPolynomial.C beta := by
  let _ : DecidableEq K := instDecidableEqOfLawfulBEq
  apply CPolynomial.toPolyLinearEquiv.injective
  rw [CPolynomial.toPolyLinearEquiv_apply, CPolynomial.toPolyLinearEquiv_apply]
  rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd]
  simp only [CPolynomial.toPoly_sub, CPolynomial.toPoly_pow,
    CPolynomial.C_toPoly]
  rw [CPolynomial.X_toPoly]
  let L : Polynomial K := Polynomial.X - Polynomial.C beta
  let S : Polynomial K := R.toPoly /ₘ L
  have hfactor : L * S = R.toPoly := by
    dsimp [L, S]
    rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic,
      Polynomial.modByMonic_X_sub_C_eq_C_eval, hroot, Polynomial.C_0, sub_zero]
  have hcop : IsCoprime L S := by
    exact Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero
      R.toPoly beta hsimple
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpow : Polynomial.X ^ p - Polynomial.C theta = L ^ p := by
    dsimp [L]
    rw [sub_pow_char, ← Polynomial.C_pow, hbeta]
  have hpowFactor : L ^ p = L * L ^ (p - 1) := by
    nth_rw 1 [← Nat.succ_pred_eq_of_pos hp]
    rw [pow_succ', Nat.pred_eq_sub_one]
  rw [← hfactor, hpow, hpowFactor]
  have hcop' : IsCoprime S (L ^ (p - 1)) := hcop.symm.pow_right
  let g : Polynomial K := EuclideanDomain.gcd (L * S) (L * L ^ (p - 1))
  have hgLeft : g ∣ L * S := EuclideanDomain.gcd_dvd_left _ _
  have hgRight : g ∣ L * L ^ (p - 1) := EuclideanDomain.gcd_dvd_right _ _
  have hgL : g ∣ L := by
    rcases hcop' with ⟨a, b, hab⟩
    rcases hgLeft with ⟨u, hu⟩
    rcases hgRight with ⟨v, hv⟩
    refine ⟨a * u + b * v, ?_⟩
    calc
      L = L * 1 := by simp
      _ = L * (a * S + b * L ^ (p - 1)) := by rw [hab]
      _ = a * (L * S) + b * (L * L ^ (p - 1)) := by ring
      _ = g * (a * u + b * v) := by rw [hu, hv]; ring
  have hLg : L ∣ g :=
    EuclideanDomain.dvd_gcd (dvd_mul_right L S) (dvd_mul_right L (L ^ (p - 1)))
  have hassoc : Associated g L := associated_of_dvd_dvd hgL hLg
  change normalize g = L
  have hLmonic : L.Monic := by simpa [L] using Polynomial.monic_X_sub_C beta
  rw [← hLmonic.normalize_eq_self]
  exact (normalize_eq_normalize_iff_associated).mpr hassoc

/-- The computed gcd is exactly the linear factor of the proof-side root. -/
theorem frobeniusRootGCD_eq_reference :
    frobeniusRootGCD p f =
      CPolynomial.X - CPolynomial.C (frobeniusReferenceBeta p f) := by
  apply gcdMonic_eq_X_sub_C_of_simple_root p
  · exact frobeniusReferenceBeta_pow p f
  · simpa [CPolynomial.eval_toPoly] using
      eval_regroupPolynomial_referenceBeta_eq_zero p f
  · exact eval_derivative_regroupPolynomial_referenceBeta_ne_zero p f

/-- Constant-coefficient extraction recovers the root of the computed gcd. -/
theorem frobeniusBeta_eq_reference :
    frobeniusBeta p f = frobeniusReferenceBeta p f := by
  rw [frobeniusBeta, frobeniusRootGCD_eq_reference]
  rw [CPolynomial.coeff_sub]
  have hX : (CPolynomial.X : CPolynomial (Carrier f)).coeff 0 = 0 := by
    rfl
  have hC : (CPolynomial.C (frobeniusReferenceBeta p f)).coeff 0 =
      frobeniusReferenceBeta p f := by
    simpa using (CPolynomial.coeff_C
      (r := frobeniusReferenceBeta p f) (i := 0))
  rw [hX, hC]
  simp

/-- The computed root satisfies the defining Frobenius equation. -/
theorem frobeniusBeta_pow :
    frobeniusBeta p f ^ p = frobeniusTheta p f := by
  rw [frobeniusBeta_eq_reference, frobeniusReferenceBeta_pow]

/-- The computed gcd is exactly `X - beta`, stated using the executable root. -/
theorem frobeniusRootGCD_eq_X_sub_C :
    frobeniusRootGCD p f = CPolynomial.X - CPolynomial.C (frobeniusBeta p f) := by
  rw [frobeniusBeta_eq_reference, frobeniusRootGCD_eq_reference]

/-- The computed callback is an inverse to the characteristic-`p` Frobenius map. -/
theorem inverseFrobenius_pow (a : Carrier f) :
    inverseFrobenius p f a ^ p = a := by
  rw [inverseFrobenius]
  rw [list_sum_pow_char]
  simp only [List.map_ofFn]
  rw [List.sum_ofFn]
  calc
    _ = ∑ r : Fin p, regroupCoefficient p f a.val r.val ^ p *
        frobeniusTheta p f ^ r.val := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [Function.comp_apply, frobeniusBetaPowers,
        Array.getElem_ofFn, mul_pow]
      rw [← pow_mul, Nat.mul_comm, pow_mul, frobeniusBeta_pow]
      ring
    _ = a := by
      simpa using sum_regroup_pow_mul_theta_eq p f a.val

/-- The one-time decoder guard packages the same proved callback, with no
per-element proof argument. -/
theorem boundedInverseFrobenius_pow (B : Nat) (hpB : p ≤ B) (a : Carrier f) :
    boundedInverseFrobenius p f B hpB a ^ p = a := by
  exact inverseFrobenius_pow p f a

/-- Package the bounded callback and its law once at the decoder branch. -/
def boundedInverseFrobeniusCertificate (B : Nat) (hpB : p ≤ B) :
    InverseFrobeniusCertificate p f B where
  inverse := boundedInverseFrobenius p f B hpB
  characteristic_le := hpB
  inverse_pow_characteristic := boundedInverseFrobenius_pow p f B hpB

end ArkLib.FiniteField.ExplicitConstruction
