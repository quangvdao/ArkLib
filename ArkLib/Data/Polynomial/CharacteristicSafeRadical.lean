/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Frobenius
public import CompPoly.Univariate.Modular
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Characteristic-safe radical recursion

The executed recursion forms `v = f / gcd(f,f')`, removes all visible primary factors with
`gcd(f,v^D mod f)`, and contracts the remaining polynomial using the supplied inverse Frobenius.
It does not compute multiplicity labels. Termination follows from polynomial degree bounds,
independently of correctness of the supplied coefficient operation.

The two gcds classify the visible squarefree support and the derivative-zero residual.
Under the supplied inverse-power law, the total recursion returns a monic squarefree polynomial
with exactly the original roots after every coefficient-field extension.
-/

@[expose] public section

namespace CompPoly.CPolynomial.CharacteristicSafeRadical

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq

/-- Actual intermediate polynomials of one radical saturation step. -/
structure Step (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  common : CPolynomial F
  visible : CPolynomial F
  poweredRemainder : CPolynomial F
  removed : CPolynomial F
  residual : CPolynomial F

/-- Compute the two gcds and quotients prescribed by the radical recursion. -/
def saturate (f : CPolynomial F) : Step F :=
  let common := gcdMonic f f.derivative
  let visible := f.div common
  let poweredRemainder := powModWith .naive .remainderOnly f visible f.natDegree
  let removed := gcdMonic f poweredRemainder
  { common, visible, poweredRemainder, removed, residual := f.div removed }

private theorem div_gcdMonic_eq_complement (f g : CPolynomial F) (hf : f ≠ 0) :
    f.div (gcdMonic f g) = gcdComplement f g := by
  apply toPoly_injective
  rw [div_toPoly_eq_div, gcdComplement_toPoly hf,
    Polynomial.divByMonic_eq_div _ ((monic_toPoly_iff _).mp (gcdFactor_monic hf))]
  rfl

/-- Both actual quotients preserve monicity of the input. -/
theorem saturate_monic (f : CPolynomial F) (hf : f.monic) :
    (saturate f).visible.monic ∧ (saturate f).residual.monic := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  constructor
  · change (f.div (gcdMonic f f.derivative)).monic
    rw [div_gcdMonic_eq_complement _ _ hn]
    exact gcdComplement_monic hf
  · change (f.div (gcdMonic f _)).monic
    rw [div_gcdMonic_eq_complement _ _ hn]
    exact gcdComplement_monic hf

/-- Saturation retains an exact product identity with the full removed factor. -/
theorem removed_mul_residual (f : CPolynomial F) (hf : f ≠ 0) :
    (saturate f).removed * (saturate f).residual = f := by
  change gcdFactor f (saturate f).poweredRemainder *
    f.div (gcdMonic f (saturate f).poweredRemainder) = f
  rw [div_gcdMonic_eq_complement f (saturate f).poweredRemainder hf]
  exact gcdFactor_mul_gcdComplement hf

/-- A quotient cannot increase degree, including at malformed zero inputs. -/
theorem residual_degree_le (f : CPolynomial F) :
    (saturate f).residual.natDegree ≤ f.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly]
  change (f.div _).toPoly.natDegree ≤ f.toPoly.natDegree
  rw [div_toPoly_eq_div]
  exact Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le _ _)

/-- The concrete coefficient array for contraction has at most `D/p+1` entries. -/
theorem contract_degree_le (p : ℕ) (inverse : F → F) (f : CPolynomial F) :
    (FullSquarefreeDecomposition.contractWith p inverse f).natDegree ≤ f.natDegree / p := by
  rw [natDegree_toPoly, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [← coeff_toPoly, FullSquarefreeDecomposition.coeff_contractWith]
  simp [show ¬j < f.natDegree / p + 1 by omega]

/-- Every recursive argument strictly decreases degree when the characteristic is prime. -/
theorem recursive_degree_lt (p : ℕ) [Fact p.Prime] (inverse : F → F)
    (f : CPolynomial F) (hf : 0 < f.natDegree) :
    (FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual).natDegree <
      f.natDegree := by
  exact (contract_degree_le p inverse _).trans_lt
    ((Nat.div_le_div_right (residual_degree_le f)).trans_lt
      (Nat.div_lt_self hf (Fact.out : p.Prime).one_lt))

/-- Execute the characteristic-safe recursion with an explicit inverse-Frobenius operation.
The mathematical radical specification requires a monic input and the inverse-power law. -/
def radical (p : ℕ) [Fact p.Prime] (inverse : F → F) (f : CPolynomial F) : CPolynomial F :=
  if _hf : f.natDegree = 0 then 1
  else
    let step := saturate f
    if step.residual.natDegree = 0 then step.visible
    else step.visible * radical p inverse
        (FullSquarefreeDecomposition.contractWith p inverse step.residual)
termination_by f.natDegree
decreasing_by exact recursive_degree_lt p inverse f (Nat.pos_of_ne_zero _hf)

/-- The constant branch executes without invoking inverse Frobenius. -/
theorem radical_of_natDegree_zero (p : ℕ) [Fact p.Prime] (inverse : F → F)
    (f : CPolynomial F) (hf : f.natDegree = 0) : radical p inverse f = 1 := by
  rw [radical, dif_pos hf]

/-- The nonconstant branch exposes exactly the computed saturation and contracted recursion. -/
theorem radical_of_natDegree_pos (p : ℕ) [Fact p.Prime] (inverse : F → F)
    (f : CPolynomial F) (hf : 0 < f.natDegree) :
    radical p inverse f =
      if (saturate f).residual.natDegree = 0 then (saturate f).visible
      else (saturate f).visible * radical p inverse
        (FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual) := by
  rw [radical, dif_neg (Nat.ne_of_gt hf)]

/-- Supplied inverse Frobenius reconstructs a derivative-zero residual exactly; no
finite-field enumeration is needed. -/
theorem contracted_residual_pow (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hd : (saturate f).residual.derivative = 0) :
    FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual ^ p =
      (saturate f).residual :=
  FullSquarefreeDecomposition.contractWith_pow_eq p inverse hinverse _ hd

/-- Inverse-Frobenius contraction preserves the geometric zero set of a derivative-zero
residual over every extension field. -/
theorem contracted_residual_eval₂_eq_zero_iff (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hd : (saturate f).residual.derivative = 0)
    {K : Type*} [Field K] (base : F →+* K) (x : K) :
    (FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual).toPoly.eval₂
        base x = 0 ↔ (saturate f).residual.toPoly.eval₂ base x = 0 := by
  have heq := congrArg (fun q : CPolynomial F => q.toPoly.eval₂ base x)
    (contracted_residual_pow p inverse hinverse f hd)
  rw [toPoly_pow, Polynomial.eval₂_pow] at heq
  rw [← heq]
  exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).symm

/-- A nonconstant derivative-zero residual forces the characteristic below its degree.
This is the guard needed only when inverse Frobenius is reached. -/
theorem char_le_residual_degree (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hne : (saturate f).residual ≠ 0)
    (hpos : 0 < (saturate f).residual.natDegree)
    (hd : (saturate f).residual.derivative = 0) :
    p ≤ (saturate f).residual.natDegree := by
  let r := (saturate f).residual
  have hderiv : r.toPoly.derivative = 0 := by
    rw [← derivative_toPoly, hd, toPoly_zero]
  have hcoeff := Polynomial.coeff_derivative r.toPoly (r.natDegree - 1)
  have hcastadd : ((r.natDegree - 1 : ℕ) : F) + 1 = (r.natDegree : F) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : F))
        (Nat.sub_add_cancel (show 1 ≤ r.natDegree from hpos))
  rw [hderiv, Polynomial.coeff_zero,
    Nat.sub_add_cancel (show 1 ≤ r.natDegree from hpos),
    ← coeff_toPoly, hcastadd] at hcoeff
  have hlead : r.coeff r.natDegree ≠ 0 := by
    rw [coeff_toPoly, natDegree_toPoly, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr ((toPoly_eq_zero_iff r).not.mpr hne)
  have hcast : (r.natDegree : F) = 0 :=
    (mul_eq_zero.mp hcoeff.symm).resolve_left hlead
  exact Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p _).mp hcast)

/-- The recursive inverse-Frobenius branch inherits its characteristic guard from the
original input degree once the residual classification is established. -/
theorem char_le_input_degree (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hne : (saturate f).residual ≠ 0)
    (hpos : 0 < (saturate f).residual.natDegree)
    (hd : (saturate f).residual.derivative = 0) : p ≤ f.natDegree :=
  (char_le_residual_degree p f hne hpos hd).trans (residual_degree_le f)

private theorem normalize_monic_eq_self (f : CPolynomial F) (hf : f.monic) :
    monicNormalize f = f := by
  classical
  apply toPoly_injective
  rw [monicNormalize_toPoly_eq_normalize]
  exact ((monic_toPoly_iff f).mp hf).normalize_eq_self

private theorem map_remainder {S : Type*} [CommRing S] (φ : Polynomial F →+* S)
    (f a : CPolynomial F) (hf : f.monic) (hφ : φ f.toPoly = 0) :
    φ (a.modByMonic f).toPoly = φ a.toPoly := by
  rw [modByMonic_toPoly_eq_modByMonic _ _ hf,
    Polynomial.modByMonic_eq_sub_mul_div, map_sub, map_mul, hφ]
  simp

private theorem map_mulMod {S : Type*} [CommRing S] (φ : Polynomial F →+* S)
    (f a b : CPolynomial F) (hf : f.monic) (hφ : φ f.toPoly = 0) :
    φ (mulModWith .naive .remainderOnly f a b).toPoly = φ a.toPoly * φ b.toPoly := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hb : ¬(f == 0) = true := by simpa using hn
  simp only [mulModWith, MulContext.mul_eq_mul, if_neg hb,
    ModContext.modByMonic_eq_modByMonic, normalize_monic_eq_self f hf]
  rw [map_remainder φ f (a * b) hf hφ, toPoly_mul, map_mul]

private theorem map_binaryPower {S : Type*} [CommRing S] (φ : Polynomial F →+* S)
    (f : CPolynomial F) (hf : f.monic) (hφ : φ f.toPoly = 0) (n : ℕ)
    (acc current : CPolynomial F) :
    φ (powModBinaryAuxWith .naive .remainderOnly f n acc current).toPoly =
      φ acc.toPoly * φ current.toPoly ^ n := by
  induction n using Nat.strongRecOn generalizing acc current with
  | ind n ih =>
    cases n with
    | zero => simp [powModBinaryAuxWith]
    | succ n =>
      rw [powModBinaryAuxWith,
        ih ((n + 1) / 2) (Nat.div_lt_self (Nat.succ_pos n) (by decide)),
        map_mulMod φ f current current hf hφ]
      by_cases hodd : (n + 1) % 2 == 1
      · rw [if_pos hodd, map_mulMod φ f acc current hf hφ]
        have hp : (φ current.toPoly * φ current.toPoly) ^ ((n + 1) / 2) =
            φ current.toPoly ^ n := by
          rw [mul_pow, ← pow_add]
          congr 1
          have : (n + 1) % 2 = 1 := by simpa using hodd
          omega
        rw [hp, pow_succ]
        ring
      · rw [if_neg hodd]
        have hp : (φ current.toPoly * φ current.toPoly) ^ ((n + 1) / 2) =
            φ current.toPoly ^ (n + 1) := by
          rw [mul_pow, ← pow_add]
          congr 1
          have : (n + 1) % 2 ≠ 1 := by simpa using hodd
          omega
        rw [hp]

/-- Binary modular powering has the same image as ordinary powering in every quotient
annihilating the monic modulus. -/
theorem map_poweredRemainder {S : Type*} [CommRing S] (φ : Polynomial F →+* S)
    (f : CPolynomial F) (hf : f.monic) (hφ : φ f.toPoly = 0) :
    φ (saturate f).poweredRemainder.toPoly =
      φ (saturate f).visible.toPoly ^ f.natDegree := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hb : ¬(f == 0) = true := by simpa using hn
  change φ (powModWith .naive .remainderOnly f (saturate f).visible f.natDegree).toPoly = _
  simp only [powModWith, if_neg hb,
    ModContext.modByMonic_eq_modByMonic, normalize_monic_eq_self f hf]
  rw [map_binaryPower φ f hf hφ, map_remainder φ f 1 hf hφ, toPoly_one, map_one, one_mul]

/-- The second gcd is the gcd with the full power; binary modular reduction preserves it. -/
theorem removed_toPoly (f : CPolynomial F) (hf : f.monic) [DecidableEq F] :
    (saturate f).removed.toPoly =
      normalize (EuclideanDomain.gcd f.toPoly ((saturate f).visible.toPoly ^ f.natDegree)) := by
  have hcong : f.toPoly ∣ (saturate f).poweredRemainder.toPoly -
      (saturate f).visible.toPoly ^ f.natDegree := by
    apply AdjoinRoot.mk_eq_mk.mp
    rw [map_pow]
    exact map_poweredRemainder (AdjoinRoot.mk f.toPoly) f hf
      (AdjoinRoot.mk_eq_zero.mpr dvd_rfl)
  change (gcdFactor f (saturate f).poweredRemainder).toPoly = _
  rw [gcdFactor_toPoly]
  apply normalize_eq_normalize_iff_associated.mpr
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _)
    have hsub := (EuclideanDomain.gcd_dvd_left f.toPoly
      (saturate f).poweredRemainder.toPoly).trans hcong
    have hd := dvd_sub (EuclideanDomain.gcd_dvd_right f.toPoly
      (saturate f).poweredRemainder.toPoly) hsub
    simpa using hd
  · apply EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _)
    have hsub := (EuclideanDomain.gcd_dvd_left f.toPoly
      ((saturate f).visible.toPoly ^ f.natDegree)).trans hcong
    have hd := dvd_add hsub (EuclideanDomain.gcd_dvd_right f.toPoly
      ((saturate f).visible.toPoly ^ f.natDegree))
    simpa using hd

private theorem common_mul_visible (f : CPolynomial F) (hf : f ≠ 0) :
    (saturate f).common * (saturate f).visible = f := by
  change gcdFactor f f.derivative * f.div (gcdMonic f f.derivative) = f
  rw [div_gcdMonic_eq_complement f f.derivative hf]
  exact gcdFactor_mul_gcdComplement hf

open Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity in
/-- The two computed gcds classify visible squarefree support and the coprime residual. -/
theorem saturate_classification (f : CPolynomial F) (hf : f.monic) :
    Squarefree (saturate f).visible.toPoly ∧
      IsCoprime (saturate f).visible.toPoly (saturate f).residual.toPoly ∧
      Associated (UniqueFactorizationMonoid.radical f.toPoly)
        ((saturate f).visible.toPoly *
          UniqueFactorizationMonoid.radical (saturate f).residual.toPoly) := by
  classical
  have hA : f.toPoly ≠ 0 := ((monic_toPoly_iff f).mp hf).ne_zero
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp hA
  have hVC : Associated ((saturate f).visible.toPoly * (saturate f).common.toPoly)
      f.toPoly := by
    apply Associated.of_eq
    rw [mul_comm, ← toPoly_mul, common_mul_visible f hn]
  have hrepeat : EuclideanDomain.divRadical f.toPoly ∣ (saturate f).common.toPoly := by
    change _ ∣ (gcdFactor f f.derivative).toPoly
    rw [gcdFactor_toPoly, dvd_normalize_iff, derivative_toPoly]
    exact EuclideanDomain.dvd_gcd (EuclideanDomain.divRadical_dvd_self f.toPoly)
      (divRadical_dvd_derivative f.toPoly)
  have hvs := squarefree_of_divRadical_dvd_complement hA hVC hrepeat
  have hvd : (saturate f).visible.toPoly ∣ f.toPoly :=
    (dvd_mul_right _ _).trans hVC.dvd
  have hG : Associated (saturate f).removed.toPoly
      (EuclideanDomain.gcd f.toPoly ((saturate f).visible.toPoly ^ f.natDegree)) := by
    rw [removed_toPoly f hf]
    exact normalize_associated _
  have hRG : Associated ((saturate f).residual.toPoly * (saturate f).removed.toPoly)
      f.toPoly := by
    apply Associated.of_eq
    rw [mul_comm, ← toPoly_mul, removed_mul_residual f hn]
  have hs := Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity.boundedGcd_radical_split
    hA hvs hvd (fun q hq _ => by
      simpa only [natDegree_toPoly] using
        Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity.prime_multiplicity_le_natDegree
          hA hq) hG hRG
  exact ⟨hvs, hs⟩

/-- The actual saturation residual is derivative-zero, including mixed multiplicities. -/
theorem residual_derivative_eq_zero (f : CPolynomial F) (hf : f.monic) :
    (saturate f).residual.derivative = 0 := by
  classical
  let V := (saturate f).visible.toPoly
  let C := (saturate f).common.toPoly
  let G := (saturate f).removed.toPoly
  let R := (saturate f).residual.toPoly
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hVC : V * C = f.toPoly := by
    dsimp [V, C]
    rw [mul_comm, ← toPoly_mul, common_mul_visible f hn]
  have hGR : G * R = f.toPoly := by
    dsimp [G, R]
    rw [← toPoly_mul, removed_mul_residual f hn]
  have hcop : IsCoprime V R := (saturate_classification f hf).2.1
  have hGdvd : G ∣ V ^ f.natDegree := by
    dsimp [G, V]
    rw [removed_toPoly f hf]
    exact (normalize_associated _).dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hRGcop : IsCoprime R G :=
    hcop.symm.pow_right.of_isCoprime_of_dvd_right hGdvd
  have hRdvd : R ∣ f.toPoly := ⟨G, by rw [← hGR, mul_comm]⟩
  have hRC : R ∣ C := hcop.symm.dvd_of_dvd_mul_left (hVC ▸ hRdvd)
  have hCf : C ∣ f.toPoly.derivative := by
    dsimp [C]
    rw [← derivative_toPoly]
    exact gcdFactor_dvd_right f f.derivative
  have hRf : R ∣ f.toPoly.derivative := hRC.trans hCf
  have hRder : R ∣ R.derivative := by
    rw [← hGR, Polynomial.derivative_mul] at hRf
    have hprod : R ∣ G * R.derivative := by
      have hd := dvd_sub hRf (dvd_mul_left R G.derivative)
      simpa using hd
    exact hRGcop.dvd_of_dvd_mul_left hprod
  have hR0 : R ≠ 0 := ((monic_toPoly_iff _).mp (saturate_monic f hf).2).ne_zero
  have hd : R.derivative = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hRder
    (Polynomial.degree_derivative_lt hR0)
  apply toPoly_injective
  simpa only [derivative_toPoly, toPoly_zero] using hd

/-- The supplied inverse-power law preserves monicity when contracting a derivative-zero
monic residual. -/
theorem contracted_residual_monic (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hf : f.monic) :
    (FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual).monic := by
  have hp := congrArg CPolynomial.toPoly
    (contracted_residual_pow p inverse hinverse f (residual_derivative_eq_zero f hf))
  rw [toPoly_pow] at hp
  rw [monic_toPoly_iff]
  apply frobenius_inj F p
  change _ ^ p = (1 : F) ^ p
  rw [← Polynomial.leadingCoeff_pow, hp,
    ((monic_toPoly_iff _).mp (saturate_monic f hf).2).leadingCoeff]
  simp

private theorem monic_constant_eq_one (f : CPolynomial F) (hf : f.monic)
    (hd : f.natDegree = 0) : f.toPoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero ((monic_toPoly_iff f).mp hf)
    (by simpa only [natDegree_toPoly] using hd)

/-- The executed recursion is monic and associated to the mathematical radical. All geometric
classification premises are discharged by the two computed gcds. -/
theorem radical_monic_associated (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hf : f.monic) :
    (radical p inverse f).monic ∧
      Associated (radical p inverse f).toPoly (UniqueFactorizationMonoid.radical f.toPoly) := by
  induction hd : f.natDegree using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases hz : f.natDegree = 0
    · rw [radical_of_natDegree_zero p inverse f hz]
      have hone := monic_constant_eq_one f hf hz
      simp [monic_toPoly_iff, toPoly_one, hone]
    · have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hz
      rw [radical_of_natDegree_pos p inverse f hpos]
      have hclass := saturate_classification f hf
      have hmonic := saturate_monic f hf
      split_ifs with hR
      · refine ⟨hmonic.1, ?_⟩
        have hone := monic_constant_eq_one (saturate f).residual hmonic.2 hR
        have hs := hclass.2.2.symm
        simpa [hone] using hs
      · let q := FullSquarefreeDecomposition.contractWith p inverse (saturate f).residual
        have hq : q.monic := contracted_residual_monic p inverse hinverse f hf
        obtain ⟨hiq, hiaq⟩ := ih q.natDegree (hd ▸ recursive_degree_lt p inverse f hpos) q hq rfl
        have hpow : q.toPoly ^ p = (saturate f).residual.toPoly := by
          simpa only [toPoly_pow] using congrArg CPolynomial.toPoly
            (contracted_residual_pow p inverse hinverse f (residual_derivative_eq_zero f hf))
        have hrad : UniqueFactorizationMonoid.radical (saturate f).residual.toPoly =
            UniqueFactorizationMonoid.radical q.toPoly := by
          rw [← hpow, UniqueFactorizationMonoid.radical_pow _ (Fact.out : p.Prime).ne_zero]
        constructor
        · rw [monic_toPoly_iff, toPoly_mul]
          exact ((monic_toPoly_iff _).mp hmonic.1).mul ((monic_toPoly_iff _).mp hiq)
        · rw [toPoly_mul]
          have hs := hclass.2.2.symm
          rw [hrad] at hs
          exact ((Associated.refl (saturate f).visible.toPoly).mul_mul hiaq).trans hs

/-- The actual output is squarefree and monic under the supplied perfect-field operation. -/
theorem radical_squarefree_monic (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hf : f.monic) :
    Squarefree (radical p inverse f).toPoly ∧ (radical p inverse f).monic := by
  have hs := radical_monic_associated p inverse hinverse f hf
  exact ⟨hs.2.squarefree_iff.mpr UniqueFactorizationMonoid.squarefree_radical, hs.1⟩

/-- Radical execution preserves roots after every extension of the coefficient field. -/
theorem radical_eval₂_eq_zero_iff (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hf : f.monic)
    {K : Type*} [Field K] (base : F →+* K) (x : K) :
    (radical p inverse f).toPoly.eval₂ base x = 0 ↔ f.toPoly.eval₂ base x = 0 := by
  have hs := (radical_monic_associated p inverse hinverse f hf).2
  constructor
  · exact Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero base x
      (hs.dvd.trans UniqueFactorizationMonoid.radical_dvd_self)
  · intro hroot
    obtain ⟨n, hn⟩ := UniqueFactorizationMonoid.exists_dvd_radical_self_pow
      ((monic_toPoly_iff f).mp hf).ne_zero
    have hdvd : f.toPoly ∣ (radical p inverse f).toPoly ^ n :=
      hn.trans (pow_dvd_pow_of_dvd hs.dvd' n)
    have hpow := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero base x hdvd hroot
    rw [Polynomial.eval₂_pow] at hpow
    exact eq_zero_of_pow_eq_zero hpow

/-- The characteristic condition used for a nonconstant residual is derived from execution. -/
theorem recursive_characteristic_guard (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic)
    (hpos : 0 < (saturate f).residual.natDegree) : p ≤ f.natDegree := by
  have hr := (monic_toPoly_iff _).mp (saturate_monic f hf).2
  exact char_le_input_degree p f ((toPoly_eq_zero_iff _).not.mp hr.ne_zero) hpos
    (residual_derivative_eq_zero f hf)

/-- The radical divides the original polynomial, so the curve filter retains its degree bound. -/
theorem radical_degree_le (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (f : CPolynomial F) (hf : f.monic) :
    (radical p inverse f).natDegree ≤ f.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly]
  exact Polynomial.natDegree_le_of_dvd
    ((radical_monic_associated p inverse hinverse f hf).2.dvd.trans
      UniqueFactorizationMonoid.radical_dvd_self)
    ((monic_toPoly_iff f).mp hf).ne_zero

end CompPoly.CPolynomial.CharacteristicSafeRadical
