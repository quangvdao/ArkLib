/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Driver
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Failure elimination for labelled squarefree decomposition

This file proves that the bounded residue loop exhausts the separable quotient over a perfect
field and that the resulting weighted residue product divides the input exactly.
-/

@[expose] public section
namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
open Polynomial.FunctionFieldAlgorithms Polynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

theorem residueLoop_residual_eval₂_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (fuel r : ℕ) (a q : CPolynomial F) (ha : a.monic) (hs : Squarefree a.toPoly) :
    (residueLoop fuel r a q).residual.toPoly.eval₂ phi x = 0 ↔
      a.toPoly.eval₂ phi x = 0 ∧
        ∀ i < fuel, q.toPoly.eval₂ phi x ≠ ((r + i : ℕ) : K) := by
  induction fuel generalizing r a q with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    by_cases hunit : a = 1
    · simp [residueLoop, hunit, toPoly_one]
    · have ha0 : a ≠ 0 :=
        (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero
      let e := q - C (r : F)
      let next := gcdComplement a e
      have hnextMonic : next.monic := gcdComplement_monic ha
      have hnextFree : Squarefree next.toPoly := gcdComplement_squarefree ha0 hs
      rw [residueLoop, if_neg (by simpa only [beq_iff_eq] using hunit),
        ih (r + 1) next (q.modByMonic next) hnextMonic hnextFree]
      constructor
      · rintro ⟨hnextRoot, htail⟩
        have hsplit := (eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
          phi x ha0 hs).mp hnextRoot
        refine ⟨hsplit.1, ?_⟩
        intro i hi
        cases i with
        | zero =>
          simpa [e, toPoly_sub, toPoly_C, sub_ne_zero] using hsplit.2
        | succ i =>
          have hi' : i < fuel := by omega
          have htail' := htail i hi'
          have hrem := Polynomial.eval₂_modByMonic_eq_self_of_root
            (p := q.toPoly) (q := next.toPoly) hnextRoot
          rw [modByMonic_toPoly_eq_modByMonic _ _ hnextMonic, hrem] at htail'
          simpa [Nat.add_assoc, add_assoc, add_comm, add_left_comm] using htail'
      · rintro ⟨haRoot, hall⟩
        have hcurrent : e.toPoly.eval₂ phi x ≠ 0 := by
          simpa [e, toPoly_sub, toPoly_C, sub_ne_zero] using
            hall 0 (Nat.zero_lt_succ fuel)
        have hnextRoot := (eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
          phi x ha0 hs).mpr ⟨haRoot, hcurrent⟩
        refine ⟨hnextRoot, ?_⟩
        intro i hi
        have htail := hall (i + 1) (by omega)
        have hrem := Polynomial.eval₂_modByMonic_eq_self_of_root
          (p := q.toPoly) (q := next.toPoly) hnextRoot
        rw [modByMonic_toPoly_eq_modByMonic _ _ hnextMonic, hrem]
        simpa [Nat.add_assoc, add_assoc, add_comm, add_left_comm] using htail

theorem residueLoop_stratum_eval₂_eq
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (fuel r : ℕ) (a q : CPolynomial F) (ha : a.monic) (hs : Squarefree a.toPoly)
    (z : ℕ × CPolynomial F) (hz : z ∈ (residueLoop fuel r a q).strata)
    (hx : z.2.toPoly.eval₂ phi x = 0) :
    a.toPoly.eval₂ phi x = 0 ∧ q.toPoly.eval₂ phi x = (z.1 : K) := by
  induction fuel generalizing r a q z with
  | zero => simp [residueLoop] at hz
  | succ fuel ih =>
    by_cases hunit : a = 1
    · simp [residueLoop, hunit] at hz
    · let e := q - C (r : F)
      let next := gcdComplement a e
      simp only [residueLoop, beq_iff_eq, hunit, ↓reduceIte, List.mem_cons] at hz
      rcases hz with rfl | hz
      · have hg := (eval₂_gcdFactor_eq_zero_iff_left_right phi x a e).mp hx
        refine ⟨hg.1, ?_⟩
        simpa [e, toPoly_sub, toPoly_C, sub_eq_zero] using hg.2
      · have hnextMonic : next.monic := gcdComplement_monic ha
        have ha0 :=
          (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero
        have hnextFree := gcdComplement_squarefree (e := e) ha0 hs
        have hi := ih (r + 1) next (q.modByMonic next)
          hnextMonic hnextFree z hz hx
        have hnextRoot := hi.1
        have hsplit := (eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
          phi x
          ha0 hs).mp hnextRoot
        have hrem := Polynomial.eval₂_modByMonic_eq_self_of_root
          (p := q.toPoly) (q := next.toPoly) hnextRoot
        refine ⟨hsplit.1, ?_⟩
        rw [modByMonic_toPoly_eq_modByMonic _ _ hnextMonic, hrem] at hi
        exact hi.2

private theorem map_gcdFactor_eq_polynomial_gcd
    {K : Type*} [Field K] [DecidableEq K] (phi : F →+* K)
    (f g : CPolynomial F) :
    (gcdFactor f g).toPoly.map phi = gcd (f.toPoly.map phi) (g.toPoly.map phi) := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [gcdFactor_toPoly, Polynomial.map_normalize, ← Polynomial.gcd_map]
  have hass : Associated
      (EuclideanDomain.gcd (f.toPoly.map phi) (g.toPoly.map phi))
      (gcd (f.toPoly.map phi) (g.toPoly.map phi)) :=
    associated_of_dvd_dvd
      (dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _))
      (EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  calc
    _ = normalize (gcd (f.toPoly.map phi) (g.toPoly.map phi)) :=
      normalize_eq_normalize_iff_associated.mpr hass
    _ = _ := StrongNormalizedGCDMonoid.normalize_gcd _ _

theorem gcdComplement_rootMultiplicity_cast_ne_zero
    {K : Type*} [Field K] (phi : F →+* K)
    (f : CPolynomial F) (hf : f.monic) (x : K)
    (hx : ((gcdComplement f f.derivative).toPoly.map phi).IsRoot x) :
    ((f.toPoly.map phi).rootMultiplicity x : K) ≠ 0 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  let : DecidableEq K := Classical.decEq K
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hf0 : f.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr
      ((monic_toPoly_iff f).mp hf).ne_zero
  have hv0 : (gcdComplement f f.derivative).toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr
      ((monic_toPoly_iff _).mp (gcdComplement_monic hf)).ne_zero
  have hbase := congrArg CPolynomial.toPoly
    (gcdFactor_mul_gcdComplement (h := f) (e := f.derivative) hfn)
  have hmapped := congrArg (Polynomial.map phi) hbase
  simp only [toPoly_mul, Polynomial.map_mul] at hmapped
  rw [map_gcdFactor_eq_polynomial_gcd] at hmapped
  have hfactor :
      gcd (f.toPoly.map phi) (f.toPoly.map phi).derivative *
        (gcdComplement f f.derivative).toPoly.map phi = f.toPoly.map phi := by
    rw [Polynomial.derivative_map]
    rw [← derivative_toPoly]
    exact hmapped
  intro hm
  have hz := Multiplicity.derivative_quotient_rootMultiplicity_zero
    (f.toPoly.map phi) ((gcdComplement f f.derivative).toPoly.map phi)
    hf0 x hm hfactor
  have hp := (Polynomial.rootMultiplicity_pos hv0).mpr hx
  omega

theorem gcdComplement_rootMultiplicity_eq_one
    {K : Type*} [Field K] (phi : F →+* K)
    (f : CPolynomial F) (hf : f.monic) (x : K)
    (hx : (f.toPoly.map phi).IsRoot x)
    (hm : ((f.toPoly.map phi).rootMultiplicity x : K) ≠ 0) :
    ((gcdComplement f f.derivative).toPoly.map phi).rootMultiplicity x = 1 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  let : DecidableEq K := Classical.decEq K
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hf0 : f.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr
      ((monic_toPoly_iff f).mp hf).ne_zero
  have hbase := congrArg CPolynomial.toPoly
    (gcdFactor_mul_gcdComplement (h := f) (e := f.derivative) hfn)
  have hmapped := congrArg (Polynomial.map phi) hbase
  simp only [toPoly_mul, Polynomial.map_mul] at hmapped
  rw [map_gcdFactor_eq_polynomial_gcd] at hmapped
  have hfactor :
      gcd (f.toPoly.map phi) (f.toPoly.map phi).derivative *
        (gcdComplement f f.derivative).toPoly.map phi = f.toPoly.map phi := by
    rw [Polynomial.derivative_map, ← derivative_toPoly]
    exact hmapped
  exact Multiplicity.derivative_quotient_rootMultiplicity
    (f.toPoly.map phi) ((gcdComplement f f.derivative).toPoly.map phi)
    hf0 x hx hm hfactor

theorem residue_run_stratum_label_eq_rootMultiplicity_mod [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out)
    (z : ℕ × CPolynomial F) (hz : z ∈ out.strata)
    (hx : z.2.toPoly.eval₂ phi x = 0) :
    z.1 = (f.toPoly.map phi).rootMultiplicity x % p := by
  have hzBounds := residue_run_label_bounds p f out hout z hz
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [FullSquarefreeDecomposition.run, beq_iff_eq, hfn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    let v := (derivativeParts f).2.1
    have hvMonic : v.monic := gcdComplement_monic hf
    have hvFree : Squarefree v.toPoly := gcdDerivativeComplement_squarefree f hfn
    have hi := residueLoop_stratum_eval₂_eq phi x
      (min (p - 1) f.natDegree) 1 v q hvMonic hvFree z hz hx
    have hvRoot : ((gcdComplement f f.derivative).toPoly.map phi).IsRoot x := by
      change (v.toPoly.map phi).IsRoot x
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hi.1
    have hr := residuePolynomial?_eval₂_eq_rootMultiplicity phi f q hf x hvRoot hq
    have heval : q.toPoly.eval₂ phi x = (z.1 : K) := hi.2
    rw [heval] at hr
    let _ : CharP K p := charP_of_injective_ringHom phi.injective p
    have hmod : z.1 % p = (f.toPoly.map phi).rootMultiplicity x % p :=
      (CharP.cast_eq_iff_mod_eq K p).mp hr
    rw [Nat.mod_eq_of_lt hzBounds.2.1] at hmod
    exact hmod

theorem residue_run_stratum_label_le_rootMultiplicity [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out)
    (z : ℕ × CPolynomial F) (hz : z ∈ out.strata)
    (hx : z.2.toPoly.eval₂ phi x = 0) :
    z.1 ≤ (f.toPoly.map phi).rootMultiplicity x :=
  (residue_run_stratum_label_eq_rootMultiplicity_mod
    p phi x f hf out hout z hz hx).trans_le (Nat.mod_le _ _)

theorem residue_run_strata_monic_squarefree
    (p : ℕ) (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    ∀ z ∈ out.strata, z.2.monic ∧ Squarefree z.2.toPoly := by
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [FullSquarefreeDecomposition.run, beq_iff_eq, hfn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    let v := (derivativeParts f).2.1
    have hvMonic : v.monic := gcdComplement_monic hf
    have hvFree : Squarefree v.toPoly := gcdDerivativeComplement_squarefree f hfn
    intro z hz
    exact ⟨residueLoop_strata_monic _ _ v q hvMonic z hz,
      (residueLoop_squarefree _ _ v q hvMonic hvFree).2 z hz⟩

private theorem pow_dvd_of_geometric_rootMultiplicity
    [PerfectField F] (a f : CPolynomial F) (ha : a.monic)
    (hs : Squarefree a.toPoly) (hf0 : f.toPoly ≠ 0) (n : ℕ)
    (hroot : ∀ (x : AlgebraicClosure F),
      (a.toPoly.map (algebraMap F (AlgebraicClosure F))).IsRoot x →
        n ≤ (f.toPoly.map (algebraMap F (AlgebraicClosure F))).rootMultiplicity x) :
    a.toPoly ^ n ∣ f.toPoly := by
  let K := AlgebraicClosure F
  let phi : F →+* K := algebraMap F K
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  let : DecidableEq K := Classical.decEq K
  have ha0 : a.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr ((monic_toPoly_iff a).mp ha).ne_zero
  have hfmap0 : f.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr hf0
  apply (Polynomial.map_dvd_map phi phi.injective ((monic_toPoly_iff a).mp ha |>.pow n)).mp
  rw [Polynomial.map_pow]
  apply (IsAlgClosed.dvd_iff_roots_le_roots (pow_ne_zero n ha0) hfmap0).mpr
  rw [Multiset.le_iff_count]
  intro x
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    Polynomial.count_roots, Polynomial.count_roots]
  by_cases hx : (a.toPoly.map phi).IsRoot x
  · have hsep : (a.toPoly.map phi).Separable :=
      (PerfectField.separable_iff_squarefree.mpr hs).map
    have hm : (a.toPoly.map phi).rootMultiplicity x = 1 := by
      apply le_antisymm (Polynomial.rootMultiplicity_le_one_of_separable hsep x)
      exact (Polynomial.rootMultiplicity_pos ha0).mpr hx
    simpa [hm] using hroot x hx
  · rw [Polynomial.rootMultiplicity_eq_zero hx]
    simp

theorem residue_run_stratum_pow_dvd [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out)
    (z : ℕ × CPolynomial F) (hz : z ∈ out.strata) :
    z.2.toPoly ^ z.1 ∣ f.toPoly := by
  have hshape := residue_run_strata_monic_squarefree p f hf out hout z hz
  apply pow_dvd_of_geometric_rootMultiplicity z.2 f hshape.1 hshape.2
    ((monic_toPoly_iff f).mp hf).ne_zero z.1
  intro x hx
  apply residue_run_stratum_label_le_rootMultiplicity
    p (algebraMap F (AlgebraicClosure F)) x f hf out hout z hz
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using hx

theorem residue_run_residual_eq_one [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) : out.residual = 1 := by
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [FullSquarefreeDecomposition.run, beq_iff_eq, hfn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    let v := (derivativeParts f).2.1
    have hvMonic : v.monic := gcdComplement_monic hf
    have hv0 : v ≠ 0 :=
      (toPoly_eq_zero_iff v).not.mp ((monic_toPoly_iff v).mp hvMonic).ne_zero
    have hvFree : Squarefree v.toPoly := gcdDerivativeComplement_squarefree f hfn
    have hresMonic := residueLoop_residual_monic
      (min (p - 1) f.natDegree) 1 v q hvMonic
    change (residueLoop (min (p - 1) f.natDegree) 1 v q).residual = 1
    apply toPoly_injective
    rw [toPoly_one]
    apply Polynomial.eq_one_of_monic_natDegree_zero
      ((monic_toPoly_iff _).mp hresMonic)
    by_contra hdegree
    let K := AlgebraicClosure F
    let phi : F →+* K := algebraMap F K
    have hmapDegree :
        ((residueLoop (min (p - 1) f.natDegree) 1 v q).residual.toPoly.map phi).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective phi.injective]
      simpa [Polynomial.degree_eq_natDegree
        ((monic_toPoly_iff _).mp hresMonic).ne_zero] using hdegree
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
      ((residueLoop (min (p - 1) f.natDegree) 1 v q).residual.toPoly.map phi)
      hmapDegree
    have hxEval :
        (residueLoop (min (p - 1) f.natDegree) 1 v q).residual.toPoly.eval₂ phi x = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hx
    have hloop := (residueLoop_residual_eval₂_eq_zero_iff phi x
      (min (p - 1) f.natDegree) 1 v q hvMonic hvFree).mp hxEval
    have hvRoot : ((gcdComplement f f.derivative).toPoly.map phi).IsRoot x := by
      change (v.toPoly.map phi).IsRoot x
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hloop.1
    have hresidue := residuePolynomial?_eval₂_eq_rootMultiplicity phi f q hf x hvRoot hq
    let mappedF := f.toPoly.map phi
    have hmappedF0 : mappedF ≠ 0 :=
      (Polynomial.map_ne_zero_iff phi.injective).mpr ((monic_toPoly_iff f).mp hf).ne_zero
    have hmNonzero : (mappedF.rootMultiplicity x : K) ≠ 0 := by
      apply gcdComplement_rootMultiplicity_cast_ne_zero phi f hf x
      exact hvRoot
    let m := mappedF.rootMultiplicity x
    let residue := m % p
    have hresiduePos : 0 < residue := by
      by_contra hz
      have hz' : residue = 0 := Nat.eq_zero_of_not_pos hz
      apply hmNonzero
      rw [CharP.cast_eq_mod K p m]
      simp [residue, hz']
    have hresidueLt : residue < p := Nat.mod_lt m (Fact.out : Nat.Prime p).pos
    have hmLeDegree : m ≤ f.natDegree := by
      have hd := Polynomial.natDegree_le_of_dvd (mappedF.pow_rootMultiplicity_dvd x)
        hmappedF0
      rw [natDegree_toPoly]
      simpa [m, mappedF, Polynomial.natDegree_map] using hd
    have hindex : residue - 1 < min (p - 1) f.natDegree := by
      apply lt_min
      · omega
      · exact lt_of_lt_of_le (Nat.sub_lt (Nat.zero_lt_of_lt hresiduePos) (by decide))
          ((Nat.mod_le m p).trans hmLeDegree)
    have havoid := hloop.2 (residue - 1) hindex
    apply havoid
    rw [hresidue, CharP.cast_eq_mod K p m]
    congr 1
    omega

theorem residue_run_strata_product_eq_gcdComplement [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    (out.strata.map Prod.snd).prod = gcdComplement f f.derivative := by
  have hres := residue_run_residual_eq_one p f hf out hout
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [FullSquarefreeDecomposition.run, beq_iff_eq, hfn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    let v := (derivativeParts f).2.1
    have hvMonic : v.monic := gcdComplement_monic hf
    have hexact := residueLoop_exact (min (p - 1) f.natDegree) 1 v q hvMonic
    rw [hres, mul_one] at hexact
    exact hexact

theorem residue_run_strata_product_squarefree [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    Squarefree ((out.strata.map Prod.snd).prod).toPoly := by
  rw [residue_run_strata_product_eq_gcdComplement p f hf out hout]
  exact gcdDerivativeComplement_squarefree f
    ((toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero)

private theorem isCoprime_factorProduct_left
    (z : ℕ × CPolynomial F) (factors : List (ℕ × CPolynomial F))
    (hc : ∀ a ∈ factors, IsCoprime z.2.toPoly a.2.toPoly) :
    IsCoprime (z.2.toPoly ^ z.1) (factorProduct factors).toPoly := by
  induction factors with
  | nil => simpa [factorProduct, toPoly_one] using
      (isCoprime_one_right : IsCoprime (z.2.toPoly ^ z.1) 1)
  | cons a rest ih =>
    rw [factorProduct, List.map_cons, List.prod_cons, toPoly_mul, toPoly_pow]
    exact (hc a (by simp)).pow.mul_right
      (ih (fun b hb => hc b (by simp [hb])))

private theorem factorProduct_dvd_of_pairwise
    (f : CPolynomial F) (factors : List (ℕ × CPolynomial F))
    (hc : factors.Pairwise (fun a b => IsCoprime a.2.toPoly b.2.toPoly))
    (hd : ∀ z ∈ factors, z.2.toPoly ^ z.1 ∣ f.toPoly) :
    (factorProduct factors).toPoly ∣ f.toPoly := by
  induction factors with
  | nil => simp [factorProduct, toPoly_one]
  | cons z rest ih =>
    have hpair := List.pairwise_cons.mp hc
    rw [factorProduct, List.map_cons, List.prod_cons, toPoly_mul, toPoly_pow]
    exact (isCoprime_factorProduct_left z rest hpair.1).mul_dvd
      (hd z (by simp)) (ih hpair.2 (fun a ha => hd a (by simp [ha])))

theorem residue_run_factorProduct_dvd [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    (factorProduct out.strata).toPoly ∣ f.toPoly := by
  have hs := residue_run_strata_product_squarefree p f hf out hout
  have hc : out.strata.Pairwise
      (fun a b => IsCoprime a.2.toPoly b.2.toPoly) := by
    simpa only [List.pairwise_map] using
      pairwise_of_squarefree_product (out.strata.map Prod.snd) hs
  exact factorProduct_dvd_of_pairwise f out.strata hc
    (fun z hz => residue_run_stratum_pow_dvd p f hf out hout z hz)

theorem factorProduct_pruneTagged (pieces : List (ℕ × CPolynomial F)) :
    factorProduct (pruneTagged pieces) = factorProduct pieces := by
  induction pieces with
  | nil => rfl
  | cons z rest ih =>
    unfold pruneTagged at ih ⊢
    simp only [factorProduct] at ih ⊢
    by_cases hz : z.2 = 1
    · simp [hz, ih]
    · simp [hz, ih]

theorem residue_run_exactDivide_exists [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (M : MulContext F) (f : CPolynomial F) (hf : f.monic)
    (out : ResidueOutput F) (hout : FullSquarefreeDecomposition.run p f = some out) :
    ∃ repeated, exactDivide f (weightedProduct M (pruneTagged out.strata)) =
      some repeated := by
  have hshape := residue_run_strata_monic_squarefree p f hf out hout
  have hmonic : ∀ z ∈ pruneTagged out.strata, z.2.monic := by
    intro z hz
    exact (hshape z (List.mem_filter.mp hz).1).1
  have hproduct :
      weightedProduct M (pruneTagged out.strata) = factorProduct out.strata := by
    rw [weightedProduct_eq M _ hmonic, ← factorProduct]
    exact factorProduct_pruneTagged out.strata
  have hdvd : (weightedProduct M (pruneTagged out.strata)).toPoly ∣ f.toPoly := by
    rw [hproduct]
    exact residue_run_factorProduct_dvd p f hf out hout
  let divisor := weightedProduct M (pruneTagged out.strata)
  have hdivisor : divisor ≠ 0 := by
    intro hz
    have hf0 := ((monic_toPoly_iff f).mp hf).ne_zero
    have hzpoly : divisor.toPoly = 0 := (toPoly_eq_zero_iff divisor).mpr hz
    have hfzero : f.toPoly = 0 := (zero_dvd_iff.mp (by rw [← hzpoly]; exact hdvd))
    exact hf0 hfzero
  refine ⟨f.div divisor, (exactDivide_eq_some_iff _ _ _).mpr ⟨hdivisor, ?_⟩⟩
  apply toPoly_injective
  rw [toPoly_mul, div_toPoly_eq_div]
  rw [mul_comm]
  exact EuclideanDomain.mul_div_cancel'
    ((toPoly_eq_zero_iff divisor).not.mpr hdivisor) hdvd

private theorem derivative_eq_zero_of_geometric_rootMultiplicity_mod_eq_zero
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (g : CPolynomial F) (hg0 : g.toPoly ≠ 0)
    (hroot : ∀ x : AlgebraicClosure F,
      (g.toPoly.map (algebraMap F (AlgebraicClosure F))).rootMultiplicity x % p = 0) :
    g.derivative = 0 := by
  apply toPoly_injective
  rw [toPoly_zero, derivative_toPoly]
  by_contra hderiv
  let K := AlgebraicClosure F
  let phi : F →+* K := algebraMap F K
  let : DecidableEq K := Classical.decEq K
  have hgmap0 : g.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr hg0
  have hderivMap : (g.toPoly.map phi).derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    exact (Polynomial.map_ne_zero_iff phi.injective).mpr hderiv
  have hdvd : g.toPoly.map phi ∣ (g.toPoly.map phi).derivative := by
    apply (IsAlgClosed.dvd_iff_roots_le_roots hgmap0 hderivMap).mpr
    rw [Multiset.le_iff_count]
    intro x
    rw [Polynomial.count_roots, Polynomial.count_roots]
    by_cases hx : (g.toPoly.map phi).IsRoot x
    · obtain ⟨A, hA, _⟩ := (g.toPoly.map phi).exists_eq_pow_rootMultiplicity_mul_and_not_dvd
        hgmap0 x
      have hcast : ((g.toPoly.map phi).rootMultiplicity x : K) = 0 := by
        let _ : CharP K p := charP_of_injective_ringHom phi.injective p
        rw [CharP.cast_eq_mod K p, hroot x]
        simp
      have hpow : (Polynomial.X - Polynomial.C x) ^
          (g.toPoly.map phi).rootMultiplicity x ∣ (g.toPoly.map phi).derivative := by
        refine ⟨A.derivative, ?_⟩
        conv_lhs => rw [hA, Polynomial.derivative_mul,
          Polynomial.derivative_X_sub_C_pow]
        simp [hcast]
      exact (Polynomial.le_rootMultiplicity_iff hderivMap).mpr hpow
    · rw [Polynomial.rootMultiplicity_eq_zero hx]
      exact Nat.zero_le _
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd hderivMap
  exact (not_lt_of_ge hdegree) (Polynomial.natDegree_derivative_lt
    (by intro hzero; exact hderivMap (Polynomial.derivative_of_natDegree_zero hzero)))

private theorem rootMultiplicity_pow
    {K : Type*} [Field K] (a : Polynomial K) (ha : a ≠ 0) (x : K) (n : ℕ) :
    (a ^ n).rootMultiplicity x = n * a.rootMultiplicity x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero n ha) ha), ih, Nat.succ_mul]

private theorem factorProduct_ne_zero_of_monic
    (factors : List (ℕ × CPolynomial F))
    (hmonic : ∀ z ∈ factors, z.2.monic) :
    factorProduct factors ≠ 0 := by
  apply (toPoly_eq_zero_iff _).not.mp
  induction factors with
  | nil => simp [factorProduct, toPoly_one]
  | cons z rest ih =>
    change (z.2 ^ z.1 * factorProduct rest).toPoly ≠ 0
    rw [toPoly_mul, toPoly_pow]
    exact mul_ne_zero
      (pow_ne_zero _ ((monic_toPoly_iff z.2).mp (hmonic z (by simp))).ne_zero)
      (ih (fun a ha => hmonic a (by simp [ha])))

private theorem supportProduct_ne_zero_of_monic
    (factors : List (ℕ × CPolynomial F))
    (hmonic : ∀ z ∈ factors, z.2.monic) :
    (factors.map Prod.snd).prod ≠ 0 := by
  apply (toPoly_eq_zero_iff _).not.mp
  induction factors with
  | nil => simp [toPoly_one]
  | cons z rest ih =>
    change (z.2 * (rest.map Prod.snd).prod).toPoly ≠ 0
    rw [toPoly_mul]
    exact mul_ne_zero
      ((monic_toPoly_iff z.2).mp (hmonic z (by simp))).ne_zero
      (ih (fun a ha => hmonic a (by simp [ha])))

private theorem factorProduct_rootMultiplicity_eq_mul
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (factors : List (ℕ × CPolynomial F))
    (hmonic : ∀ z ∈ factors, z.2.monic) (n : ℕ)
    (hlabel : ∀ z ∈ factors, (z.2.toPoly.map phi).IsRoot x → z.1 = n) :
    ((factorProduct factors).toPoly.map phi).rootMultiplicity x =
      n * (((factors.map Prod.snd).prod).toPoly.map phi).rootMultiplicity x := by
  induction factors with
  | nil =>
    rw [factorProduct, List.map_nil, List.prod_nil, toPoly_one,
      Polynomial.map_one, List.map_nil, List.prod_nil, toPoly_one,
      Polynomial.map_one]
    simp [Polynomial.rootMultiplicity_eq_zero]
  | cons z rest ih =>
    have hz0 : z.2.toPoly.map phi ≠ 0 :=
      (Polynomial.map_ne_zero_iff phi.injective).mpr
        ((monic_toPoly_iff z.2).mp (hmonic z (by simp))).ne_zero
    have hrestMonic : ∀ a ∈ rest, a.2.monic :=
      fun a ha => hmonic a (by simp [ha])
    have hrest0 : ((factorProduct rest).toPoly.map phi) ≠ 0 := by
      exact (Polynomial.map_ne_zero_iff phi.injective).mpr
        ((toPoly_eq_zero_iff _).not.mpr
          (factorProduct_ne_zero_of_monic rest hrestMonic))
    have hrestSupport0 : (((rest.map Prod.snd).prod).toPoly.map phi) ≠ 0 := by
      exact (Polynomial.map_ne_zero_iff phi.injective).mpr
        ((toPoly_eq_zero_iff _).not.mpr
          (supportProduct_ne_zero_of_monic rest hrestMonic))
    have hzterm :
        z.1 * (z.2.toPoly.map phi).rootMultiplicity x =
          n * (z.2.toPoly.map phi).rootMultiplicity x := by
      by_cases hx : (z.2.toPoly.map phi).IsRoot x
      · rw [hlabel z (by simp) hx]
      · rw [Polynomial.rootMultiplicity_eq_zero hx]
        simp
    change (((z.2 ^ z.1) * factorProduct rest).toPoly.map phi).rootMultiplicity x =
      n * ((z.2 * (rest.map Prod.snd).prod).toPoly.map phi).rootMultiplicity x
    rw [toPoly_mul, Polynomial.map_mul, toPoly_pow, Polynomial.map_pow,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero z.1 hz0) hrest0),
      rootMultiplicity_pow _ hz0, toPoly_mul, Polynomial.map_mul,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hz0 hrestSupport0),
      ih hrestMonic (fun a ha => hlabel a (by simp [ha]))]
    rw [Nat.mul_add, hzterm]

theorem residue_run_factorProduct_rootMultiplicity_eq_mod [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (f : CPolynomial F) (hf : f.monic) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    ((factorProduct out.strata).toPoly.map phi).rootMultiplicity x =
      (f.toPoly.map phi).rootMultiplicity x % p := by
  let m := (f.toPoly.map phi).rootMultiplicity x
  have hshape := residue_run_strata_monic_squarefree p f hf out hout
  have hmul := factorProduct_rootMultiplicity_eq_mul phi x out.strata
    (fun z hz => (hshape z hz).1) (m % p)
    (fun z hz hzx => residue_run_stratum_label_eq_rootMultiplicity_mod
      p phi x f hf out hout z hz
        (by simpa [Polynomial.IsRoot, Polynomial.eval_map] using hzx))
  have hsupport := congrArg (fun a : CPolynomial F => a.toPoly.map phi)
    (residue_run_strata_product_eq_gcdComplement p f hf out hout)
  rw [hsupport] at hmul
  by_cases hresidue : m % p = 0
  · have hmul0 := hmul
    rw [hresidue] at hmul0
    have hwzero : ((factorProduct out.strata).toPoly.map phi).rootMultiplicity x = 0 := by
      simpa only [Nat.zero_mul] using hmul0
    change ((factorProduct out.strata).toPoly.map phi).rootMultiplicity x = m % p
    rw [hresidue]
    exact hwzero
  · have hfmap0 : f.toPoly.map phi ≠ 0 :=
      (Polynomial.map_ne_zero_iff phi.injective).mpr
        ((monic_toPoly_iff f).mp hf).ne_zero
    have hmpos : 0 < m := by
      by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      exact hresidue (by simp [this])
    have hx : (f.toPoly.map phi).IsRoot x :=
      (Polynomial.rootMultiplicity_pos hfmap0).mp hmpos
    let _ : CharP K p := charP_of_injective_ringHom phi.injective p
    have hmcast : (m : K) ≠ 0 := by
      intro hzero
      apply hresidue
      have hcastResidue : ((m % p : ℕ) : K) = 0 := by
        rw [← CharP.cast_eq_mod K p m]
        exact hzero
      exact Nat.eq_zero_of_dvd_of_lt
        ((CharP.cast_eq_zero_iff K p (m % p)).mp hcastResidue)
        (Nat.mod_lt m (Fact.out : Nat.Prime p).pos)
    have hv := gcdComplement_rootMultiplicity_eq_one phi f hf x hx (by simpa [m] using hmcast)
    simpa [hv] using hmul

theorem residue_run_repeated_derivative_eq_zero [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (M : MulContext F) (f : CPolynomial F) (hf : f.monic)
    (out : ResidueOutput F) (hout : FullSquarefreeDecomposition.run p f = some out)
    (repeated : CPolynomial F)
    (hdivide : exactDivide f (weightedProduct M (pruneTagged out.strata)) =
      some repeated) :
    repeated.derivative = 0 := by
  have hshape := residue_run_strata_monic_squarefree p f hf out hout
  have hmonic : ∀ z ∈ pruneTagged out.strata, z.2.monic := by
    intro z hz
    exact (hshape z (List.mem_filter.mp hz).1).1
  have hproduct :
      weightedProduct M (pruneTagged out.strata) = factorProduct out.strata := by
    rw [weightedProduct_eq M _ hmonic, ← factorProduct]
    exact factorProduct_pruneTagged out.strata
  have hexact := (exactDivide_eq_some_iff _ _ _).mp hdivide
  have hrep0 : repeated.toPoly ≠ 0 := by
    intro hz
    have hfzero := congrArg CPolynomial.toPoly hexact.2
    rw [toPoly_mul, hz] at hfzero
    have hzeroMul : (0 : Polynomial F) *
        (weightedProduct M (pruneTagged out.strata)).toPoly = 0 := by ring
    have : f.toPoly = 0 := hfzero.symm.trans hzeroMul
    exact ((monic_toPoly_iff f).mp hf).ne_zero this
  apply derivative_eq_zero_of_geometric_rootMultiplicity_mod_eq_zero p repeated hrep0
  intro x
  let K := AlgebraicClosure F
  let phi : F →+* K := algebraMap F K
  have hfactor := congrArg (fun a : CPolynomial F => a.toPoly.map phi) hexact.2
  rw [toPoly_mul, Polynomial.map_mul, hproduct] at hfactor
  have hrepMap0 : repeated.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).mpr hrep0
  have hproductMap0 : (factorProduct out.strata).toPoly.map phi ≠ 0 := by
    have hdivisor0 : weightedProduct M (pruneTagged out.strata) ≠ 0 := hexact.1
    apply (Polynomial.map_ne_zero_iff phi.injective).mpr
    apply (toPoly_eq_zero_iff _).not.mpr
    simpa [hproduct] using hdivisor0
  have hadd := Polynomial.rootMultiplicity_mul
    (x := x) (mul_ne_zero hrepMap0 hproductMap0)
  rw [hfactor,
    residue_run_factorProduct_rootMultiplicity_eq_mod p phi x f hf out hout] at hadd
  have hrepeated :
      (repeated.toPoly.map phi).rootMultiplicity x =
        (f.toPoly.map phi).rootMultiplicity x -
          (f.toPoly.map phi).rootMultiplicity x % p := by
    omega
  rw [hrepeated]
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.mod_mod]

/-- Every checked preparation branch succeeds on monic input over a perfect field. -/
theorem prepare_succeeds [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (M : MulContext F) (f : CPolynomial F) (hf : f.monic) :
    ∃ out, prepare p inverse M f = .ok out := by
  obtain ⟨residues, hr, _⟩ := run_exists_exact_of_perfect p hf
  have hresidual := residue_run_residual_eq_one p f hf residues hr
  obtain ⟨repeated, hdivide⟩ := residue_run_exactDivide_exists p M f hf residues hr
  have hderivative :=
    residue_run_repeated_derivative_eq_zero p M f hf residues hr repeated hdivide
  refine ⟨⟨pruneTagged residues.strata, contractWith p inverse repeated⟩, ?_⟩
  simp [prepare, hr, hresidual, hdivide, hderivative]

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
