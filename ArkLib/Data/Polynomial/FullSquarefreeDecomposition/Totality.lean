/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.RefinementSuccess

/-! # Unconditional success of full labelled squarefree decomposition -/

@[expose] public section
namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
open Polynomial.FunctionFieldAlgorithms Polynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Internal recursive invariant: normalized nonunit factors with positive labels and squarefree
joint support. -/
def FactorValidity (factors : List (ℕ × CPolynomial F)) : Prop :=
  (∀ z ∈ factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1) ∧
    Squarefree ((factors.map Prod.snd).prod).toPoly

private theorem validFactors_nodup {factors : List (ℕ × CPolynomial F)}
    (hv : FactorValidity factors) : (factors.map Prod.snd).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hp := pairwise_of_squarefree_product (factors.map Prod.snd) hv.2
  simpa only [List.pairwise_map] using hp.imp_of_mem (fun {a b} ha hb hab heq => by
    subst b
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    have hu : IsUnit z.2.toPoly := isCoprime_self.mp hab
    have hone : z.2.toPoly = 1 :=
      ((monic_toPoly_iff z.2).mp (hv.1 z hz).2.1).eq_one_of_isUnit hu
    exact (hv.1 z hz).2.2 (toPoly_injective (by simpa [toPoly_one] using hone)))

private theorem checkFactors_complete [PerfectField F]
    (M : MulContext F) (factors : List (ℕ × CPolynomial F))
    (hv : FactorValidity factors) : checkFactors M factors = true := by
  let support := weightedProduct M (factors.map fun z => (1, z.2))
  have hsupport : support = (factors.map Prod.snd).prod := by
    dsimp [support]
    rw [weightedProduct_eq]
    · simp [List.map_map, Function.comp_def]
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact (hv.1 a ha).2.1
  have hsep : support.toPoly.Separable := by
    rw [hsupport]
    exact PerfectField.separable_iff_squarefree.mpr hv.2
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hg : gcdFactor support support.derivative = 1 := by
    apply toPoly_injective
    rw [gcdFactor_toPoly, toPoly_one, normalize_eq_one]
    apply (EuclideanDomain.gcd_isUnit_iff).2
    rw [derivative_toPoly]
    exact (Polynomial.separable_def support.toPoly).mp hsep
  rw [checkFactors, Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr ?_, ?_⟩
  · intro z hz
    have hs := hv.1 z hz
    simpa [Bool.and_eq_true, and_assoc, bne_iff_ne] using hs
  · dsimp
    simpa only [beq_iff_eq] using hg

private theorem prepare_strata_valid [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (M : MulContext F) (f : CPolynomial F)
    (out : Preparation F) (hf : f.monic) (hout : prepare p inverse M f = .ok out) :
    (∀ z ∈ out.strata, 0 < z.1 ∧ z.2.monic) ∧
      Squarefree ((out.strata.map Prod.snd).prod).toPoly := by
  obtain ⟨residues, repeated, hr, _, hstrata, _, _, _⟩ :=
    prepare_spec p inverse M f out hout
  constructor
  · intro z hz
    rw [hstrata] at hz
    exact ⟨(residue_run_label_bounds p f residues hr z (List.mem_filter.mp hz).1).1,
      (residue_run_strata_monic_squarefree p f hf residues hr z
        (List.mem_filter.mp hz).1).1⟩
  · rw [hstrata, pruneTagged_erase, prune_prod]
    exact residue_run_strata_product_squarefree p f hf residues hr

/-- The recursive monic producer succeeds, reconstructs its input, and returns factors that pass
the full shape and squarefree-support invariant. -/
theorem decomposeMonic_succeeds [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (M : MulContext F) (D : ModContext F) (f : CPolynomial F) (hf : f.monic) :
    ∃ out, decomposeMonic p inverse M D f = .ok out ∧
      factorProduct out.factors = f ∧ FactorValidity out.factors := by
  induction hdegree : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
      rw [decomposeMonic]
      have hpguard : ¬p ≤ 1 := Nat.not_le_of_lt (Fact.out : Nat.Prime p).one_lt
      rw [if_neg hpguard]
      simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hfunit : f = 1
      · rw [if_pos (by simpa only [beq_iff_eq] using hfunit)]
        subst f
        refine ⟨⟨[], []⟩, rfl, ?_, ?_⟩
        · simp [factorProduct]
        · simp [FactorValidity, toPoly_one]
      · rw [if_neg (by simpa only [beq_iff_eq] using hfunit)]
        obtain ⟨prepared, hprepare⟩ := prepare_succeeds p inverse M f hf
        rw [hprepare]
        have hlt := prepare_contracted_natDegree_lt
          p inverse hinverse M f prepared hf hfunit hprepare
        dsimp only [Bind.bind, Except.bind]
        rw [dif_pos hlt]
        have hcontractedMonic := (prepare_monic p inverse hinverse M f prepared hf hprepare).2
        obtain ⟨recursive, hrecursive, hreconstruct, hrecursiveValid⟩ :=
          ih prepared.contracted.natDegree (by simpa [hdegree] using hlt)
            prepared.contracted hcontractedMonic rfl
        rw [hrecursive]
        dsimp only [Bind.bind, Except.bind]
        have hstrataValid := prepare_strata_valid p inverse M f prepared hf hprepare
        obtain ⟨factors, hrefine⟩ := refineFactors_succeeds p M D
          prepared.strata recursive.factors
          (fun z hz => (hstrataValid.1 z hz).2) hstrataValid.2
          (fun z hz => (hrecursiveValid.1 z hz).2.1)
        rw [hrefine]
        have hrecursiveNodup := validFactors_nodup hrecursiveValid
        have hrefineReconstruct := refineFactors_reconstruct p M D
          prepared.strata recursive.factors factors
          (fun z hz => (hstrataValid.1 z hz).2) hrecursiveNodup hrefine
        have hfactor : factorProduct factors = f := by
          rw [hrefineReconstruct, hreconstruct]
          have hprep := prepare_reconstruct p inverse hinverse M f prepared hprepare
          rw [weightedProduct_eq M prepared.strata
            (fun z hz => (hstrataValid.1 z hz).2)] at hprep
          exact hprep
        dsimp only
        rw [if_neg (by
          simpa only [bne_iff_ne] using
            (show ¬factorProduct factors ≠ f from fun h => h hfactor))]
        have hshape := refineFactors_positive_monic p (Fact.out : Nat.Prime p).pos
          M D prepared.strata recursive.factors factors hstrataValid.1
          (fun z hz => ⟨(hrecursiveValid.1 z hz).1,
            (hrecursiveValid.1 z hz).2.1⟩) hrefine
        have hsupport := refineFactors_support_squarefree p M D
          prepared.strata recursive.factors factors
          (fun z hz => (hstrataValid.1 z hz).2) hstrataValid.2
          (fun z hz => (hrecursiveValid.1 z hz).2.1) hrecursiveValid.2
          hrecursiveNodup hrefine
        exact ⟨⟨factors, ⟨f.natDegree, prepared.contracted.natDegree,
          prepared.strata.map Prod.fst⟩ :: recursive.stages⟩,
          rfl, hfactor, ⟨hshape, hsupport⟩⟩

private theorem leadingCoeff_inv_smul_monic (f : CPolynomial F) (hf : f ≠ 0) :
    (f.leadingCoeff⁻¹ • f).monic := by
  rw [monic_toPoly_iff, toPoly_smul, leadingCoeff_toPoly,
    Polynomial.smul_eq_C_mul, mul_comm]
  exact Polynomial.monic_mul_leadingCoeff_inv ((toPoly_eq_zero_iff f).not.mpr hf)

private theorem leadingCoeff_mul_inv_smul (f : CPolynomial F) (hf : f ≠ 0) :
    C f.leadingCoeff * (f.leadingCoeff⁻¹ • f) = f := by
  apply toPoly_injective
  rw [toPoly_mul, toPoly_C, toPoly_smul, leadingCoeff_toPoly,
    Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul]
  have hlc : f.toPoly.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr ((toPoly_eq_zero_iff f).not.mpr hf)
  rw [mul_inv_cancel₀ hlc, Polynomial.C_1, one_mul]

/-- Full decomposition succeeds on every nonzero polynomial over a perfect field when supplied
with a certified inverse Frobenius callback. -/
theorem decompose_succeeds [PerfectField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a)
    (M : MulContext F) (D : ModContext F) (f : CPolynomial F) (hf : f ≠ 0) :
    ∃ out, decompose p inverse M D f = .ok out := by
  let g := f.leadingCoeff⁻¹ • f
  have hgmonic : g.monic := leadingCoeff_inv_smul_monic f hf
  obtain ⟨monicOut, hmonicOut, hreconstruct, hvalid⟩ :=
    decomposeMonic_succeeds p inverse hinverse M D g hgmonic
  have hcheck := checkFactors_complete M monicOut.factors hvalid
  have hglobal : C f.leadingCoeff * factorProduct monicOut.factors = f := by
    rw [hreconstruct]
    exact leadingCoeff_mul_inv_smul f hf
  refine ⟨⟨f.leadingCoeff, monicOut.factors, monicOut.stages⟩, ?_⟩
  unfold decompose
  rw [if_neg (by simpa only [beq_iff_eq] using hf)]
  change (match decomposeMonic p inverse M D g with
    | Except.error err => Except.error err
    | Except.ok out =>
      if !checkFactors M out.factors then Except.error Failure.factorCertificate
      else if C f.leadingCoeff * factorProduct out.factors != f then
        Except.error Failure.reconstruction
      else Except.ok (Output.mk f.leadingCoeff out.factors out.stages)) = _
  rw [hmonicOut]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by
    simpa only [bne_iff_ne] using
      (show ¬C f.leadingCoeff * factorProduct monicOut.factors ≠ f from
        fun h => h hglobal))]

/-- Prime-field decomposition succeeds on every nonzero input. -/
theorem decomposePrime_succeeds
    (p : ℕ) [Fact p.Prime]
    (M : MulContext (ZMod p)) (D : ModContext (ZMod p))
    (f : CPolynomial (ZMod p)) (hf : f ≠ 0) :
    ∃ out, decomposePrime p M D f = .ok out :=
  decompose_succeeds p id (fun a => ZMod.pow_card a) M D f hf

/-- Zero has the explicit failure semantics rather than an empty factorization. -/
theorem decompose_zero
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F) :
    decompose p inverse M D (0 : CPolynomial F) = .error .zeroInput := by
  simp [decompose]

/-- A nonzero constant is returned as the scalar with no factors or recursive stages. -/
theorem decompose_constant
    [PerfectField F] (p : ℕ) [Fact p.Prime]
    (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (a : F) (ha : a ≠ 0) :
    decompose p inverse M D (C a) = .ok ⟨a, [], []⟩ := by
  have hlc : (C a : CPolynomial F).leadingCoeff = a := by
    rw [leadingCoeff_toPoly, toPoly_C, Polynomial.leadingCoeff_C]
  have hnormalize : a⁻¹ • (C a : CPolynomial F) = 1 := by
    apply toPoly_injective
    rw [toPoly_smul, toPoly_C, Polynomial.smul_eq_C_mul, ← Polynomial.C_mul,
      inv_mul_cancel₀ ha, Polynomial.C_1, toPoly_one]
  have hmonic : decomposeMonic p inverse M D (1 : CPolynomial F) = .ok ⟨[], []⟩ := by
    have honeMonic : (1 : CPolynomial F).monic = true := by
      rw [monic_toPoly_iff]
      simp [toPoly_one]
    rw [decomposeMonic]
    rw [if_neg (Nat.not_le_of_lt (Fact.out : Nat.Prime p).one_lt)]
    simp only [honeMonic, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      beq_self_eq_true]
    rfl
  have hcne : (C a : CPolynomial F) ≠ 0 := by
    intro h
    apply ha
    have hc := congrArg (fun q : CPolynomial F => q.toPoly.coeff 0) h
    simpa [toPoly_C, toPoly_zero] using hc
  have hvalid : FactorValidity ([] : List (ℕ × CPolynomial F)) := by
    simp [FactorValidity, toPoly_one]
  have hcheck : checkFactors M ([] : List (ℕ × CPolynomial F)) = true :=
    checkFactors_complete M [] hvalid
  unfold decompose
  rw [if_neg (by simpa only [beq_iff_eq] using hcne)]
  rw [hlc, hnormalize, hmonic]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by simp [factorProduct])]

/-- The concrete supplied polynomial-basis field path succeeds without an inverse oracle. -/
theorem decomposeSupplied_succeeds
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : ModContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (f : CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hf : f ≠ 0) :
    ∃ out, decomposeSupplied p modulus M D f = .ok out := by
  exact decompose_succeeds p
    (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius p modulus)
    (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius_pow p modulus) M D f hf

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
