/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Driver

/-!
# Degree bounds for labelled threshold products

A threshold product keeps one copy of every returned factor whose integer multiplicity is at
least the threshold. Exact labelled reconstruction therefore bounds its degree times the
threshold by the input degree.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver

open Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem filteredProduct_pow_dvd_factorProduct
    (threshold : ℕ) (factors : List (ℕ × CPolynomial F)) :
    (((factors.filter fun z => threshold ≤ z.1).map Prod.snd).prod) ^ threshold ∣
      factorProduct factors := by
  induction factors with
  | nil => simp [factorProduct]
  | cons z rest ih =>
      simp only [factorProduct, List.map_cons, List.prod_cons]
      by_cases hz : threshold ≤ z.1
      · have hz' : (decide (threshold ≤ z.1) : Bool) = true := decide_eq_true hz
        simp only [List.filter_cons, hz', ↓reduceIte, List.map_cons, List.prod_cons,
          mul_pow]
        exact mul_dvd_mul (pow_dvd_pow z.2 hz) ih
      · have hz' : (decide (threshold ≤ z.1) : Bool) = false := decide_eq_false hz
        simp only [List.filter_cons, hz', Bool.false_eq_true, ↓reduceIte]
        exact dvd_mul_of_dvd_right ih (z.2 ^ z.1)

private theorem cpoly_list_prod_monic (pieces : List (CPolynomial F))
    (hm : ∀ q ∈ pieces, q.monic) : pieces.prod.monic := by
  induction pieces with
  | nil =>
      change (1 : CPolynomial F).monic
      rw [monic_toPoly_iff, toPoly_one]
      exact Polynomial.monic_one
  | cons q rest ih =>
      rw [monic_toPoly_iff, List.prod_cons, toPoly_mul]
      exact ((monic_toPoly_iff q).mp (hm q (by simp))).mul
        ((monic_toPoly_iff rest.prod).mp (ih (fun a ha => hm a (by simp [ha]))))

/-- For every successful decomposition, the squarefree threshold product uses at most the input
degree divided by the threshold. The statement also covers threshold zero. -/
theorem thresholdProduct_degree_le
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (threshold : ℕ)
    (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    threshold * (thresholdProduct M threshold out).natDegree ≤ f.natDegree := by
  have hs := decompose_sound p inverse M D f out hout
  have hm : ∀ z ∈ out.factors, z.2.monic := fun z hz => (hs.2.1 z hz).2.1
  have hthresholdEq := thresholdProduct_eq M threshold out hm
  have hselectedMonic :
      ∀ q ∈ (out.factors.filter fun z => threshold ≤ z.1).map Prod.snd, q.monic := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    exact hm z (List.mem_filter.mp hz).1
  have hthresholdMonic : (thresholdProduct M threshold out).monic := by
    rw [hthresholdEq]
    exact cpoly_list_prod_monic _ hselectedMonic
  have hdivFactors : (thresholdProduct M threshold out) ^ threshold ∣
      factorProduct out.factors := by
    rw [hthresholdEq]
    exact filteredProduct_pow_dvd_factorProduct threshold out.factors
  have hfactorDvdInput : factorProduct out.factors ∣ f := by
    refine ⟨C out.scalar, ?_⟩
    rw [mul_comm]
    exact hs.2.2.2.symm
  have hdivInput := hdivFactors.trans hfactorDvdInput
  have hdivPoly : ((thresholdProduct M threshold out) ^ threshold).toPoly ∣ f.toPoly := by
    obtain ⟨q, hq⟩ := hdivInput
    refine ⟨q.toPoly, ?_⟩
    simpa only [toPoly_pow, toPoly_mul] using congrArg CPolynomial.toPoly hq
  have hf0 : f.toPoly ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mpr (decompose_input_ne_zero p inverse M D f out hout)
  have hdegree := Polynomial.natDegree_le_of_dvd hdivPoly hf0
  rw [toPoly_pow, ((monic_toPoly_iff _).mp hthresholdMonic).natDegree_pow] at hdegree
  simpa only [← natDegree_toPoly] using hdegree

/-- The concrete supplied-field entrypoint inherits the threshold-product degree bound. -/
theorem decomposeSupplied_thresholdProduct_degree_le
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : ModContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (threshold : ℕ)
    (f : CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (out : Output (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hout : decomposeSupplied p modulus M D f = .ok out) :
    threshold * (thresholdProduct M threshold out).natDegree ≤ f.natDegree :=
  thresholdProduct_degree_le p
    (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius p modulus)
    M D threshold f out hout

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
