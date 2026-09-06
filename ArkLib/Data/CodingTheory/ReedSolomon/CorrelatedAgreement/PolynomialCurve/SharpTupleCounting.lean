/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.GraphCounting
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.TaylorChart.SharpPairCounting

/-!
# Sharp counting of admissible polynomial tuples

A generic batching challenge injects a finite admissible tuple family into one ordinary Taylor
chart.  Applying the sharp chart count retains the exact graph-count ratio

```text
(n-k+1) / (L-k+1),
```

independently of the batching degree.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

private theorem jetDegree_pos_of_initialSeparant_ne_zero_sharpTuple (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- Any finite family of admissible polynomial tuples at exponent `τ` obeys the sharp
graph-count ratio after one common regular batching specialization. -/
theorem admissibleChartTuples_card_le_sharp_of_exponent [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ (v : ℚ) *
      ((((((n - k + 1) * (1 + τ * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (symbolicSourceSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_polynomialTuple_specialization_injective_avoiding_roots (ℓ := ℓ)
      iota tuples ∅ auxiliary (by
      intro R hR
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hR
      exact (htuples P hP).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin (r + 1) → E) := tuples.image (chartTupleJet iota center z)
  have hspec (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (htuples P hP).specialize hτ hkK z
      (havoid _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hjetinj : Set.InjOn (chartTupleJet (r := r) iota center z)
      (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    apply hinj hP hR
    change powerBatchedPolynomial (fun t ↦ (P t).map iota) z =
      powerBatchedPolynomial (fun t ↦ (R t).map iota) z
    rw [← (hspec P hP).2.2.2, ← (hspec R hR).2.2.2, heq]
  have hcard : jets.card = tuples.card := Finset.card_image_of_injOn hjetinj
  obtain ⟨P₀, hP₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsep : initialJetSeparant center Qz ≠ 0 := by
    intro hz
    exact (hspec P₀ hP₀).2.1 (by rw [hz]; simp)
  have hvz := jetDegree_pos_of_initialSeparant_ne_zero_sharpTuple center Qz hsep
  let domainE : Fin n ↪ E := mappedDomain domain iota
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hbound := finite_regularHighCutJets_card_le_sharp_of_exponent
    center Qz K k τ hτ hK hsep hvz
    domainE received hk hkL hLn jets (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      exact ⟨(hspec P hP).1, (hspec P hP).2.1,
        fun l ↦ (hspec P hP).2.2.1 l.val l.property⟩) (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      apply (htuples P hP).common.trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, taylorAgreementEquation_eq_zero_iff_of_exponent
        _ _ _ τ hτ _ (hspec P hP).2.1, (hspec P hP).2.2.2]
      have hi' : ∀ t, (P t).eval (domain i) = w t i := by
        simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
          (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
      rw [powerBatchedPolynomial_eval]
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t])
  rw [hcard] at hbound
  apply hbound.trans
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz K (τ := τ) ≤ 1 + τ * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply mul_le_mul
  · exact_mod_cast hvle
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left (n - k + 1) hB
  · positivity
  · positivity

/-- Compatibility form of the tuple-counting theorem at exponent `2K`. -/
theorem admissibleChartTuples_card_le_sharp [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples, IsAdmissibleChartTuple domain w iota center Q K k L P) :
    (tuples.card : ℚ) ≤ (v : ℚ) *
      ((((((n - k + 1) * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  apply admissibleChartTuples_card_le_sharp_of_exponent domain w iota center Q
    K k L v (2 * K) (taylorExponentSufficient_two_mul r K)
      hK hkK hk hkL hLn hjet tuples
  intro P hP
  exact ⟨(htuples P hP).degree, (htuples P hP).common,
    (htuples P hP).initial, (htuples P hP).high,
    (htuples P hP).regular, (htuples P hP).reconstruction⟩

/-- The complete finite admissible tuple family obeys the sharp graph-count ratio. -/
theorem admissibleChartTupleFamily_card_le_sharp [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ((admissibleChartTupleFamily domain w iota center Q K k L).card : ℚ) ≤ (v : ℚ) *
      ((((((n - k + 1) * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  apply admissibleChartTuples_card_le_sharp domain w iota center Q K k L v
    hK hkK hk hkL hLn hjet
  intro P hP
  exact (mem_admissibleChartTupleFamily_iff domain w iota center Q K k L hkL P).mp hP

end ReedSolomon
