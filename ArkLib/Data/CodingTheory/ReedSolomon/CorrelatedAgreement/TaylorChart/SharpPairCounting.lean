/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.TaylorChart.PairCounting
import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpPrimeFamily

/-!
# Sharp counting of admissible Taylor-chart pairs

The generic sharp incidence theorem retains the number of non-identically-zero cuts at every
stage.  Applying it to the ordinary Taylor chart replaces the numerator `n` in the pair-family
bound by `n-k+1`.  Thus its sampling ratio is

```text
(n-k+1) / (L-k+1).
```
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial AffineHilbert
open scoped BigOperators

variable {F : Type*} [Field F] {r : ℕ}

/-- Finite regular high-cut jets obey the sharp ordinary-chart incidence ratio. -/
theorem finite_regularHighCutJets_card_le_sharp
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i)) jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((((n - k + 1) * rationalTaylorCutDegreeBound Q K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ^ r) := by
  classical
  let B := rationalTaylorCutDegreeBound Q K
  let T := highTaylorPrimeFamily center Q K k
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) F := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i)
  let R : ℚ := (((n - k + 1) * B : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let t : ℚ := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hB : 0 < B := by simp [B, rationalTaylorCutDegreeBound]
  have hcNat : 0 < A - k + 1 := by omega
  have hcn : A - k + 1 ≤ n - k + 1 := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hcNat)).2
    simpa only [one_mul] using (show ((A - k + 1 : ℕ) : ℚ) ≤
      ((n - k + 1 : ℕ) : ℚ) by exact_mod_cast hcn)
  have hR : R = (B : ℚ) * t := by
    dsimp only [R, t]
    push_cast
    field_simp
  have hspec := highTaylorPrimeFamily_spec (F := F) (E := F) center Q K k
  have hcoverNat : S.card ≤
      ∑ P ∈ T, (componentPoints S P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ componentPoints S P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := hspec.2 jet
          (hS jet hjet).1 (hS jet hjet).2.1 (hS jet hjet).2.2
        exact Finset.mem_biUnion.mpr ⟨P, hPT, by
          rw [mem_componentPoints]
          exact ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (componentPoints S P).card := Finset.card_biUnion_le
  have hcover : (S.card : ℚ) ≤
      ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
    exact_mod_cast hcoverNat
  have hcomponent : ∀ P ∈ T,
      ((componentPoints S P).card : ℚ) ≤
        affineDegree P * R ^ (hilbertPolynomial P).natDegree := by
    intro P hPT
    have hPspec := hspec.1 P hPT
    apply affineAgreementIncidence_bound_sharp hPspec.1 hPspec.2.1
      cuts (fun i ↦ totalDegree_taylorAgreementEquation_le center Q hv K _ _)
      hB hk hkA hAn (componentPoints S P)
    · intro jet hjet
      rw [mem_componentPoints] at hjet
      exact ⟨hjet.2, (hS jet hjet.1).2.1⟩
    · intro jet hjet
      rw [mem_componentPoints] at hjet
      exact hA jet hjet.1
    · intro U hU jet jet' hjetP hjetS hjetP' hjetS' hzero
      apply eq_of_mem_principalOpen_of_highCuts_of_agreementFinset
        center Q K k hK P hPspec.2.2 domain received U hU
        ⟨hjetP, hjetS⟩ ⟨hjetP', hjetS'⟩
      · intro i hi
        exact (hzero i hi).1
      · intro i hi
        exact (hzero i hi).2
  have hpotential := sum_highTaylorPrimeFamily_affineDegree_mul_pow_le
    center Q hsep hv K k
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T,
        ((componentPoints S P).card : ℚ) := hcover
    _ ≤ ∑ P ∈ T, affineDegree P * R ^ (hilbertPolynomial P).natDegree :=
      Finset.sum_le_sum hcomponent
    _ = ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ (hilbertPolynomial P).natDegree := by
      apply Finset.sum_congr rfl
      intro P _
      rw [hR, mul_pow]
      ring
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ r := by
      apply Finset.sum_le_sum
      intro P hPT
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ ht
          (highTaylorPrimeFamily_hilbertPolynomial_natDegree_le center Q K k hinit hPT)
      · exact mul_nonneg (affineDegree_nonneg P) (by positivity)
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^
          (hilbertPolynomial P).natDegree) * t ^ r := by rw [Finset.sum_mul]
    _ ≤ (((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          (B : ℚ) ^ r) * t ^ r :=
      mul_le_mul_of_nonneg_right hpotential (by positivity)
    _ = ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          R ^ r := by
      rw [hR, mul_pow]
      ring

end ReedSolomon.HiddenDerivative

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

private theorem jetDegree_pos_of_initialSeparant_ne_zero_sharp (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- A finite family of admissible pair graphs obeys the sharp graph-count ratio. -/
theorem admissibleChartPairs_card_le_sharp [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (pairs : Finset (F[X] × F[X]))
    (hpairs : ∀ pair ∈ pairs, IsAdmissibleChartPair domain f g iota center Q K k L pair) :
    (pairs.card : ℚ) ≤ (v : ℚ) *
      ((((((n - k + 1) * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  classical
  by_cases hempty : pairs = ∅
  · subst pairs
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let aux := pairs.image fun pair ↦
    chartPairPullback iota center pair (symbolicSourceSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ := exists_correlatedPairSpecialization_injOn_avoiding_roots
    iota pairs ∅ aux (by
      intro R hR
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hR
      exact (hpairs pair hp).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin (r + 1) → E) := pairs.image (chartPairJet iota center z)
  have hspec (pair : F[X] × F[X]) (hp : pair ∈ pairs) :=
    (hpairs pair hp).specialize hkK z
      (havoid _ (Finset.mem_image.mpr ⟨pair, hp, rfl⟩))
  have hjetinj : Set.InjOn (chartPairJet (r := r) iota center z) (↑pairs) := by
    intro p hp q hq heq
    apply hinj hp hq
    rw [← (hspec p hp).2.2.2, ← (hspec q hq).2.2.2, heq]
  have hcard : jets.card = pairs.card := Finset.card_image_of_injOn hjetinj
  obtain ⟨pair₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsep : initialJetSeparant center Qz ≠ 0 := by
    intro hz
    exact (hspec pair₀ hp₀).2.1 (by rw [hz]; simp)
  have hvz := jetDegree_pos_of_initialSeparant_ne_zero_sharp center Qz hsep
  let domainE : Fin n ↪ E := ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := fun i ↦ iota (f i) + z * iota (g i)
  have hbound := finite_regularHighCutJets_card_le_sharp center Qz K k hK hsep hvz
    domainE received hk hkL hLn jets (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨(hspec pair hp).1, (hspec pair hp).2.1,
        fun l ↦ (hspec pair hp).2.2.1 l.val l.property⟩) (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      apply (hpairs pair hp).common.trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, taylorAgreementEquation_eq_zero_iff _ _ _ _
        (hspec pair hp).2.1, (hspec pair hp).2.2.2]
      have hi' : pair.1.eval (domain i) = f i ∧ pair.2.eval (domain i) = g i := by
        simpa only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      change (correlatedPairSpecialization iota z pair).eval (iota (domain i)) =
        iota (f i) + z * iota (g i)
      simp only [correlatedPairSpecialization, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map_apply, hi'.1, hi'.2])
  rw [hcard] at hbound
  apply hbound.trans
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz K ≤ 1 + 2 * K * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply mul_le_mul
  · exact_mod_cast hvle
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left (n - k + 1) hB
  · positivity
  · positivity

/-- The explicit admissible pair family has the sharp graph-count bound. -/
theorem admissibleChartPairFamily_card_le_sharp [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ((admissibleChartPairFamily domain f g iota center Q K k L).card : ℚ) ≤ (v : ℚ) *
      ((((((n - k + 1) * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r) := by
  apply admissibleChartPairs_card_le_sharp domain f g iota center Q K k L v
    hK hkK hk hkL hLn hjet
  intro pair hp
  exact (mem_admissibleChartPairFamily_iff domain f g iota center Q K k L hkL pair).mp hp

end ReedSolomon
