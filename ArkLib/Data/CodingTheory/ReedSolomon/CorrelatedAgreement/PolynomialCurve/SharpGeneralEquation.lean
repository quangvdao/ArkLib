/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.SharpRegularEquation

/-!
# Sharp regular polynomial-curve bounds at arbitrary derivative order

For a source differential equation of order `r`, put

```text
a = ell + 2*K*h,
b = 1 + 2*K*(v-1),
J = h*b^(r+1) + (r+1)*v*a*b^r.
```

This file proves the regular-curve exceptional-set bound

```text
J * ((n-L+1)/(A-L+1))^(r+1)
  + ell*(n-L)*v * (((n-k+1)*b)/(L-k+1))^r.
```

The first term is the sharp mixed degree of the source hypersurface times the sharp
high-agreement incidence ratio. The second term is the exact `ell*(n-L)` accidental-root
count for each admissible tuple, combined with sharp tuple counting.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Mixed affine degree of the pulled-back order-`r` initial hypersurface. -/
def sourceCurveInitialMixedDegree (r ℓ K v h : ℕ) : ℕ :=
  h * sourceCurveCutJetDegree K v ^ (r + 1) +
    (r + 1) * v * sourceCurveCutChallengeDegree ℓ K h *
      sourceCurveCutJetDegree K v ^ r

/-- Sharp regular order-`r` MCA budget: mixed source incidence plus exact tuple roots. -/
def regularSymbolicCurveMCASharpBound
    (r n ℓ K k L A v h : ℕ) : ℚ :=
  (sourceCurveInitialMixedDegree r ℓ K v h : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) +
    ((ℓ * (n - L) : ℕ) : ℚ) * (v : ℚ) *
      (((((n - k + 1) * sourceCurveCutJetDegree K v : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ))) ^ r

private theorem span_singleton_ne_top_of_aeval_eq_zero_general {S : Type*}
    (g : MvPolynomial S E) (x : S → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial S E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

private theorem source_initial_ne_zero_of_regular_general {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_separant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquationOver (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- The generic bidegree presentation specialized to an order-`r` source hypersurface. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_sharp_general
    {r a b h v n A L : ℕ} (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin (r + 1))) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin (r + 1))) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) a b)
    (highCuts : List (MvPolynomial (Option (Fin (r + 1))) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) a b)
    (cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) a b)
    (excluded : Set (Option (Fin (r + 1)) → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin (r + 1))) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option (Fin (r + 1)) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (h * b ^ (r + 1) + (r + 1) * v * a * b ^ r : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  have hc := bidegreeHypersurface_source_incidence_off_excluded_sharp ha hb hLA hAn
    g s hg0 hproper hgAB hs highCuts hhigh cuts hcuts excluded hterminal S hS hA
  have hd := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
  have hd' : (hilbertPolynomial (Ideal.span {g})).natDegree = r + 1 := by omega
  rw [hd'] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (bidegreeHypersurface_affineDegree_le ha hb hg0 hproper hg) (by positivity))

/-- Sharp off-tuple incidence for an order-`r` source equation. -/
theorem finite_sourceCurve_points_off_tuples_card_le_sharp
    {r : ℕ} [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h) (hv : 0 < v)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceCurveTupleLocus domain w iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement center Q K (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ sourceCurveInitialMixedDegree r ℓ K v h *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := symbolicSourceInitialEquation center Q
  let s := symbolicSourceSeparant center Q
  let high := sourceCurveHighCuts center Q K k
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    symbolicSourceCurveAgreement center Q K (iota (domain i)) (fun t ↦ iota (w t i))
  have hKpos : 0 < K := by omega
  have ha : 0 < sourceCurveCutChallengeDegree ℓ K h := by
    unfold sourceCurveCutChallengeDegree
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      have : 0 < 2 * K * h := Nat.mul_pos (Nat.mul_pos (by omega) hKpos) hh
      omega
  have hb : 0 < sourceCurveCutJetDegree K v := by
    unfold sourceCurveCutJetDegree
    omega
  have hproper :
      Ideal.span ({g} : Set (MvPolynomial (Option (Fin (r + 1))) E)) ≠ ⊤ :=
    span_singleton_ne_top_of_aeval_eq_zero_general g x₀ (hS x₀ hx₀).1
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_general
    ha hb hLA hAn g s hinit hproper
      (symbolicSourceInitialEquation_mem_restrictBidegree center Q h v hheight hjet)
      (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree
        center Q ℓ K h v hKpos hv hheight hjet)
      (symbolicSourceSeparant_mem_sourceCurveCutBidegree
        center Q ℓ K h v hKpos hheight hjet)
      high ?_ cuts ?_ (sourceCurveTupleLocus domain w iota center Q K k L) ?_ S ?_ ?_
  · intro f hf
    simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    exact symbolicSourceNumerator_mem_sourceCurveCutBidegree
      center Q ℓ K h v hv hheight hjet l.val
  · intro i
    exact symbolicSourceCurveAgreement_mem_sourceCurveCutBidegree center
      (iota (domain i)) (fun t ↦ iota (w t i)) Q K h v hv hheight hjet
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_sourceCurveTupleLocus domain w iota center Q hK hkL J hJ
    · simpa only [s] using hsJ
    · simpa only [g] using hgJ
    · intro q hq
      exact hhighJ q (by simpa only [high] using hq)
    · exact hdJ
    · simpa only [cuts] using hcutsJ
  · intro x hx
    exact ⟨(hS x hx).1, (hS x hx).2.1, (by
      intro f hf
      simp only [high, sourceCurveHighCuts, List.mem_map, Finset.mem_toList] at hf
      obtain ⟨l, _, rfl⟩ := hf
      exact (hS x hx).2.2.1 l.val l.property), (hS x hx).2.2.2⟩
  · simpa only [cuts] using hA

/-- Exact fixed-center bad-challenge bound for an order-`r` source equation. -/
theorem finite_sourceCurve_bad_challenges_card_le_sharp
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ regularSymbolicCurveMCASharpBound r n ℓ K k L A v h := by
  classical
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularSymbolicCurveMCASharpBound
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := source_initial_ne_zero_of_regular_general center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  simpa only [regularSymbolicCurveMCASharpBound] using
    (finite_sourceCurve_bad_challenges_card_le_of_source_bound
      domain w iota center Q K k L A v hK hkK hk hkL hLA hAn hjet
      ((sourceCurveInitialMixedDegree r ℓ K v h : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1))
      (fun S hS hA ↦ finite_sourceCurve_points_off_tuples_card_le_sharp
        domain w iota center Q K k L A v h hK hkL hLA hAn hD hv hinit
          hjet hheight S hS hA)
      challenges witness jet hchart hagree hbad)

/-- Every finite set of regular bad challenges at order `r` satisfies the sharp budget. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le_sharp
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicCurveMCASharpBound r n ℓ K k L A v h := by
  classical
  apply finite_regularSymbolicCurveBadChallenges_card_le_of_fixedCenter
    domain w iota Q K k A hkK hbin
      (regularSymbolicCurveMCASharpBound r n ℓ K k L A v h) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_sourceCurve_bad_challenges_card_le_sharp
    domain w iota center Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight
      challenges witness jet hchart hagree hbad

private theorem set_finite_of_finset_card_le_rational_general {X : Type*} (T : Set X) (B : ℚ)
    (hbound : ∀ S : Finset X, ↑S ⊆ T → (S.card : ℚ) ≤ B) : T.Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := hbound S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- The full regular bad-challenge set at order `r` is finite. -/
theorem regularSymbolicCurveBadChallenges_finite_sharp
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
  classical
  apply set_finite_of_finset_card_le_rational_general _
    (regularSymbolicCurveMCASharpBound r n ℓ K k L A v h)
  exact finite_regularSymbolicCurveBadChallenges_card_le_sharp
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin

/-- A single sharply bounded exceptional set works for every regular order-`r` solution. -/
theorem exists_exceptional_regularSymbolicCurveMCA_sharp
    {r : ℕ} [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicCurveMCASharpBound r n ℓ K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite := regularSymbolicCurveBadChallenges_finite_sharp
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le_sharp
      domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
