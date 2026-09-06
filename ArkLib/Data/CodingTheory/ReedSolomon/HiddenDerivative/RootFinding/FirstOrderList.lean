/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.TaylorCharZeroSolutions
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting

/-!
# Cap-sensitive first-order differential list counting

For a first-order differential equation of total jet degree at most `μ`, whose degree in `Y₁`
is at most `M`, a separant chain can select the top jet at most `M` times. Charging those stages
the order-one Taylor cost and every later stage the order-zero cost gives

```text
B₀ = ∑_{j=1}^{μ-c} j,
B₁ = ∑_{j=μ-c+1}^{μ} j (1 + 2 K (j - 1)),
c  = min(M, μ),
|S| ≤ n (B₀ + B₁) / (A - k + 1).
```

`firstOrderListWeight K μ M` is the executable recursive form of `B₀ + B₁`.

## Reading the main theorem

* `Q` is any nonzero differential equation in `X,Y₀,Y₁` with the two displayed degree
  caps. `S` is any finite set of degree-`< k` polynomial solutions of `Q`, each agreeing with
  `received` at `A` or more of the distinct centers supplied by `domain`.
* `K` is the Taylor cutoff. The hypotheses `1 < K`, `k ≤ K`, and `K ≤ n` discharge the
  Taylor and binomial-pivot conditions.
* The field may have characteristic zero. In positive characteristic, the sufficient condition
  is `max n μ < ringChar F`.

## Proof route and scope

The proof follows the actual singular separant recursion. At a regular stage it restricts the
equation to its highest active jet and invokes the field-independent Taylor count. A `Y₁`
separant decreases the first-jet cap, while a stage headed by `Y₀` has no active `Y₁`.
Total jet degree drops at every singular step, so the recursive charge is precisely
`firstOrderListWeight` even when degrees are skipped or the active order drops early.

The theorem bounds a supplied finite set. It does not assert that the complete set of close
polynomials is finite, and it does not perform an interleaving or polynomial-curve transfer.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], cap-sensitive first-order list bound.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F]

/-- The cap-sensitive sum of regular-branch fiber degrees.  The `M` highest total-jet-degree
stages receive the order-one Taylor factor; the remaining stages receive factor one. -/
def firstOrderListWeight (K : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1) + firstOrderListWeight K μ 0
  | μ + 1, M + 1 =>
      (μ + 1) * (1 + 2 * K * μ) + firstOrderListWeight K μ M

/-- A regular branch whose highest active jet is `Y₀` costs only its total jet degree. -/
private theorem regularSolutions_card_le_of_agreement_orderZero
    (current : DifferentialPolynomial F 1) (s : Fin 2) (hsval : s.val = 0)
    (hhighest : highestActiveJet current = some s)
    (K k ν : ℕ) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree current ≤ ν)
    (regular : Finset (BoundedSolution current (k - 1)))
    (haccepts : ∀ solution ∈ regular,
      IsAgreementSolution domain received k A solution.polynomial)
    (hseparant : ∀ solution ∈ regular,
      differentialSpecialization (separant current s) solution.polynomial ≠ 0) :
    (regular.card : ℚ) ≤ ν := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective (fun solution : BoundedSolution current (k - 1) ↦
      solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card :=
    Finset.card_image_of_injective regular hinjective
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding s Q', hQ']
    exact hdegree
  have hv : 0 < jetTotalDegree Q' := by
    have hactive : 0 < jetDegree current s :=
      (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
    have hactive' : 0 < jetDegree Q' (Fin.last s.val) := by
      unfold jetDegree
      rw [← MvPolynomial.degreeOf_rename_of_injective
        (jetPrefixEmbedding s).injective (some (Fin.last s.val)),
        jetPrefixEmbedding_top, hQ']
      exact hactive
    exact hactive'.trans_le (jetDegree_le_total Q' (Fin.last s.val))
  have hstage := finite_regular_solutions_card_le Q' K k (by omega) hkK
    (by rw [← jetTotalDegree_eq_weightedTotalDegree_elim]; exact hv)
    domain received hk hkA hAn polys
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      have heqsep :
          differentialSpecialization (separant current s) solution.polynomial =
            differentialSpecialization (separant Q' (Fin.last s.val)) solution.polynomial := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding s)
                (separant Q' (Fin.last s.val))) solution.polynomial := by
              rw [← separant_rename_jetPrefixEmbedding, hQ']
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hs (heqsep.trans hz))
    (fun i _hi _hiK ↦ by simp [hsval])
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).2)
  rw [hcard, ← jetTotalDegree_eq_weightedTotalDegree_elim] at hstage
  have hstage' : (regular.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) := by
    simpa [hsval] using hstage
  exact hstage'.trans (by exact_mod_cast hQ'Degree)

/-- Every finite family of accepted solutions of a first-order equation is bounded by the
cap-sensitive sum.  `μ` bounds total jet degree and `M` bounds the degree in `Y₁`. -/
theorem finite_firstOrder_agreement_solutions_card_le_sharp
    (Q : DifferentialPolynomial F 1) (K k μ M : ℕ)
    (hQ : Q ≠ 0) (hdegree : jetTotalDegree Q ≤ μ)
    (hfirst : jetDegree Q (1 : Fin 2) ≤ M)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max n μ < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  classical
  let toRoot : {P // P ∈ S} → BoundedSolution Q (k - 1) := fun P ↦
    ⟨⟨P.1, by
      rw [Polynomial.mem_degreeLT]
      simpa [Nat.sub_add_cancel hk] using (haccept P.1 P.2).1⟩, hsol P.1 P.2⟩
  let roots : Finset (BoundedSolution Q (k - 1)) := S.attach.image toRoot
  have htoRoot : Function.Injective toRoot := by
    intro left right heq
    apply Subtype.ext
    exact congrArg BoundedSolution.polynomial heq
  have hcard : roots.card = S.card := by
    change (S.attach.image toRoot).card = S.card
    rw [Finset.card_image_of_injective _ htoRoot, Finset.card_attach]
  have hroots : ∀ solution ∈ roots,
      IsAgreementSolution domain received k A solution.polynomial := by
    intro solution hsolution
    change solution ∈ S.attach.image toRoot at hsolution
    rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, rfl⟩
    exact haccept source.1 source.2
  have hdenPos : 0 < A - k + 1 := by omega
  have hdenLe : A - k + 1 ≤ n := by omega
  have recurse : ∀ (μ M : ℕ) (Q : DifferentialPolynomial F 1), Q ≠ 0 →
      jetTotalDegree Q ≤ μ → jetDegree Q (1 : Fin 2) ≤ M →
      (ringChar F = 0 ∨ max n μ < ringChar F) →
      ∀ roots : Finset (BoundedSolution Q (k - 1)),
        (∀ solution ∈ roots,
          IsAgreementSolution domain received k A solution.polynomial) →
        (roots.card : ℚ) ≤
          ((n * firstOrderListWeight K μ M : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ) := by
    intro bound
    induction bound with
    | zero =>
        intro M current hcurrent hcurrentDegree _hcurrentFirst _hcurrentChar currentRoots _
        have hterminal : highestActiveJet current = none := by
          apply (highestActiveJet_eq_none_iff current).mpr
          intro j hj
          have := hj.trans_le ((jetDegree_le_total current j).trans hcurrentDegree)
          omega
        let _ : IsEmpty (BoundedSolution current (k - 1)) :=
          isEmpty_boundedSolution_of_highestActiveJet_eq_none current hcurrent hterminal
        have hempty : currentRoots = ∅ := by
          ext solution
          exact isEmptyElim solution
        simp [hempty, firstOrderListWeight]
    | succ bound ih =>
        intro M current hcurrent hcurrentDegree hcurrentFirst hcurrentChar currentRoots
          hcurrentRoots
        cases hactive : highestActiveJet current with
        | none =>
            let _ : IsEmpty (BoundedSolution current (k - 1)) :=
              isEmpty_boundedSolution_of_highestActiveJet_eq_none current hcurrent hactive
            have hempty : currentRoots = ∅ := by
              ext solution
              exact isEmptyElim solution
            rw [hempty]
            positivity
        | some s =>
            let regularRoots := regularSolutions current s (k - 1) currentRoots
            let singularRoots := singularSolutions current s (k - 1) currentRoots
            let nextRoots := singularDescendants current s (k - 1) currentRoots
            have hactiveJet : DependsOnJet current s :=
              (isHighestActiveJet_of_highestActiveJet_eq_some hactive).1
            have hnextNe : separant current s ≠ 0 := by
              rcases hcurrentChar with hzero | hpos
              · let _ : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
                let _ : CharZero F := CharP.charP_to_charZero F
                exact separant_ne_zero_of_dependsOnJet_charZero current s hactiveJet
              · exact separant_ne_zero_of_dependsOnJet_of_lt_ringChar current s hactiveJet
                  ((jetDegree_le_total current s).trans hcurrentDegree |>.trans_lt
                    ((Nat.le_max_right n (bound + 1)).trans_lt hpos))
            have hregularAccepts : ∀ solution ∈ regularRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              apply hcurrentRoots solution
              exact (Finset.mem_filter.mp (show
                solution ∈ currentRoots.filter fun candidate ↦
                  differentialSpecialization (separant current s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).1
            have hregularSep : ∀ solution ∈ regularRoots,
                differentialSpecialization (separant current s) solution.polynomial ≠ 0 := by
              intro solution hsolution
              exact (Finset.mem_filter.mp (show
                solution ∈ currentRoots.filter fun candidate ↦
                  differentialSpecialization (separant current s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).2
            have hnextAccepts : ∀ solution ∈ nextRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              change solution ∈ singularDescendants current s (k - 1) currentRoots at hsolution
              unfold singularDescendants at hsolution
              rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, heq⟩
              rw [← heq]
              apply hcurrentRoots source.1
              exact (Finset.mem_filter.mp source.2).1
            have hnextDegree : jetTotalDegree (separant current s) ≤ bound := by
              have hsep := separant_total_le current s
              omega
            have hnextChar : ringChar F = 0 ∨ max n bound < ringChar F :=
              hcurrentChar.imp_right fun hpos ↦
                (max_le_max_left n (Nat.le_succ bound)).trans_lt hpos
            cases M with
            | zero =>
                have hs : s = (0 : Fin 2) := by
                  fin_cases s
                  · rfl
                  · have := hactiveJet.trans_le hcurrentFirst
                    omega
                subst s
                have hnextFirst : jetDegree (separant current (0 : Fin 2)) (1 : Fin 2) ≤ 0 :=
                  (jetDegree_separant_le current (0 : Fin 2) (1 : Fin 2)).trans
                    hcurrentFirst
                have hnext := ih 0 (separant current (0 : Fin 2)) hnextNe hnextDegree
                  hnextFirst hnextChar nextRoots hnextAccepts
                have hregularBase : (regularRoots.card : ℚ) ≤ ((bound + 1 : ℕ) : ℚ) :=
                  regularSolutions_card_le_of_agreement_orderZero current (0 : Fin 2) rfl hactive
                    K k (bound + 1)
                    hkK domain received hk hkA hAn hcurrentDegree regularRoots
                      hregularAccepts hregularSep
                have hregular : (regularRoots.card : ℚ) ≤
                    ((n * (bound + 1) : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
                  apply hregularBase.trans
                  rw [le_div_iff₀ (by exact_mod_cast hdenPos)]
                  norm_cast
                  simpa [Nat.mul_comm] using Nat.mul_le_mul_right (bound + 1) hdenLe
                have hsingular : (singularRoots.card : ℚ) ≤
                    ((n * firstOrderListWeight K bound 0 : ℕ) : ℚ) /
                      ((A - k + 1 : ℕ) : ℚ) := by
                  rw [← card_singularDescendants current (0 : Fin 2) (k - 1) currentRoots]
                  exact hnext
                have hpartition : regularRoots.card + singularRoots.card = currentRoots.card :=
                  card_regular_add_card_singular current (0 : Fin 2) (k - 1) currentRoots
                calc
                  (currentRoots.card : ℚ) =
                      (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
                    exact_mod_cast hpartition.symm
                  _ ≤ _ := add_le_add hregular hsingular
                  _ = ((n * firstOrderListWeight K (bound + 1) 0 : ℕ) : ℚ) /
                        ((A - k + 1 : ℕ) : ℚ) := by
                    simp only [firstOrderListWeight]
                    push_cast
                    ring
            | succ cap =>
                have hnextFirst : jetDegree (separant current s) (1 : Fin 2) ≤ cap := by
                  fin_cases s
                  · have hzero : jetDegree current (1 : Fin 2) = 0 := by
                      apply Nat.eq_zero_of_not_pos
                      exact (isHighestActiveJet_of_highestActiveJet_eq_some hactive).2
                        (1 : Fin 2) (by decide)
                    exact (jetDegree_separant_le current (0 : Fin 2) (1 : Fin 2)).trans
                      (by omega)
                  · have hd := MvPolynomial.degreeOf_pderiv_le_sub_one
                        (some (1 : Fin 2)) current
                    change jetDegree (separant current (1 : Fin 2)) (1 : Fin 2) ≤
                      jetDegree current (1 : Fin 2) - 1 at hd
                    exact hd.trans (by omega)
                have hnext := ih cap (separant current s) hnextNe hnextDegree hnextFirst
                  hnextChar nextRoots hnextAccepts
                have hregularBase := regularSolutions_card_le_of_agreement_charZero
                  current s hactive K k (bound + 1) hK hkK domain received hk hkA hAn
                    hcurrentDegree
                    (fun r _hr i hri hiK ↦
                      binomial_pivots_of_characteristic
                        (hcurrentChar.imp_right fun hpos ↦
                          (hKn.trans (Nat.le_max_left n (bound + 1))).trans
                            (Nat.le_of_lt hpos)) r i hri hiK)
                    regularRoots hregularAccepts hregularSep
                have hregular : (regularRoots.card : ℚ) ≤
                    ((n * ((bound + 1) * (1 + 2 * K * bound)) : ℕ) : ℚ) /
                      ((A - k + 1 : ℕ) : ℚ) := by
                  calc
                    (regularRoots.card : ℚ) ≤ ((bound + 1 : ℕ) : ℚ) *
                        ((((n * (1 + 2 * K * ((bound + 1) - 1)) : ℕ) : ℚ) /
                          ((A - k + 1 : ℕ) : ℚ)) ^ 1) := hregularBase
                    _ = _ := by
                      simp only [Nat.add_sub_cancel, pow_one, Nat.cast_add, Nat.cast_one]
                      push_cast
                      ring
                have hsingular : (singularRoots.card : ℚ) ≤
                    ((n * firstOrderListWeight K bound cap : ℕ) : ℚ) /
                      ((A - k + 1 : ℕ) : ℚ) := by
                  rw [← card_singularDescendants current s (k - 1) currentRoots]
                  exact hnext
                have hpartition : regularRoots.card + singularRoots.card = currentRoots.card :=
                  card_regular_add_card_singular current s (k - 1) currentRoots
                calc
                  (currentRoots.card : ℚ) =
                      (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
                    exact_mod_cast hpartition.symm
                  _ ≤ _ := add_le_add hregular hsingular
                  _ = ((n * firstOrderListWeight K (bound + 1) (cap + 1) : ℕ) : ℚ) /
                        ((A - k + 1 : ℕ) : ℚ) := by
                    simp only [firstOrderListWeight]
                    push_cast
                    ring
  have hbound := recurse μ M Q hQ hdegree hfirst hchar roots hroots
  rwa [hcard] at hbound

end

end ReedSolomon.HiddenDerivative
