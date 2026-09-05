/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBand
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.ScaledLattice
import ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Variance


/-!
# Finite simplex counting for asymmetric bands

Coordinatewise division by the higher-jet costs transports ordinary-simplex events into
asymmetric bands. Remainders bound every fiber by `(d - 1)!`; no uniformity of the quotient
is assumed. The final two-sided Chebyshev estimate retains the exact finite variance.
It is an intermediate counting estimate, not a proof of optimized manuscript constants.
-/

open PolynomialDifferential


open DiscreteSimplex

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- Weights for the real statistic before coordinatewise integer division. -/
def simplexReciprocalWeights (d : ℕ) (i : Fin (d - 1)) : ℝ := 1 / (i.val + 1 : ℕ)

/-- Integer division loses at most one per coordinate in the ordinary degree. -/
theorem simplex_quotient_degree_bounds {d W : ℕ} (u : OrdinarySimplex (d - 1) W) :
    (higherJetTupleDegree (ordinaryToScaledWithResidue d W u).1.1 : ℝ) ≤
        simplexWeightedStatistic (simplexReciprocalWeights d) u ∧
      simplexWeightedStatistic (simplexReciprocalWeights d) u ≤
        higherJetTupleDegree (ordinaryToScaledWithResidue d W u).1.1 + (d - 1 : ℕ) := by
  have hcoord (i : Fin (d - 1)) :
      (u.1 i / (i.val + 1) : ℕ) ≤ (1 / (i.val + 1 : ℕ) : ℝ) * u.1 i ∧
      (1 / (i.val + 1 : ℕ) : ℝ) * u.1 i ≤ (u.1 i / (i.val + 1) : ℕ) + 1 := by
    have hp : (0 : ℝ) < (i.val + 1 : ℕ) := by positivity
    have hle := Nat.mul_div_le (u.1 i) (i.val + 1)
    have hlt := Nat.mod_lt (u.1 i) (Nat.succ_pos i.val)
    change u.1 i % (i.val + 1) < i.val + 1 at hlt
    have heq := Nat.mod_add_div (u.1 i) (i.val + 1)
    have hle' : (i.val + 1 : ℕ) * (u.1 i / (i.val + 1) : ℕ) ≤ (u.1 i : ℝ) := by
      exact_mod_cast hle
    have hlt' : (u.1 i : ℝ) ≤ (i.val + 1 : ℕ) * ((u.1 i / (i.val + 1) : ℕ) + 1 : ℝ) := by
      have : u.1 i ≤ (i.val + 1) * (u.1 i / (i.val + 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact_mod_cast this
    constructor
    · rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hp).mpr
      simpa [mul_comm] using hle'
    · rw [one_div_mul_eq_div]
      exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hlt')
  constructor
  · simpa [higherJetTupleDegree, ordinaryToScaledWithResidue, simplexWeightedStatistic,
      simplexReciprocalWeights] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ (hcoord i).1)
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ (hcoord i).2)
    simpa [higherJetTupleDegree, ordinaryToScaledWithResidue, simplexWeightedStatistic,
      simplexReciprocalWeights, Finset.sum_add_distrib] using h

/-- Fixing a quotient leaves at most the number of possible remainder vectors. -/
theorem simplex_quotient_fiber_card_le {d W : ℕ} (c : HigherJetTuple d) :
    (Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
      (ordinaryToScaledWithResidue d W u).1.1 = c).card ≤ (d - 1).factorial := by
  let fiber := Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
    (ordinaryToScaledWithResidue d W u).1.1 = c
  let f : ↥fiber → ScaledResidue d := fun u ↦ (ordinaryToScaledWithResidue d W u.1).2
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply ordinaryToScaledWithResidue_injective d W
    apply Prod.ext
    · apply Subtype.ext
      exact (Finset.mem_filter.mp u.2).2.trans (Finset.mem_filter.mp v.2).2.symm
    · exact huv
  simpa only [Fintype.card_coe, card_scaledResidue] using Fintype.card_le_of_injective f hf

/-- Two statistic cutoffs place the actual integer quotient in the asymmetric band. -/
theorem simplex_quotient_mem_band {d W Cmin Cmax : ℕ}
    (u : OrdinarySimplex (d - 1) W)
    (hlo : (Cmin : ℝ) + (d - 1 : ℕ) ≤
      simplexWeightedStatistic (simplexReciprocalWeights d) u)
    (hhi : simplexWeightedStatistic (simplexReciprocalWeights d) u ≤ Cmax) :
    (ordinaryToScaledWithResidue d W u).1.1 ∈ asymmetricBandTuples d W Cmin Cmax := by
  have hb := simplex_quotient_degree_bounds u
  rw [mem_asymmetricBandTuples]
  refine ⟨mem_scaledExponentFinset.mp (ordinaryToScaledWithResidue d W u).1.2, ?_, ?_⟩
  · exact_mod_cast (show (Cmin : ℝ) ≤
      higherJetTupleDegree (ordinaryToScaledWithResidue d W u).1.1 by linarith)
  · exact_mod_cast hb.1.trans hhi

/-- Remainders give an explicit factorial fiber bound for any two-sided good event. -/
theorem simplex_event_card_le_band_mul_factorial {d W Cmin Cmax : ℕ}
    (event : Finset (OrdinarySimplex (d - 1) W))
    (hlo : ∀ u ∈ event, (Cmin : ℝ) + (d - 1 : ℕ) ≤
      simplexWeightedStatistic (simplexReciprocalWeights d) u)
    (hhi : ∀ u ∈ event, simplexWeightedStatistic (simplexReciprocalWeights d) u ≤ Cmax) :
    event.card ≤ (asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial := by
  let f : ↥event → ↥(asymmetricBandTuples d W Cmin Cmax) × ScaledResidue d := fun u ↦
    (⟨(ordinaryToScaledWithResidue d W u.1).1.1,
      simplex_quotient_mem_band u.1 (hlo u.1 u.2) (hhi u.1 u.2)⟩,
      (ordinaryToScaledWithResidue d W u.1).2)
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply ordinaryToScaledWithResidue_injective d W
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p ↦ p.1.1) huv
    · exact congrArg (fun p : ↥(asymmetricBandTuples d W Cmin Cmax) × ScaledResidue d ↦ p.2) huv
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, card_scaledResidue] using h

/-- The strict central event loses at most `C * V / t²` points, with the exact discrete
variance. The division-free statement also makes sense when `t = 0`. -/
theorem simplex_central_event_count {r S : ℕ} (w : Fin r → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (Fintype.card (OrdinarySimplex r S) : ℝ) * (t ^ 2 - simplexWeightedVariance S w) ≤
      t ^ 2 * ((Finset.univ.filter fun u : OrdinarySimplex r S ↦
        |simplexWeightedStatistic w u - simplexWeightedMean S w| < t).card : ℝ) := by
  classical
  let good := Finset.univ.filter fun u : OrdinarySimplex r S ↦
    |simplexWeightedStatistic w u - simplexWeightedMean S w| < t
  let bad := Finset.univ \ good
  have hC : (Fintype.card (OrdinarySimplex r S) : ℝ) ≠ 0 := by
    exact_mod_cast (card_ordinarySimplex_pos r S).ne'
  have hTotal := simplex_average_centered_square (S := S) w
  unfold simplexAverage at hTotal
  have hSum := (div_eq_iff hC).mp hTotal
  have hbad : t ^ 2 * (bad.card : ℝ) ≤
      Fintype.card (OrdinarySimplex r S) * simplexWeightedVariance S w := by
    calc
      _ = ∑ _u ∈ bad, t ^ 2 := by simp [mul_comm]
      _ ≤ ∑ u ∈ bad, (simplexWeightedStatistic w u - simplexWeightedMean S w) ^ 2 := by
        apply Finset.sum_le_sum
        intro u hu
        have hnot : ¬ |simplexWeightedStatistic w u - simplexWeightedMean S w| < t := by
          simpa [bad, good] using hu
        have h := le_of_not_gt hnot
        nlinarith [sq_abs (simplexWeightedStatistic w u - simplexWeightedMean S w)]
      _ ≤ ∑ u : OrdinarySimplex r S,
          (simplexWeightedStatistic w u - simplexWeightedMean S w) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
      _ = _ := by simpa [mul_comm] using hSum
  have hcard : bad.card + good.card = Fintype.card (OrdinarySimplex r S) := by
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
  have hcard' : (bad.card : ℝ) + good.card = Fintype.card (OrdinarySimplex r S) := by
    exact_mod_cast hcard
  change _ ≤ t ^ 2 * (good.card : ℝ)
  nlinarith

/-- A two-sided central event gives an explicit lower bound for the asymmetric band.
The lower-edge hypothesis pays the full coordinatewise rounding loss. All variance terms
retain the finite-simplex correction, and the factorial accounts for quotient fibers. -/
theorem asymmetricBand_card_lower_of_simplex_variance {d W Cmin Cmax : ℕ}
    (t : ℝ) (ht : 0 ≤ t)
    (hlo : (Cmin : ℝ) + (d - 1 : ℕ) ≤
      simplexWeightedMean W (simplexReciprocalWeights d) - t)
    (hhi : simplexWeightedMean W (simplexReciprocalWeights d) + t ≤ Cmax) :
    (Fintype.card (OrdinarySimplex (d - 1) W) : ℝ) *
        (t ^ 2 - simplexWeightedVariance W (simplexReciprocalWeights d)) ≤
      t ^ 2 * ((asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial : ℕ) := by
  let event := Finset.univ.filter fun u : OrdinarySimplex (d - 1) W ↦
    |simplexWeightedStatistic (simplexReciprocalWeights d) u -
      simplexWeightedMean W (simplexReciprocalWeights d)| < t
  have hcard := simplex_event_card_le_band_mul_factorial (Cmin := Cmin) (Cmax := Cmax)
    event (fun u hu ↦ by
      have h := abs_lt.mp (Finset.mem_filter.mp hu).2
      linarith) (fun u hu ↦ by
      have h := abs_lt.mp (Finset.mem_filter.mp hu).2
      linarith)
  have hcard' : (event.card : ℝ) ≤
      ((asymmetricBandTuples d W Cmin Cmax).card * (d - 1).factorial : ℕ) := by
    exact_mod_cast hcard
  exact (simplex_central_event_count (S := W) (simplexReciprocalWeights d) t ht).trans
    (mul_le_mul_of_nonneg_left hcard' (sq_nonneg t))

/-- A nonvacuous finite-budget example: the variance is `10` and the radius is `4`. -/
example : (66 : ℝ) ≤ 16 * (asymmetricBandTuples 2 10 0 9).card := by
  have h := asymmetricBand_card_lower_of_simplex_variance
    (d := 2) (W := 10) (Cmin := 0) (Cmax := 9) 4 (by norm_num)
  simp only [show 2 - 1 = 1 from rfl, card_ordinarySimplex, Nat.choose_one_right] at h
  norm_num [simplexWeightedMean, simplexWeightedVariance, simplexReciprocalWeights,
    Fin.sum_univ_succ] at h
  exact h

end
end ReedSolomon.HiddenDerivative
