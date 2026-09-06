/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVMInterpolation
import ArkLibExamples.ReedSolomon.CurveProfile
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound

/-!
# List bounds for all five LambdaVM equality-table examples

Undoing the DEEP quotient restores one degree: a table with `T` trace rows needs a list
bound for degree strictly below `T + 1`, on a domain of size `2 * T`. This module derives
that bound for each of the five table lengths in the paper, from 2048 through 32768.

The counts are consequences of actual interpolation certificates. Each row passes the
finite column-height inequality, which produces a nonzero differential equation for every
received word. The generic first-order list theorem then bounds every finite family of
polynomials satisfying the agreement predicate. The final arithmetic rounds this rational
bound upwards. The separant-stage refinement retains the first-derivative cap, yielding the
exact list bounds in the paper.

## Reading the statement

The field is arbitrary of characteristic zero or characteristic greater than the row's
block length and jet-degree cap. The domain is any embedding of that many distinct points;
no special evaluation domain is required. The received word and finite candidate family
are universally quantified. Every candidate must have degree below `T + 1` and agree on
at least the recorded number of positions. The conclusion bounds the cardinality of that
family, with no list-size hypothesis.

These scalar bounds are uniform over extension fields. The separate interleaving transfer
uses that uniformity to bound tuples without multiplying the list size by their width.
Powers exceptional counts and the local error composition are separate results.
-/

open PolynomialDifferential Polynomial
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.LambdaVMLists

open CurveProfile LambdaVMInterpolation

/-- Original-tuple profiles, ordered by increasing table size. -/
def profiles : Fin 5 → LineProfile := ![
  { n := 4096, k := 2049, agreement := 2843, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 67038568, localRank := 16336,
    columnY₀Weight := 1407095340, height := 11139, heightSlots := 745402552180 },
  { n := 8192, k := 4097, agreement := 5697, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 71052995, localRank := 8645,
    columnY₀Weight := 1197631071, height := 5136, heightSlots := 363801604244 },
  { n := 16384, k := 8193, agreement := 11415, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 67822380, localRank := 4125,
    columnY₀Weight := 893143920, height := 3746, heightSlots := 253237313940 },
  { n := 32768, k := 16385, agreement := 22878, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 79261668, localRank := 2408,
    columnY₀Weight := 885489362, height := 2485, heightSlots := 196159017286 },
  { n := 65536, k := 32769, agreement := 45910, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 92451520, localRank := 1400,
    columnY₀Weight := 835596090, height := 1191, heightSlots := 109366615750 }
]

/-- Integer ceilings of the five derived geometric list expressions. -/
def listBounds : Fin 5 → ℕ := ![1242977545, 1263690225, 1174501452, 1303321936, 1434752117]

/-- Every original-tuple row satisfies the actual finite support and height tests. -/
theorem profiles_verified (i : Fin 5) : (profiles i).Verification := by
  fin_cases i <;> constructor <;> decide +kernel

/-- The geometric side conditions hold on each of the five original-tuple domains. -/
theorem profiles_admissible (i : Fin 5) :
    1 < (profiles i).k ∧ (profiles i).k ≤ (profiles i).n ∧
      (profiles i).k ≤ (profiles i).agreement ∧ (profiles i).agreement ≤ (profiles i).n := by
  fin_cases i <;> decide

/-- The rational geometric expression lies below the recorded integer list bound. -/
theorem list_envelope_le (i : Fin 5) :
    (((profiles i).n * firstOrderListWeight (profiles i).k (profiles i).totalJetCap
      (profiles i).firstDerivativeCap : ℕ) : ℚ) /
        (((profiles i).agreement - (profiles i).k + 1 : ℕ) : ℚ) ≤ listBounds i := by
  fin_cases i <;> norm_num [profiles, listBounds, firstOrderListWeight]


/-- Each row bounds every finite scalar list of original tuples after restoring the DEEP degree.
The result is uniform over all fields satisfying the characteristic condition. -/
theorem finite_list_bound {F : Type*} [Field F] (i : Fin 5)
    (domain : Fin (profiles i).n ↪ F) (received : Fin (profiles i).n → F)
    (hchar : ringChar F = 0 ∨ max (profiles i).n (profiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (profiles i).k
      (profiles i).agreement P) :
    (S.card : ℚ) ≤ listBounds i := by
  have hp := profiles_verified i
  obtain ⟨hk, hkn, hka, han⟩ := profiles_admissible i
  have hb := finite_firstOrder_list_bound_of_heightSlotCount_sharp
    hp.D_gt_one hp.budget_pos hp.degree_le domain received hp.heightSurplus
    hk le_rfl hkn (by omega) hka han hchar S hS
  apply hb.trans
  exact list_envelope_le i

end ArkLibExamples.ReedSolomon.LambdaVMLists
