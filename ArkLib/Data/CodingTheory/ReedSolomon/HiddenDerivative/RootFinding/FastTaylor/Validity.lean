/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ChartData
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting

/-!
# Proof predicates for one computed Taylor chart

Runtime chart data remains unchanged. These predicates separate the supported characteristic,
normal-form degree bounds, and exact cleared coefficient identity. Solution precision is `k`;
for order `r` the supported differential residual precision is only `k-r`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CPoly CompPoly CPoly.TaylorReconstruction

/-- The paper regime supplies every integration and Hasse pivot below the requested cap. -/
structure Supported (p r k Bjet : ℕ) : Prop where
  order_lt : r < k
  precision_le : k ≤ p
  jetDegree_lt : Bjet < p

/-- The supported differential order is strictly below the characteristic. -/
theorem Supported.order_lt_characteristic {p r k Bjet : ℕ} (hs : Supported p r k Bjet) :
    r < p := hs.order_lt.trans_le hs.precision_le

/-- Differentiation leaves a positive, explicitly smaller residual cap. -/
theorem Supported.residual_pos {p r k Bjet : ℕ} (hs : Supported p r k Bjet) :
    0 < k - r := Nat.sub_pos_of_lt hs.order_lt

/-- The global normal-form degree budget used by the chart constructor. -/
def globalDegreeBudget (k Bjet : ℕ) : ℕ := 1 + 2 * k * (Bjet - 1)

/-- The parameter precision strictly exceeds the global degree budget. -/
def parameterPrecision (k Bjet : ℕ) : ℕ := globalDegreeBudget k Bjet + 1

/-- No bounded global coefficient is lost by the chosen parameter precision. -/
theorem globalDegreeBudget_lt_precision (k Bjet : ℕ) :
    globalDegreeBudget k Bjet < parameterPrecision k Bjet := Nat.lt_succ_self _

/-- The confluent parameter ring has positive precision, including boundary degree budgets. -/
theorem parameterPrecision_pos (k Bjet : ℕ) : 0 < parameterPrecision k Bjet :=
  Nat.succ_pos _

variable {E : Type*} [Field E]

/-- Scalar integration denominators are units because their indices lie below `p`. -/
theorem Supported.integration_unit {p r k Bjet i : ℕ} [CharP E p]
    (hs : Supported p r k Bjet) (hi : 0 < i) (hik : i < k) : IsUnit (i : E) := by
  apply isUnit_iff_ne_zero.mpr
  rw [Ne, CharP.cast_eq_zero_iff E p]
  exact Nat.not_dvd_of_pos_of_lt hi (hik.trans_le hs.precision_le)

/-- Binomial Hasse pivots are derived from the same guard, not provided by the caller. -/
theorem Supported.hasse_pivot_unit {p r k Bjet i : ℕ} [CharP E p]
    (hs : Supported p r k Bjet) (hri : r ≤ i) (hik : i < k) :
    IsUnit (i.choose r : E) := by
  apply isUnit_iff_ne_zero.mpr
  have hp : 0 < p := (Nat.zero_le i).trans_lt (hik.trans_le hs.precision_le)
  exact Polynomial.natCast_choose_ne_zero_of_lt_charP
    (CharP.char_prime_of_ne_zero E (Nat.ne_of_gt hp)) (hik.trans_le hs.precision_le) hri

variable [BEq E] [LawfulBEq E] [DecidableEq E]

/-- A stored polynomial is a bounded global normal form for a monic equation of degree `b`. -/
def NormalFormBound {r : ℕ} (b L : ℕ) (p : CMvPolynomial (r + 1) E) : Prop :=
  (splitLast p).toPoly.degree < (b : WithBot ℕ) ∧ (fromCMvPolynomial p).totalDegree ≤ L

/-- Monicity, exact quotient degree, and bounded output normal forms are separate certificates. -/
def ChartData.NormalForms {r k : ℕ} (chart : ChartData E r k) (b L : ℕ) : Prop :=
  (splitLast chart.equation).monic ∧ (splitLast chart.equation).natDegree = b ∧
    NormalFormBound b L chart.denominator ∧ ∀ j, NormalFormBound b L (chart.numerators j)

omit [DecidableEq E] in
/-- Clearing the computed coefficients turns the stored agreement polynomial into the
common denominator times the Taylor agreement residual, over any target commutative ring. -/
theorem ChartData.eval₂_agreement_of_cleared {r k : ℕ} {A : Type*} [CommRing A]
    (chart : ChartData E r k) (base : E →+* A) (point : Fin (r + 1) → A)
    (coefficients : Fin k → A)
    (hclear : ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
      CMvPolynomial.eval₂ base point chart.denominator * coefficients j)
    (alpha received : E) :
    CMvPolynomial.eval₂ base point (chart.agreement alpha received) =
      CMvPolynomial.eval₂ base point chart.denominator *
        ((∑ j : Fin k, coefficients j * (base alpha - base chart.center) ^ j.val) -
          base received) := by
  rw [chart.eval₂_agreement]
  simp_rw [hclear, mul_assoc]
  rw [← Finset.mul_sum]
  ring

end ReedSolomon.HiddenDerivative.FastTaylor
