/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.TruncatedSeries.Basic
public import ArkLib.Data.Polynomial.ConfluentAlgebra.Inverse
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative

/-!
# Precision-doubling series arithmetic over the confluent algebra

Series inversion computes the inverse of its constant coefficient, then uses Newton doubling
in the stored quotient by `Z^k`. The nonreduced coefficient algebra is never treated as a field.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra.SeriesNewton

open CompPoly ArkLib.TruncatedSeries

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable {r N : ℕ} [Fact (0 < N)]
variable (h : CPolynomial (CPoly.BoxAlgebra.Carrier r N E))
variable [Fact h.monic] [Fact (0 < h.toPoly.degree)]

/-- Compute a truncated inverse series from a computed constant-coefficient inverse. -/
def inverseSeries? (k : ℕ) (a : CPolynomial (Representative h)) :
    Option (CPolynomial (Representative h)) :=
  if k = 0 then some 0 else
    (inverse? h (a.coeff 0)).map (fun b =>
      (Polynomial.NewtonInverse.correct k (project k a) (project k (CPolynomial.C b))).val)

/-- The returned series is a right inverse at the requested precision. -/
theorem inverseSeries?_sound (k : ℕ) (a b : CPolynomial (Representative h))
    (hb : inverseSeries? h k a = some b) : LowEq k (a * b) 1 := by
  by_cases hk : k = 0
  · subst k
    intro i hi
    omega
  rw [inverseSeries?, if_neg hk] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hinv := (inverse?_sound h (a.coeff 0) b₀ hb₀).1
  have he : Order 1 (1 - a * CPolynomial.C b₀) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp [CPolynomial.coeff_sub, CPolynomial.coeff_mul, CPolynomial.coeff_C,
      CPolynomial.coeff_one, CPolynomial.coeff_zero, hinv]
  have hepow : Order k ((1 - a * CPolynomial.C b₀) ^ k) := by
    simpa using he.pow k
  have hz := (project_eq_zero_iff k _).mpr hepow
  rw [map_pow, map_sub, map_one, map_mul] at hz
  have hright := Polynomial.NewtonInverse.right_inverse k (project k a)
    (project k (CPolynomial.C b₀)) hz
  apply (project_eq_iff k _ _).mp
  rw [map_mul, project_representative, map_one]
  exact hright

/-- In positive precision, a failed series inversion means its constant coefficient is a nonunit. -/
theorem inverseSeries?_eq_none_iff (k : ℕ) (hk : 0 < k)
    (a : CPolynomial (Representative h)) :
    inverseSeries? h k a = none ↔ ¬ ∃ b, a.coeff 0 * b = 1 := by
  rw [inverseSeries?, if_neg (by omega), Option.map_eq_none_iff, inverse?_eq_none_iff]

/-- Every returned inverse is stored below the requested degree cap. -/
theorem inverseSeries?_degree (k : ℕ) (a b : CPolynomial (Representative h))
    (hb : inverseSeries? h k a = some b) : b.toPoly.degree < k := by
  by_cases hk : k = 0
  · subst k
    simp only [inverseSeries?, ↓reduceIte, Option.some.injEq] at hb
    subst b
    simp [CPolynomial.toPoly_zero]
  rw [inverseSeries?, if_neg hk] at hb
  obtain ⟨b₀, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  rw [← project_representative k
    (Polynomial.NewtonInverse.correct k (project k a) (project k (CPolynomial.C b₀))),
    project_val]
  exact degree_truncate_lt k _

/-- Executable embedding of the ground field into the stored confluent coefficient ring. -/
def scalarHom : E →+* Representative h := (constantHom h).comp parameterConstantHom

/-- Executable constant-polynomial embedding. -/
def seriesScalarHom : E →+* CPolynomial (Representative h) where
  toFun a := CPolynomial.C (scalarHom h a)
  map_zero' := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.toPoly_zero]
  map_one' := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
  map_add' a b := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_add]
  map_mul' a b := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.C_toPoly, CPolynomial.toPoly_mul]

/-- Substitute the shifted independent variable and the stored Hasse jet. -/
def jetPoint (k d : ℕ) (c : E) (Y : CPolynomial (Representative h)) :
    Fin (d + 2) → CPolynomial (Representative h) :=
  fun i => if i.val = 0 then CPolynomial.X + seriesScalarHom h c
    else hasse k (i.val - 1) Y

/-- Evaluate the actual stored nonlinear equation on a Hasse jet. -/
def jetEval (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) : CPolynomial (Representative h) :=
  CPoly.CMvPolynomial.eval₂ (seriesScalarHom h) (jetPoint h k d c Y) T

/-- Compute a jet partial derivative, then evaluate it on the current jet. -/
def jetPartial (k d : ℕ) (c : E) (T : CPoly.CMvPolynomial (d + 2) E)
    (Y : CPolynomial (Representative h)) (j : Fin (d + 1)) :
    CPolynomial (Representative h) :=
  jetEval h k d c (CPoly.CMvPolynomial.partialDerivative ⟨j.val + 1, by omega⟩ T) Y

/-- Algebraic Newton update with a computed separant inverse. -/
def algebraicStep? (k : ℕ) (c : E) (T : CPoly.CMvPolynomial 2 E)
    (Y : CPolynomial (Representative h)) : Option (CPolynomial (Representative h)) :=
  (inverseSeries? h k (jetPartial h k 0 c T Y 0)).map fun V =>
    truncate k (Y - V * jetEval h k 0 c T Y)

/-- Execute algebraic Newton updates, propagating precisely the inversion failure. -/
def algebraicIterate? (k : ℕ) (c : E) (T : CPoly.CMvPolynomial 2 E) :
    ℕ → ℕ → CPolynomial (Representative h) → Option (CPolynomial (Representative h))
  | 0, _, Y => some Y
  | n + 1, m, Y =>
    (algebraicStep? h (min (2 * m) k) c T Y).bind (algebraicIterate? k c T n (2 * m))

/-- Start algebraic Newton from one initial root coefficient; no inverse or series is supplied. -/
def algebraicNewton? (k : ℕ) (c : E) (T : CPoly.CMvPolynomial 2 E)
    (y₀ : Representative h) : Option (CPolynomial (Representative h)) :=
  let Y := CPolynomial.C y₀
  if (jetEval h k 0 c T Y).coeff 0 == 0 then
    (inverse? h ((jetPartial h k 0 c T Y 0).coeff 0)).bind
      fun _ => algebraicIterate? h k c T (Polynomial.NewtonInverse.rounds k) 1 Y
  else none

end ArkLib.ConfluentAlgebra.SeriesNewton
