/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SquarefreeSupport

/-!
# Polynomial threshold comparators

An ascending comparator replaces two polynomials by their monic gcd and lcm.
Its outputs preserve the product and total degree. At every extension-field
point, the smaller output records intersection and the larger output union.
These are the arithmetic primitives for a distinct-position sorting network.
-/

@[expose] public section

namespace CompPoly.CPolynomial.PolynomialThreshold

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The smaller and larger wires of an ascending polynomial comparator. -/
def compare (a b : CPolynomial F) : CPolynomial F × CPolynomial F :=
  (gcdMonic a b, lcmMonic a b)

/-- A comparator preserves monic inputs on both output wires. -/
theorem compare_monic {a b : CPolynomial F} (ha : a.monic) (hb : b.monic) :
    (compare a b).1.monic ∧ (compare a b).2.monic := by
  have ha0 : a ≠ 0 :=
    (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero
  exact ⟨gcdFactor_monic ha0, lcmMonic_monic ha hb⟩

/-- Nonzero inputs produce two nonzero output wires. -/
theorem compare_ne_zero {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (compare a b).1 ≠ 0 ∧ (compare a b).2 ≠ 0 := by
  refine ⟨?_, lcmMonic_ne_zero ha hb⟩
  exact (toPoly_eq_zero_iff _).not.mp
    ((monic_toPoly_iff _).mp (gcdFactor_monic (e := b) ha)).ne_zero

/-- The two wires preserve the input product exactly. -/
theorem compare_product {a b : CPolynomial F} (ha : a ≠ 0) :
    (compare a b).1 * (compare a b).2 = a * b :=
  gcdMonic_mul_lcmMonic ha

/-- Every comparator conserves the sum of wire degrees. -/
theorem compare_degree {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (compare a b).1.natDegree + (compare a b).2.natDegree =
      a.natDegree + b.natDegree := by
  have hproduct := congrArg (CPolynomial.toPoly (R := F)) (compare_product (b := b) ha)
  rw [toPoly_mul, toPoly_mul] at hproduct
  have hout := compare_ne_zero ha hb
  have hdegree := congrArg Polynomial.natDegree hproduct
  rw [Polynomial.natDegree_mul ((toPoly_eq_zero_iff _).not.mpr hout.1)
      ((toPoly_eq_zero_iff _).not.mpr hout.2),
    Polynomial.natDegree_mul ((toPoly_eq_zero_iff _).not.mpr ha)
      ((toPoly_eq_zero_iff _).not.mpr hb)] at hdegree
  simpa only [← natDegree_toPoly] using hdegree

/-- The smaller wire vanishes exactly at common roots over any extension. -/
theorem compare_fst_eval₂_eq_zero_iff {K : Type*} [Field K]
    (phi : F →+* K) (x : K) (a b : CPolynomial F) :
    (compare a b).1.toPoly.eval₂ phi x = 0 ↔
      a.toPoly.eval₂ phi x = 0 ∧ b.toPoly.eval₂ phi x = 0 :=
  eval₂_gcdFactor_eq_zero_iff_left_right phi x a b

/-- The larger wire vanishes exactly at the union of roots over any extension. -/
theorem compare_snd_eval₂_eq_zero_iff {K : Type*} [Field K]
    (phi : F →+* K) (x : K) {a b : CPolynomial F} (ha : a ≠ 0) :
    (compare a b).2.toPoly.eval₂ phi x = 0 ↔
      a.toPoly.eval₂ phi x = 0 ∨ b.toPoly.eval₂ phi x = 0 :=
  eval₂_lcmMonic_eq_zero_iff phi x ha

end CompPoly.CPolynomial.PolynomialThreshold
