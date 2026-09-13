/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Scalar primary-split Chinese remainder equivalence

This is the product decomposition of one polynomial quotient, not an equivalence of entire
nested towers. Constant factors are retained as zero rings; no positive-degree assumption is used.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The actual powered split yields a product decomposition preserving full multiplicities. -/
noncomputable def primarySplitEquiv (h e : CPolynomial F) (hh : h.monic) :
    AdjoinRoot h.toPoly ≃+*
      AdjoinRoot (nilFactor h e).toPoly × AdjoinRoot (unitFactor h e).toPoly :=
  let I : Ideal F[X] := Ideal.span {(nilFactor h e).toPoly}
  let J : Ideal F[X] := Ideal.span {(unitFactor h e).toPoly}
  have hcop : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr (factors_isCoprime h e hh)
  have heq : Ideal.span {h.toPoly} = I * J := by
    have hn : h ≠ 0 := (CPolynomial.toPoly_eq_zero_iff h).not.mp
      ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, ← CPolynomial.toPoly_mul,
      factor_product h e hn]
  (Ideal.quotEquivOfEq heq).trans (Ideal.quotientMulEquivQuotientProd I J hcop)

/-- The agreeing projection is the canonical restriction of polynomial representatives. -/
@[simp] theorem primarySplitEquiv_mk_fst (h e : CPolynomial F) (hh : h.monic)
    (p : F[X]) :
    (primarySplitEquiv h e hh (AdjoinRoot.mk h.toPoly p)).1 =
      AdjoinRoot.mk (nilFactor h e).toPoly p := by
  change (Ideal.quotientMulEquivQuotientProd
    (Ideal.span {(nilFactor h e).toPoly}) (Ideal.span {(unitFactor h e).toPoly})
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr (factors_isCoprime h e hh))
    (Ideal.Quotient.mk _ p)).1 = _
  exact Ideal.quotientMulEquivQuotientProd_fst _ _ _ _

/-- The nonagreeing projection is the canonical restriction of polynomial representatives. -/
@[simp] theorem primarySplitEquiv_mk_snd (h e : CPolynomial F) (hh : h.monic)
    (p : F[X]) :
    (primarySplitEquiv h e hh (AdjoinRoot.mk h.toPoly p)).2 =
      AdjoinRoot.mk (unitFactor h e).toPoly p := by
  change (Ideal.quotientMulEquivQuotientProd
    (Ideal.span {(nilFactor h e).toPoly}) (Ideal.span {(unitFactor h e).toPoly})
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr (factors_isCoprime h e hh))
    (Ideal.Quotient.mk _ p)).2 = _
  exact Ideal.quotientMulEquivQuotientProd_snd _ _ _ _

/-- Both projections use the same input representative; no root or factorization oracle occurs. -/
theorem primarySplitEquiv_mk (h e : CPolynomial F) (hh : h.monic) (p : F[X]) :
    primarySplitEquiv h e hh (AdjoinRoot.mk h.toPoly p) =
      (AdjoinRoot.mk (nilFactor h e).toPoly p, AdjoinRoot.mk (unitFactor h e).toPoly p) := by
  exact Prod.ext (primarySplitEquiv_mk_fst h e hh p) (primarySplitEquiv_mk_snd h e hh p)

end ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit
