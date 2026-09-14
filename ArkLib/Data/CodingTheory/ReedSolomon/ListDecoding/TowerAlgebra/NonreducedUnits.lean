/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.GeometricSeparation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.InverseElimination

/-!
# Geometric units without fiber reduction

Nonvanishing detects units even when geometric points do not separate nilpotents. At each
geometric base root we cancel using coprimality with the full fiber polynomial, including its
multiplicities. Only the squarefree base is used to descend the resulting coefficient identities.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerRepresentation

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- At a base root, canonical reduction is ordinary remainder by the full specialized fiber. -/
theorem specialize_reduceElement {K : Type} [Field K] (phi : F →+* K) (x : K)
    {G : CPolynomial F} (hG : G.monic) (hx : G.toPoly.eval₂ phi x = 0)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (p : CPolynomial (CPolynomial F)) :
    specializeFiberCPolynomial (reduceElement G h p) phi x =
      specializeFiberCPolynomial p phi x %ₘ specializeFiberCPolynomial h phi x := by
  rw [reduceElement, reduceBase, specialize_reduceFiberCoefficients phi x hG hx]
  simp only [specializeFiberCPolynomial]
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hh,
    Polynomial.map_modByMonic _ ((CPolynomial.monic_toPoly_iff _).mp hh)]

/-- Nonvanishing permits cancellation modulo the full fiber, not just its radical. -/
theorem reduced_mul_injective_of_geometric_nonvanishing_nonreduced
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (a : CPolynomial (CPolynomial F))
    (ha : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        evalNested a (algebraMap F (AlgebraicClosure F)) x y ≠ 0)
    {p q : CPolynomial (CPolynomial F)}
    (hp : ElementReduced r.modulus r.fiber p) (hq : ElementReduced r.modulus r.fiber q)
    (he : reduceElement r.modulus r.fiber (a * p) =
      reduceElement r.modulus r.fiber (a * q)) : p = q := by
  let phi := algebraMap F (AlgebraicClosure F)
  have hmon : r.fiber.toPoly.Monic := (CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1
  have hs : ∀ x : AlgebraicClosure F, r.modulus.toPoly.aeval x = 0 →
      specializeFiberCPolynomial (p - q) phi x = 0 := by
    intro x hx
    let h := specializeFiberCPolynomial r.fiber phi x
    let b := specializeFiberCPolynomial a phi x
    let d := specializeFiberCPolynomial (p - q) phi x
    have hh : h.Monic := hmon.map _
    have hab : IsCoprime h b := by
      apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (AlgebraicClosure F) (AlgebraicClosure F) h b).mpr
      intro y
      by_cases hy : h.aeval y = 0
      · right
        have hz := ha x y ⟨hx, by simpa [h, phi, evalNested, Polynomial.aeval_def] using hy⟩
        simpa [b, evalNested, Polynomial.aeval_def] using hz
      · exact Or.inl hy
    have he' := congrArg (fun z => specializeFiberCPolynomial z phi x) he
    rw [specialize_reduceElement phi x hr.1 hx hr.2.2.2.1,
      specialize_reduceElement phi x hr.1 hx hr.2.2.2.1] at he'
    have hdvd : h ∣ b * d := by
      apply (Polynomial.modByMonic_eq_zero_iff_dvd hh).mp
      simpa [h, b, d, specializeFiberCPolynomial, CPolynomial.toPoly_mul,
        CPolynomial.toPoly_sub, mul_sub, Polynomial.sub_modByMonic] using sub_eq_zero.mpr he'
    have hd : d.degree < h.degree := by
      change ((p - q).toPoly.map _).degree < (r.fiber.toPoly.map _).degree
      rw [hmon.degree_map]
      exact Polynomial.degree_map_le.trans_lt (elementReduced_sub hp hq).1
    exact eq_zero_of_dvd_of_degree_lt (hab.dvd_of_dvd_mul_left hdvd) hd
  apply sub_eq_zero.mp
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [CPolynomial.toPoly_zero, Polynomial.coeff_zero, ← CPolynomial.coeff_toPoly]
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_zero]
  apply eq_zero_of_degree_lt_of_geometric_vanishing (K := AlgebraicClosure F)
    r.modulus.toPoly ((p - q).coeff i).toPoly ((CPolynomial.monic_toPoly_iff _).mp hr.1)
    hr.2.1 ((elementReduced_sub hp hq).2 i)
  intro x hx
  have hc := congrArg (fun z => z.coeff i) (hs x hx)
  simpa [specializeFiberCPolynomial, ← CPolynomial.coeff_toPoly, coefficientEval_apply,
    Polynomial.aeval_def, phi] using hc

end ReedSolomon.ListDecoding.TowerRepresentation

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- A geometrically nonvanishing element is a unit in a weak tower, including nilpotents. -/
theorem isTowerUnit_of_geometric_nonvanishing_nonreduced
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (a : CPolynomial (CPolynomial F))
    (ha : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        TowerRepresentation.evalNested a (algebraMap F (AlgebraicClosure F)) x y ≠ 0) :
    IsTowerUnit r.modulus r.fiber a := by
  have hd := multiplicationMatrix_det_ne_zero_of_injective hr.1 hr.2.2.2.1
    (TowerRepresentation.reduced_mul_injective_of_geometric_nonvanishing_nonreduced r hr a ha)
  obtain ⟨v, hv⟩ := inverseRepresentative?_exists_of_det_ne_zero
    hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hd
  exact isTowerUnit_of_inverseRepresentative?_eq_some _ _ _ _ hv

/-- Units do not vanish at points of a weak tower, over any extension field. -/
theorem isTowerUnit_nonvanishing_nonreduced
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (a : CPolynomial (CPolynomial F)) (ha : IsTowerUnit r.modulus r.fiber a)
    {K : Type} [Field K] (phi : F →+* K) (x y : K) (hp : r.Point phi x y) :
    TowerRepresentation.evalNested a phi x y ≠ 0 := by
  obtain ⟨v, hv, _⟩ := ha
  have he := congrArg (fun z => TowerRepresentation.evalNested z phi x y) hv
  rw [TowerRepresentation.evalNested_reduceElement phi x y hr.1 hp.1 hr.2.2.2.1 hp.2,
    TowerRepresentation.evalNested_reduceElement phi x y hr.1 hp.1 hr.2.2.2.1 hp.2] at he
  have he' : TowerRepresentation.evalNested a phi x y *
      TowerRepresentation.evalNested v phi x y = 1 := by
    simpa [TowerRepresentation.evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      CPolynomial.toPoly_mul, CPolynomial.toPoly_one] using he
  intro hz
  rw [hz, zero_mul] at he'
  exact zero_ne_one he'

/-- Geometric nonvanishing characterizes units without reducing any fiber. -/
theorem isTowerUnit_iff_geometric_nonvanishing_nonreduced
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (a : CPolynomial (CPolynomial F)) :
    IsTowerUnit r.modulus r.fiber a ↔
      ∀ x y : AlgebraicClosure F,
        r.Point (algebraMap F (AlgebraicClosure F)) x y →
          TowerRepresentation.evalNested a (algebraMap F (AlgebraicClosure F)) x y ≠ 0 := by
  exact ⟨fun ha x y hp => isTowerUnit_nonvanishing_nonreduced r hr a ha _ x y hp,
    isTowerUnit_of_geometric_nonvanishing_nonreduced r hr a⟩

/-- The executed elimination backend succeeds under weak-tower geometric nonvanishing. -/
theorem inverseElimination?_exists_of_geometric_nonvanishing_nonreduced [DecidableEq F]
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.NonreducedWellFormed width)
    (a : CPolynomial (CPolynomial F))
    (ha : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        TowerRepresentation.evalNested a (algebraMap F (AlgebraicClosure F)) x y ≠ 0) :
    ∃ inverse, inverseElimination? r.modulus r.fiber a = some inverse :=
  inverseElimination?_exists_of_isTowerUnit hr.1 hr.2.2.2.1 hr.2.2.2.2.1
    (isTowerUnit_of_geometric_nonvanishing_nonreduced r hr a ha)

end ReedSolomon.ListDecoding.TowerAlgebra
