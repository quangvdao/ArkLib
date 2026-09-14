/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ComponentDescent
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RadicalCorrectness
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

/-!
# Global removal of closed components

The powered function-field gcd removes complete primary components supported on the
obstruction. Its monic descent and complementary division have an exact global product,
so every point of the open curve survives even at component intersections and ramified
fibers. Generic coprimality does not assert disjointness in every special fiber.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval

open CompPoly Polynomial.FunctionFieldAlgorithms
open ComponentDescent

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Retain the global components not supported on the obstruction. -/
def retain (h s : CBivariate E) (b : ℕ) : CBivariate E :=
  exactComplement h (s ^ b)

/-- The removed factor, including its original primary multiplicities. -/
def removed (h s : CBivariate E) (b : ℕ) : CBivariate E :=
  monicGlobalGcd h (s ^ b)

theorem product (h s : CBivariate E) (b : ℕ) (hh : h.monic) :
    removed h s b * retain h s b = h :=
  monicGlobalGcd_mul_divByMonic h (s ^ b) hh

theorem retain_monic (h s : CBivariate E) (b : ℕ) (hh : h.monic) :
    (retain h s b).monic := by
  apply (CPolynomial.monic_toPoly_iff _).mpr
  apply ((CPolynomial.monic_toPoly_iff _).mp (monicGlobalGcd_monic h (s ^ b) hh)).of_mul_monic_left
  rw [← CPolynomial.toPoly_mul, show monicGlobalGcd h (s ^ b) = removed h s b from rfl,
    product h s b hh]
  exact (CPolynomial.monic_toPoly_iff _).mp hh

/-- Removed components vanish only on the obstruction, over every field extension. -/
theorem removed_point_obstruction {K : Type*} [Field K] (phi : E →+* K)
    (u v : K) (h s : CBivariate E) (b : ℕ) (hh : h.monic)
    (hz : evalAt phi u v (removed h s b) = 0) : evalAt phi u v s = 0 := by
  classical
  obtain ⟨q, hq⟩ := monicGlobalGcd_semantic_dvd_right h (s ^ b) hh
  have hp : evalAt phi u v (s ^ b) = 0 := by
    unfold evalAt
    rw [hq, Polynomial.eval₂_mul]
    change evalAt phi u v (removed h s b) * _ = 0
    rw [hz, zero_mul]
  rw [evalAt, show CBivariate.toPoly (s ^ b) = CBivariate.toPoly s ^ b from
    map_pow CBivariate.ringEquiv s b, Polynomial.eval₂_pow] at hp
  exact eq_zero_of_pow_eq_zero hp

/-- The open point set is unchanged; no intermediate denominator excludes a fiber. -/
theorem open_point_iff {K : Type*} [Field K] (phi : E →+* K)
    (u v : K) (h s : CBivariate E) (b : ℕ) (hh : h.monic)
    (hs : evalAt phi u v s ≠ 0) :
    evalAt phi u v (retain h s b) = 0 ↔ evalAt phi u v h = 0 := by
  have hid := congrArg (evalAt phi u v) (product h s b hh)
  rw [evalAt, CBivariate.toPoly_mul, Polynomial.eval₂_mul] at hid
  change evalAt phi u v (removed h s b) * evalAt phi u v (retain h s b) = _ at hid
  rw [← hid, mul_eq_zero, or_iff_right]
  exact fun hz => hs (removed_point_obstruction phi u v h s b hh hz)

open scoped Classical in
/-- A degree-bounded power removes all generic obstruction support, without reducedness. -/
theorem retain_generic_isCoprime (h s : CBivariate E) (b : ℕ) (hh : h.monic)
    (hzero : ClearDenominators.valueGlobal h ≠ 0)
    (hb : (ClearDenominators.valueGlobal h).natDegree ≤ b) :
    IsCoprime (ClearDenominators.valueGlobal (retain h s b))
      (ClearDenominators.valueGlobal s) := by
  apply TowerAlgebra.PrimarySplit.quotient_isCoprime_residual hzero hb
  · simpa only [RadicalCorrectness.valueGlobal_pow] using
      valueGlobal_monicGlobalGcd_associated h (s ^ b) hh
  · simpa only [ClearDenominators.valueGlobal_mul, removed] using congrArg
      (ClearDenominators.valueGlobal (F := E)) (product h s b hh)

/-- The stored fiber degree is already a sufficient saturation exponent. -/
theorem retain_degree_generic_isCoprime (h s : CBivariate E) (hh : h.monic) :
    IsCoprime (ClearDenominators.valueGlobal (retain h s h.natDegree))
      (ClearDenominators.valueGlobal s) := by
  apply retain_generic_isCoprime h s h.natDegree hh
  · intro hz
    have hraw : CPolynomial.toPoly h = 0 := by
      apply Polynomial.map_injective (CPolynomial.ringEquiv (R := E)).toRingHom
        (CPolynomial.ringEquiv (R := E)).injective
      apply Polynomial.map_injective _ (RatFunc.algebraMap_injective E)
      simpa [ClearDenominators.valueGlobal, CBivariate.toPoly_eq_map] using hz
    exact ((CPolynomial.monic_toPoly_iff _).mp hh).ne_zero hraw
  · unfold ClearDenominators.valueGlobal
    rw [Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective E),
      CBivariate.toPoly_eq_map,
      Polynomial.natDegree_map_eq_of_injective (CPolynomial.ringEquiv (R := E)).injective,
      CPolynomial.natDegree_toPoly]

open scoped Classical in
/-- Every multiplicity of a generic factor away from the obstruction is preserved. -/
theorem retained_primary_power_iff (h s : CBivariate E) (b : ℕ) (hh : h.monic)
    (p : Polynomial (RatFunc E)) (hp : Irreducible p)
    (hs : ¬p ∣ ClearDenominators.valueGlobal s) (m : ℕ) :
    p ^ m ∣ ClearDenominators.valueGlobal (retain h s b) ↔
      p ^ m ∣ ClearDenominators.valueGlobal h := by
  apply TowerAlgebra.PrimarySplit.primary_power_dvd_quotient_iff
    (D := ClearDenominators.valueGlobal (removed h s b))
    (E := ClearDenominators.valueGlobal s) (b := b) _ _ hp hs m
  · simpa only [ClearDenominators.valueGlobal_mul] using congrArg
      (ClearDenominators.valueGlobal (F := E)) (product h s b hh)
  · have ha := valueGlobal_monicGlobalGcd_associated h (s ^ b) hh
    exact ha.dvd.trans (by
      simpa only [RadicalCorrectness.valueGlobal_pow] using
        EuclideanDomain.gcd_dvd_right (ClearDenominators.valueGlobal h)
          (ClearDenominators.valueGlobal (s ^ b)))

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval
