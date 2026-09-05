/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.PrimeFamilyHilbertCoefficient

/-!
# Hilbert coefficients of finite ideal intersections

The diagonal map embeds the quotient by an intersection into the product of its
component quotients without increasing degree. Combined with prime separators,
this identifies coefficients at a common upper degree bound.
-/

noncomputable section

namespace AffineHilbert

open MvPolynomial Polynomial Filter
open scoped BigOperators

variable {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]

/-- The actual filtered diagonal map gives an upper bound by the sum of quotient dimensions. -/
theorem hilbertFunction_iInf_le_sum (P : ι → Ideal (MvPolynomial σ F)) (N : ℕ) :
    hilbertFunction (⨅ i, P i) N ≤ ∑ i, hilbertFunction (P i) N := by
  classical
  let φ : quotientDegreeLE (⨅ i, P i) N →ₗ[F] ∀ i, quotientDegreeLE (P i) N :=
    LinearMap.pi fun i ↦
      ((Ideal.Quotient.factorₐ F (iInf_le P i)).toLinearMap.domRestrict
        (quotientDegreeLE (⨅ i, P i) N)).codRestrict (quotientDegreeLE (P i) N) (fun x ↦ by
          obtain ⟨p, hp, hpx⟩ := x.property
          refine ⟨p, hp, ?_⟩
          change Ideal.Quotient.mkₐ F (P i) p = Ideal.Quotient.factorₐ F (iInf_le P i) x
          rw [← hpx]
          rfl)
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨p, hp, hpx⟩ := x.property
    obtain ⟨q, hq, hqy⟩ := y.property
    rw [← hpx, ← hqy]
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_iInf.mpr
    intro i
    have hi := congrArg (fun z : ∀ i, quotientDegreeLE (P i) N ↦ (z i).val) hxy
    change Ideal.Quotient.factorₐ F (iInf_le P i) x.val =
      Ideal.Quotient.factorₐ F (iInf_le P i) y.val at hi
    rw [← hpx, ← hqy] at hi
    exact Ideal.Quotient.eq.mp hi
  have h := LinearMap.finrank_le_finrank_of_injective hφ
  let _ (i : ι) : Module.Free F (quotientDegreeLE (P i) N) :=
    Module.Free.of_divisionRing F _
  unfold hilbertFunction
  rw [← Module.finrank_pi_fintype]
  exact h

end AffineHilbert

namespace AffineHilbert

open MvPolynomial Polynomial Filter
open scoped BigOperators

variable {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]

/-- The coefficient at a common degree bound is subadditive under intersection. -/
theorem hilbertPolynomial_iInf_coeff_le_sum
    (P : ι → Ideal (MvPolynomial σ F)) (d : ℕ)
    (hPdeg : ∀ i, (hilbertPolynomial (P i)).natDegree ≤ d)
    (hInfDeg : (hilbertPolynomial (⨅ i, P i)).natDegree ≤ d) :
    (hilbertPolynomial (⨅ i, P i)).coeff d ≤ ∑ i, (hilbertPolynomial (P i)).coeff d := by
  classical
  let S : ℚ[X] := ∑ i, hilbertPolynomial (P i)
  have hSdeg : S.natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact hPdeg i
  have hle : ∀ᶠ N : ℕ in atTop,
      (hilbertPolynomial (⨅ i, P i)).eval (N : ℚ) ≤ S.eval (N : ℚ) := by
    have hall : ∀ᶠ N : ℕ in atTop, ∀ i,
        (hilbertPolynomial (P i)).eval (N : ℚ) = (hilbertFunction (P i) N : ℚ) :=
      Filter.eventually_all.mpr (fun i ↦ hilbertPolynomial_eventually_eval (P i))
    filter_upwards [hilbertPolynomial_eventually_eval (⨅ i, P i), hall] with N hN hPN
    rw [hN]
    dsimp [S]
    rw [Polynomial.eval_finsetSum]
    simp_rw [hPN]
    exact_mod_cast hilbertFunction_iInf_le_sum P N
  have hcoeff := coeff_le_of_natDegree_le_of_eventually_eval_nat_le hInfDeg hSdeg hle
  simpa only [S, Polynomial.finsetSum_coeff] using hcoeff

/-- For incomparable prime components, the coefficient at any common upper degree
bound is exactly the sum of the component coefficients. Lower-degree components
have zero coefficient here, so this is not a purity theorem. -/
theorem hilbertPolynomial_iInf_coeff_eq_sum
    (P : ι → Ideal (MvPolynomial σ F)) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) (d : ℕ)
    (hPdeg : ∀ i, (hilbertPolynomial (P i)).natDegree ≤ d)
    (hInfDeg : (hilbertPolynomial (⨅ i, P i)).natDegree ≤ d) :
    (hilbertPolynomial (⨅ i, P i)).coeff d = ∑ i, (hilbertPolynomial (P i)).coeff d := by
  exact le_antisymm (hilbertPolynomial_iInf_coeff_le_sum P d hPdeg hInfDeg)
    (sum_hilbertPolynomial_coeff_le_iInf P hP hinc d hPdeg hInfDeg)

end AffineHilbert
