/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.Polynomial.BivariateMultiplicity
import ArkLib.Data.Polynomial.Trivariate

/-!
# Divisibility after symbolic specialization

Enough agreement points force a low-degree polynomial to be a root of the specialized
interpolant. The argument remains valid when the specialized interpolant is zero.
-/

namespace ProximityGap

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-- Symbolic multiplicity supplies Hasse vanishing at every challenge, even when the
specialized polynomial is zero. -/
theorem hasOrderAt_specialization_of_rootMultiplicity
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (x z : F) (y : Polynomial F) (m : ℕ)
    (hmult : (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C x) y) :
    GuruswamiSudan.HasOrderAt (Trivariate.evalAtZ z Q) x (y.eval z) m := by
  intro r s hrs
  have hv := (Bivariate.le_rootMultiplicity_iff_of_ne_zero Q hQ _ _ m).mp hmult r s hrs
  have heval := congrArg (Polynomial.eval z) hv
  have hshift := Bivariate.map_shift (Polynomial.evalRingHom z) Q (C x) y
  have hcoeff := congrArg (fun P : Polynomial (Polynomial F) => (P.coeff s).coeff r) hshift
  simp only [coeff_map, coe_mapRingHom, coe_evalRingHom, eval_C] at hcoeff
  change (Polynomial.eval z (((Bivariate.shift Q (C x) y).coeff s).coeff r)) =
    ((Bivariate.shift (Trivariate.evalAtZ z Q) x (y.eval z)).coeff s).coeff r at hcoeff
  change ((Bivariate.shift (Trivariate.evalAtZ z Q) x (y.eval z)).coeff s).coeff r = 0
  rw [← hcoeff]
  simpa using heval

omit [DecidableEq F] in
/-- A coefficient-support bound and enough Hasse zeros imply the usual GS linear factor. -/
theorem linear_factor_dvd_of_hasse_agreement {n k m : ℕ} (Q : Polynomial (Polynomial F))
    (x : Fin n ↪ F) (T : Finset (Fin n)) (p : Polynomial F) (D : ℝ)
    (hp : p.natDegree ≤ k)
    (hD : ∀ i j, (Q.coeff j).coeff i ≠ 0 → ((i + k * j : ℕ) : ℝ) < D)
    (hvan : ∀ a ∈ T, GuruswamiSudan.HasOrderAt Q (x a) (p.eval (x a)) m)
    (hcount : D ≤ (m * T.card : ℕ)) :
    Polynomial.X - C p ∣ Q := by
  classical
  by_cases hQ : Q = 0
  · rw [hQ]
    exact dvd_zero _
  have hw : (Bivariate.natWeightedDegree Q 1 k : ℝ) < D := by
    obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup Q.support
      (Polynomial.nonempty_support_iff.mpr hQ)
      (fun j => 1 * (Q.coeff j).natDegree + k * j)
    unfold Bivariate.natWeightedDegree
    rw [heq]
    have hc : Q.coeff j ≠ 0 := mem_support_iff.mp hj
    have hi : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 :=
      mem_support_iff.mp (natDegree_mem_support_of_nonzero hc)
    simpa using hD (Q.coeff j).natDegree j hi
  have hevalD : ((Q.eval p).natDegree : ℝ) < D := by
    have heval := GuruswamiSudan.degree_eval_le_weightedDegree Q p (k + 1) (by simpa using hp)
    have heval' : (Q.eval p).natDegree ≤ Bivariate.natWeightedDegree Q 1 k := by
      simpa using heval
    exact (by exact_mod_cast heval' : ((Q.eval p).natDegree : ℝ) ≤
      Bivariate.natWeightedDegree Q 1 k).trans_lt hw
  by_cases heval0 : Q.eval p = 0
  · exact dvd_iff_isRoot.mpr heval0
  · have hroots : ∀ a ∈ T, m ≤ (Q.eval p).rootMultiplicity (x a) := by
      intro a ha
      exact (GuruswamiSudan.orderAt_eval_ge Q p (x a) m (hvan a ha)).resolve_left heval0
    have hdeg : (Q.eval p).natDegree < m * T.card := by
      exact_mod_cast hevalD.trans_le hcount
    exact dvd_iff_isRoot.mpr
      (GuruswamiSudan.roots_le_degree_of_deg_lt_roots (ωs := x) (Q.eval p) m T hroots hdeg)

/-- Every challenge specialization admits the GS divisibility argument, including those
where the entire specialized interpolant vanishes. Agreement is on the supplied set `T`. -/
theorem linear_factor_dvd_specialization_of_agreement {n k m : ℕ}
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (x : Fin n ↪ F) (y : Fin n → Polynomial F) (z : F)
    (T : Finset (Fin n)) (p : Polynomial F) (D : ℝ) (hp : p.natDegree ≤ k)
    (hD : ∀ i j h, ((Q.coeff j).coeff i).coeff h ≠ 0 → ((i + k * j : ℕ) : ℝ) < D)
    (hmult : ∀ a, (some m : Option ℕ) ≤ Bivariate.rootMultiplicity Q (C (x a)) (y a))
    (hagrees : ∀ a ∈ T, p.eval (x a) = (y a).eval z)
    (hcount : D ≤ (m * T.card : ℕ)) :
    Polynomial.X - C p ∣ Trivariate.evalAtZ z Q := by
  classical
  apply linear_factor_dvd_of_hasse_agreement (Trivariate.evalAtZ z Q) x T p D hp
  · intro i j hc
    have hc' : ((Q.coeff j).coeff i) ≠ 0 := by
      intro hz
      apply hc
      simp [Trivariate.evalAtZ, coeff_map, hz]
    obtain ⟨h, hh⟩ : ∃ h, ((Q.coeff j).coeff i).coeff h ≠ 0 := by
      by_contra h
      push Not at h
      exact hc' (Polynomial.ext h)
    exact hD i j h hh
  · intro a ha
    rw [hagrees a ha]
    exact hasOrderAt_specialization_of_rootMultiplicity Q hQ (x a) z (y a) m (hmult a)
  · exact hcount

end ProximityGap
