/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Constructor

/-!
# Global contract of one computed Taylor chart

This module identifies the recovered denominator and numerators at every point of the
computed chart hypersurface. On its regular locus, the executable agreement polynomial is
the common denominator times the Taylor agreement residual.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- Every returned chart globally evaluates to the literal cleared Taylor numerators on its
computed hypersurface. This remains valid after any coefficient-field embedding. -/
theorem construct?_cleared_global {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [CommRing A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0) :
    let S := initialJetSeparant center (semanticEquation T)
    CMvPolynomial.eval₂ base point chart.denominator =
        CMvPolynomial.eval₂ base point
          (Geometry.projectPolynomial chart.projection (toCMvPolynomial (S ^ (2 * k)))) ∧
      ∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
        CMvPolynomial.eval₂ base point (Geometry.projectPolynomial chart.projection
          (toCMvPolynomial (commonTaylorNumerator center (semanticEquation T) k j))) := by
  unfold construct? at hc
  split at hc
  next hguard =>
    simp only [Option.bind_eq_some_iff] at hc
    obtain ⟨g, hg, hc⟩ := hc
    split at hc
    next hm =>
      split at hc
      next hb =>
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
        obtain ⟨a, ha, inverse, hinverse, Y, hY, rfl⟩ := hc
        let N := parameterPrecision k Bjet
        let : Fact (0 < N) := ⟨parameterPrecision_pos k Bjet⟩
        let : Fact (splitLast g.polynomial).monic := ⟨hm⟩
        let : Fact (0 < (splitLast g.polynomial).toPoly.degree) := ⟨by
          apply Polynomial.natDegree_pos_iff_degree_pos.mp
          simpa only [CPolynomial.natDegree_toPoly] using hb⟩
        let S := initialJetSeparant center (semanticEquation T)
        let sep := ConfluentSample.localSeparant N g.polynomial
          (Geometry.projectPolynomial g.forward (initialSeparant center T)) a
        let φ := CMvPolynomial.eval₂Hom base point
        have hz' : φ g.polynomial = 0 := hz
        have hs : sep = MvPolynomial.eval₂
            (SeriesNewton.scalarHom (localEquation N a g.polynomial))
            (localInitialJet N g.polynomial a g.forward) S := by
          dsimp only [sep, ConfluentSample.localSeparant, S]
          rw [local_project_eq_eval, initialSeparant_semantics]
        let Pden := Geometry.projectPolynomial g.forward (toCMvPolynomial (S ^ (2 * k)))
        have hden : localHom N g.polynomial a Pden = sep ^ (2 * k) := by
          dsimp only [Pden]
          rw [localHom_apply, local_project_eq_eval, fromCMvPolynomial_toCMvPolynomial,
            MvPolynomial.eval₂_pow, hs]
        have hPden : (fromCMvPolynomial Pden).totalDegree ≤ globalDegreeBudget k Bjet := by
          apply (Geometry.totalDegree_projectPolynomial_le _ _).trans
          rw [fromCMvPolynomial_toCMvPolynomial]
          calc
            (S ^ (2 * k)).totalDegree ≤ 2 * k * S.totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ 2 * k * (Bjet - 1) := Nat.mul_le_mul_left _
              ((totalDegree_initialJetSeparant_le center (semanticEquation T)).trans
                (Nat.sub_le_sub_right hB 1))
            _ ≤ globalDegreeBudget k Bjet := by unfold globalDegreeBudget; omega
        constructor
        · change φ (GlobalNormalForm.recoverFlat a (sep ^ (2 * k)).val) = φ Pden
          rw [← hden]
          exact eval_recover_local N (globalDegreeBudget k Bjet)
            (globalDegreeBudget_lt_precision k Bjet) component values g hg a Pden hPden φ hz'
        · intro j
          let Pnum := Geometry.projectPolynomial g.forward
            (toCMvPolynomial (commonTaylorNumerator center (semanticEquation T) k j))
          have hnum : localHom N g.polynomial a Pnum = sep ^ (2 * k) * Y.coeff j.val := by
            exact local_numerator_provenance N g.polynomial a g.forward p k center T
              hguard.1 Y hY j
          have hPnum : (fromCMvPolynomial Pnum).totalDegree ≤ globalDegreeBudget k Bjet := by
            apply (Geometry.totalDegree_projectPolynomial_le _ _).trans
            rw [fromCMvPolynomial_toCMvPolynomial]
            exact (totalDegree_commonTaylorNumerator_le center (semanticEquation T) hv k j).trans
              (Nat.add_le_add_left
                (Nat.mul_le_mul_left (2 * k) (Nat.sub_le_sub_right hB 1)) 1)
          change φ (GlobalNormalForm.recoverFlat a
            (sep ^ (2 * k) * Y.coeff j.val).val) = φ Pnum
          rw [← hnum]
          exact eval_recover_local N (globalDegreeBudget k Bjet)
            (globalDegreeBudget_lt_precision k Bjet) component values g hg a Pnum hPnum φ hz'
      next => simp at hc
    next => simp at hc
  next => simp at hc

/-- On the regular locus, the stored agreement polynomial is its nonzero computed denominator
times the Taylor residual of the actual recovered rational coefficients. -/
theorem construct?_agreement_at_regular {r k : ℕ} (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial (r + 2) E) (component : CMvPolynomial (r + 1) E)
    (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData E r k) (hc : construct? p r k Bjet center T component values = some chart)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point chart.equation = 0)
    (hregular : CMvPolynomial.eval₂ base point chart.denominator ≠ 0)
    (alpha received : E) :
    ((let S := initialJetSeparant center (semanticEquation T)
      CMvPolynomial.eval₂ base point chart.denominator =
          CMvPolynomial.eval₂ base point
            (Geometry.projectPolynomial chart.projection (toCMvPolynomial (S ^ (2 * k)))) ∧
        (∀ j, CMvPolynomial.eval₂ base point (chart.numerators j) =
          CMvPolynomial.eval₂ base point (Geometry.projectPolynomial chart.projection
            (toCMvPolynomial (commonTaylorNumerator center (semanticEquation T) k j))))) ∧
      CMvPolynomial.eval₂ base point (chart.agreement alpha received) =
        CMvPolynomial.eval₂ base point chart.denominator *
          ((∑ j : Fin k, (CMvPolynomial.eval₂ base point (chart.numerators j) /
            CMvPolynomial.eval₂ base point chart.denominator) *
              (base alpha - base chart.center) ^ j.val) - base received)) := by
  constructor
  · exact construct?_cleared_global p Bjet center T component values hv hB chart hc base point hz
  · apply chart.eval₂_agreement_of_cleared base point _ ?_ alpha received
    intro j
    field_simp

end ReedSolomon.HiddenDerivative.FastTaylor
