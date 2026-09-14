/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Producer
public import ArkLib.Data.Polynomial.PolynomialThreshold.Degree

/-! # Executed coefficient-degree budgets for the curve producer -/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ProducerBudget

open CompPoly Polynomial
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

omit [DecidableEq E] in
private theorem degree_sum_eq (cs : List (CPolynomial E)) :
    (∑ i ∈ Finset.range cs.toArray.size, (cs.toArray[i]?.getD 1).natDegree) =
      (cs.map CPolynomial.natDegree).sum := by
  rw [List.size_toArray, ← Fin.sum_univ_eq_sum_range]
  have he (i : Fin cs.length) : cs[i.val]?.getD 1 = cs[i] := by
    rw [List.getElem?_eq_getElem i.isLt]
    rfl
  simp_rw [List.getElem?_toArray, he]
  rw [← List.sum_ofFn]
  change (List.ofFn fun i : Fin cs.length => CPolynomial.natDegree cs[i.val]).sum = _
  rw [List.ofFn_getElem_eq_map]

omit [DecidableEq E] in
/-- The threshold compresses the actual coefficient-degree sum; radicalization only reduces
the base degree. Execution itself supplies the valid threshold range. -/
theorem filter_base_degree_mul_le (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a) (A k : ℕ)
    (h : CPolynomial (CPolynomial E)) (gs : List (CPolynomial (CPolynomial E)))
    (out : FilterCore.Trace E) (hout : FilterCore.run p inverse A k h gs = some out)
    (G : CPolynomial E) (hG : out.base = some G) :
    G.natDegree * (A - k + 1) ≤ (out.coefficients.map CPolynomial.natDegree).sum := by
  classical
  obtain ⟨cs, H, hcs, hH, rfl⟩ := FilterCore.run_provenance p inverse A k h gs out hout
  have hm := (FilterCore.coefficients?_properties h gs cs hcs).2
  have hmonic := FilterCore.threshold_monic cs hm _ H hH
  have hdegree := CPolynomial.CharacteristicSafeRadical.radical_degree_le
    p inverse hinverse H hmonic
  have hGdef := (FilterCore.finish_base_some p inverse cs H G hG).2
  have hrange : 1 ≤ A - k + 1 ∧ A - k + 1 ≤ cs.toArray.size := by
    unfold CPolynomial.PolynomialThreshold.threshold at hH
    split at hH
    · assumption
    · contradiction
  have hb := CPolynomial.PolynomialThreshold.threshold_degree_le cs.toArray (A - k + 1)
    (by
      intro c hc
      exact (CPolynomial.toPoly_eq_zero_iff c).not.mp
        ((CPolynomial.monic_toPoly_iff c).mp (hm c (by simpa using hc))).ne_zero)
    hrange.1 hrange.2 hH
  rw [degree_sum_eq] at hb
  change G.natDegree * (A - k + 1) ≤ _
  rw [hGdef, mul_comm]
  exact (Nat.mul_le_mul_left _ hdegree).trans hb

/-- Sum the degrees returned by the actual per-position coefficient scan. -/
def coefficientDegreeBudget (h : CPolynomial (CPolynomial E))
    (gs : List (CPolynomial (CPolynomial E))) : ℕ :=
  (((FilterCore.coefficients? h gs).getD []).map CPolynomial.natDegree).sum

/-- The full producer inherits threshold compression, including every empty-output branch. -/
theorem run_base_degree_mul_le {k : ℕ} (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) :
    (Producer.run p inverse hinverse chart hh A gs).baseDegree * (A - k + 1) ≤
      coefficientDegreeBudget (Producer.retained chart) gs := by
  unfold Producer.run
  split
  · split
    · simp [Producer.empty]
    · rename_i out hout
      split
      · simp [Producer.empty]
      · rename_i G hG
        have hb := filter_base_degree_mul_le p inverse hinverse A k
          (Producer.retained chart) gs out hout G hG
        obtain ⟨cs, H, hcs, _, rfl⟩ := FilterCore.run_provenance p inverse A k
          (Producer.retained chart) gs out hout
        simpa [coefficientDegreeBudget, hcs, FilterCore.finish] using hb
  · simp [Producer.empty]

/-- The executed total quotient dimension has the same threshold compression, multiplied
by the retained fiber degree. This bound counts nonreduced multiplicities. -/
theorem run_dimension_mul_le {k : ℕ} (p : ℕ) [Fact p.Prime] [CharP E p]
    (inverse : E → E) (hinverse : ∀ a, inverse a ^ p = a)
    (chart : ChartData E 1 k) (hh : (chartPolynomials chart).equation.monic)
    (A : ℕ) (gs : List (CPolynomial (CPolynomial E))) :
    ((Producer.run p inverse hinverse chart hh A gs).components.map
      fun c => c.val.dimension).sum * (A - k + 1) ≤
      coefficientDegreeBudget (Producer.retained chart) gs *
        (Producer.retained chart).natDegree := by
  have hd := Producer.run_dimension_le p inverse hinverse chart hh A gs
  have hb := run_base_degree_mul_le p inverse hinverse chart hh A gs
  calc
    _ ≤ ((Producer.run p inverse hinverse chart hh A gs).baseDegree *
        (Producer.retained chart).natDegree) * (A - k + 1) := Nat.mul_le_mul_right _ hd
    _ = ((Producer.run p inverse hinverse chart hh A gs).baseDegree * (A - k + 1)) *
        (Producer.retained chart).natDegree := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hb

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ProducerBudget
