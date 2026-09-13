/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.FactorizationCoverage
public import ArkLib.Data.Polynomial.Rojas.Producer.SafeMacaulayMap
public import ArkLib.Data.Polynomial.Rojas.SpecializationCorrectness

/-!
# Input-derived common-root data for safe Rojas maps

This module turns affine-hyperplane coverage of a computed perturbation into the exact base-field
common-root data consumed by the direct first-subresultant correctness theorem.  In particular,
the caller does not supply roots of the three specialized polynomial families separately.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.RootDataCoverage

open CPoly
open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas
open FactorizationCoverage SafeSubresultantMap SubresultantMap

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]


omit [Fintype F] [BEq F] [LawfulBEq F] in
/-- Every shift parameter prescribed by Rojas is nonzero, in both characteristic branches. -/
theorem isRojasShiftParameter_ne_zero (α : F) (hα : IsRojasShiftParameter α) : α ≠ 0 := by
  unfold IsRojasShiftParameter at hα
  split at hα
  · intro hzero
    subst α
    simp at hα
  · rw [hα]
    exact one_ne_zero

omit [Fintype F] in
private theorem cHom_injective :
    Function.Injective (CHom : F →+* CPolynomial F) := by
  intro left right hequal
  have hmapped := congrArg CPolynomial.toPoly hequal
  simpa [CPolynomial.C_toPoly, CPolynomial.toPoly_zero] using hmapped

omit [Fintype F] in
private theorem eval₂_toPoly_eval₂Polynomial
    (q : CPolynomial F) (x : CPolynomial (CPolynomial F)) :
    (q.eval₂ (CHom.comp CHom) x).toPoly =
      (q.toPoly.map CHom).comp x.toPoly := by
  rw [CPolynomial.eval₂_eq_sum_support]
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum]
  rw [Polynomial.support_map_of_injective q.toPoly cHom_injective]
  rw [CPolynomial.toPoly_sum]
  rw [CPolynomial.support_toPoly]
  apply Finset.sum_congr rfl
  intro i _
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow]
  rw [CPolynomial.coeff_toPoly]
  simp [CPolynomial.C_toPoly, Polynomial.coeff_map, CHom]

omit [Fintype F] in
private theorem natDegree_liftInTheta (q : CPolynomial F) :
    (liftInTheta q).natDegree = q.natDegree := by
  rw [CPolynomial.natDegree_toPoly]
  rw [show (liftInTheta q).toPoly = q.toPoly.map CHom by
    rw [liftInTheta, CPolynomial.eval₂_eq_sum_support]
    calc
      _ = ∑ i ∈ q.toPoly.support,
          Polynomial.C (C (q.toPoly.coeff i)) * Polynomial.X ^ i := by
        rw [CPolynomial.support_toPoly]
        rw [CPolynomial.toPoly_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow]
        rw [CPolynomial.coeff_toPoly]
        simp [CPolynomial.C_toPoly, CPolynomial.X_toPoly]
      _ = q.toPoly.map CHom := by
        conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq q.toPoly]
        rw [Polynomial.sum]
        rw [Polynomial.map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [CHom]]
  rw [Polynomial.natDegree_map_eq_of_injective cHom_injective]
  exact CPolynomial.natDegree_toPoly q |>.symm

omit [Fintype F] in
private theorem affineInner_natDegree (α : F) (hα : α ≠ 0) :
    (C (C (α + 1) * X) - C (C α) * X :
      CPolynomial (CPolynomial F)).toPoly.natDegree = 1 := by
  have hCα : C α ≠ (0 : CPolynomial F) := by
    intro hzero
    have hmapped := congrArg CPolynomial.toPoly hzero
    apply hα
    simpa [CPolynomial.C_toPoly, CPolynomial.toPoly_zero] using hmapped
  rw [CPolynomial.toPoly_sub, CPolynomial.C_toPoly,
    CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · have hright := Polynomial.natDegree_mul_le
      (p := Polynomial.C (C α)) (q := Polynomial.X)
    have hright' :
        (Polynomial.C (C α) * Polynomial.X).natDegree ≤ 1 := by
      simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] using hright
    apply Nat.le_trans (Polynomial.natDegree_sub_le _ _)
    apply max_le
    · simp only [Polynomial.natDegree_C, Nat.zero_le]
    · exact hright'
  · simp [hCα]

omit [Fintype F] in
private theorem natDegree_affineTransform (q : CPolynomial F) (α : F)
    (hα : α ≠ 0) :
    (affineTransform α q).natDegree = q.natDegree := by
  have htoPolyRingHom : Function.Injective
      (CPolynomial.toPolyRingHom : CPolynomial F →+* Polynomial F) := by
    intro left right hequal
    rw [CPolynomial.toPolyRingHom_apply,
      CPolynomial.toPolyRingHom_apply] at hequal
    exact CPolynomial.toPoly_injective hequal
  let _ : IsDomain (CPolynomial F) :=
    Function.Injective.isDomain CPolynomial.toPolyRingHom htoPolyRingHom
  rw [CPolynomial.natDegree_toPoly]
  rw [show (affineTransform α q).toPoly =
      (q.toPoly.map CHom).comp
        (C (C (α + 1) * X) - C (C α) * X).toPoly by
    exact eval₂_toPoly_eval₂Polynomial q _]
  rw [Polynomial.natDegree_comp,
    Polynomial.natDegree_map_eq_of_injective cHom_injective,
    affineInner_natDegree α hα, mul_one]
  exact CPolynomial.natDegree_toPoly q |>.symm

omit [Fact (Nat.Prime p)] [CharP F p] in
private theorem minusPolynomial_candidateFromParameter {n : ℕ}
    (perturbation : CMvPolynomial (n + 1) F) (α ε : F) (i : Fin n) :
    minusPolynomial p n (candidateFromParameter perturbation α ε) i =
      squarefreeSupport p (specializePerturbation perturbation
        (setCoordinate (momentCurve ε) i (momentCurve ε i - 1))) := by
  simp only [minusPolynomial, candidateFromParameter, specializationFamily,
    SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
  rw [List.getElem?_append_left (by simp)]
  simp

omit [Fact (Nat.Prime p)] [CharP F p] in
private theorem plusPolynomial_candidateFromParameter {n : ℕ}
    (perturbation : CMvPolynomial (n + 1) F) (α ε : F) (i : Fin n) :
    plusPolynomial p n (candidateFromParameter perturbation α ε) i =
      squarefreeSupport p (specializePerturbation perturbation
        (setCoordinate (momentCurve ε) i (momentCurve ε i + α))) := by
  simp only [plusPolynomial, candidateFromParameter, specializationFamily,
    SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
  rw [List.getElem?_append_right (by simp)]
  simp

omit [Fintype F] in
private theorem eval_eq_zero_of_linear_dvd (q : CPolynomial F) (root : F)
    (hdiv : X - C root ∣ q) : q.toPoly.eval root = 0 := by
  obtain ⟨witness, rfl⟩ := hdiv
  rw [CPolynomial.toPoly_mul, Polynomial.eval_mul]
  simp [CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]

/-- A safe moment-curve candidate receives all direct common-root data from one covered
nonsingular input root.  Positivity of the expected root count and nonzeroness of the prescribed
Rojas shift are exactly the two degree premises needed by Steps 4--5. -/
theorem rootData_candidateFromParameter {n expectedDegree : ℕ}
    {system : Fin n → CMvPolynomial n F}
    {perturbation : CMvPolynomial (n + 1) F}
    (hcoverage : CoversNonsingularAffineRoots system perturbation)
    (point : Fin n → F) (hpoint : IsNonsingularAffineRoot system point)
    (α ε : F) (hα : IsRojasShiftParameter α) (hexpected : 0 < expectedDegree)
    (hsafe : IsSafe p n expectedDegree α
      (candidateFromParameter perturbation α ε)) :
    RootData p n α (candidateFromParameter perturbation α ε)
      (RingHom.id F)
      (geometricProjection (RingHom.id F) (momentCurve ε) point) point := by
  let candidate := candidateFromParameter perturbation α ε
  let theta := geometricProjection (RingHom.id F) (momentCurve ε) point
  rcases hsafe.1 with ⟨_, heliminant, hmodulusDegree, hshifted⟩
  have hroot (u : Fin n → F) :
      (specializePerturbation perturbation u).toPoly.eval
        (geometricProjection (RingHom.id F) u point) = 0 :=
    eval_eq_zero_of_linear_dvd _ _
      (specializedLinearFactor_dvd_of_coverage hcoverage point u hpoint)
  refine
    { candidate_nonzero := heliminant
      modulus_root := ?_
      minus_degree_pos := ?_
      plus_degree_pos := ?_
      minus_root := ?_
      plus_root := ?_ }
  · apply (CPolynomial.eval₂_squarefreeSupport_eq_zero_iff
      p (RingHom.id F) theta heliminant).mpr
    simpa [candidate, theta, candidateFromParameter, specializationFamily,
      SpecializationFamily.toCandidate] using hroot (momentCurve ε)
  · intro i
    have hmember : specializePerturbation perturbation
        (setCoordinate (momentCurve ε) i (momentCurve ε i - 1)) ∈
        candidate.shiftedEliminants := by
      simp [candidate, candidateFromParameter, specializationFamily,
        SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
    have hdegree := (hshifted _ hmember).2
    rw [minusPolynomial_candidateFromParameter p, natDegree_liftInTheta, hdegree]
    exact hexpected
  · intro i
    have hmember : specializePerturbation perturbation
        (setCoordinate (momentCurve ε) i (momentCurve ε i + α)) ∈
        candidate.shiftedEliminants := by
      simp [candidate, candidateFromParameter, specializationFamily,
        SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
    have hdegree := (hshifted _ hmember).2
    rw [plusPolynomial_candidateFromParameter p,
      natDegree_affineTransform _ α (isRojasShiftParameter_ne_zero α hα), hdegree]
    exact hexpected
  · intro i
    rw [SubresultantMap.eval_specializeTheta_liftInTheta]
    rw [minusPolynomial_candidateFromParameter p]
    let shifted := specializePerturbation perturbation
      (setCoordinate (momentCurve ε) i (momentCurve ε i - 1))
    have hmember : shifted ∈ candidate.shiftedEliminants := by
      change shifted ∈
        (candidateFromParameter perturbation α ε).shiftedEliminants
      simp [shifted, candidateFromParameter, specializationFamily,
        SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
    have hnonzero := (hshifted shifted hmember).1
    apply (CPolynomial.eval₂_squarefreeSupport_eq_zero_iff p
      (RingHom.id F) (theta + point i) hnonzero).mpr
    have h := hroot
      (setCoordinate (momentCurve ε) i (momentCurve ε i - 1))
    have hprojection : geometricProjection (RingHom.id F)
        (setCoordinate (momentCurve ε) i (momentCurve ε i - 1)) point =
        theta + point i := by
      rw [geometricProjection, sum_setCoordinate]
      simp [theta, geometricProjection]
      ring
    rw [hprojection] at h
    exact h
  · intro i
    rw [SubresultantMap.eval_specializeTheta_affineTransform]
    rw [plusPolynomial_candidateFromParameter p]
    let shifted := specializePerturbation perturbation
      (setCoordinate (momentCurve ε) i (momentCurve ε i + α))
    have hmember : shifted ∈ candidate.shiftedEliminants := by
      change shifted ∈
        (candidateFromParameter perturbation α ε).shiftedEliminants
      simp [shifted, candidateFromParameter, specializationFamily,
        SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
    have hnonzero := (hshifted shifted hmember).1
    apply (CPolynomial.eval₂_squarefreeSupport_eq_zero_iff p
      (RingHom.id F) ((α + 1) * theta - α * (theta + point i)) hnonzero).mpr
    have h := hroot
      (setCoordinate (momentCurve ε) i (momentCurve ε i + α))
    have hprojection : geometricProjection (RingHom.id F)
        (setCoordinate (momentCurve ε) i (momentCurve ε i + α)) point =
        (α + 1) * theta - α * (theta + point i) := by
      rw [geometricProjection, sum_setCoordinate]
      simp [theta, geometricProjection]
      ring
    rw [hprojection] at h
    exact h


/-- Hyperplane coverage plus the executable safe guard is enough for the actual computed map to
represent a covered nonsingular base-field root. -/
theorem produce_representsPoint_of_coverage
    {n expectedDegree : ℕ} {system : Fin n → CMvPolynomial n F}
    {perturbation : CMvPolynomial (n + 1) F}
    (hcoverage : CoversNonsingularAffineRoots system perturbation)
    (point : Fin n → F) (hpoint : IsNonsingularAffineRoot system point)
    (α ε : F) (hα : IsRojasShiftParameter α) (hexpected : 0 < expectedDegree)
    (hsafe : SafeSubresultantMap.IsSafe p n expectedDegree α
      (candidateFromParameter perturbation α ε)) :
    (SubresultantMap.produce p n α
      (candidateFromParameter perturbation α ε)).RepresentsPoint
        (RingHom.id F)
        (geometricProjection (RingHom.id F) (momentCurve ε) point) point :=
  SafeSubresultantMap.IsSafe.produce_representsPoint (p := p) hsafe
    (rootData_candidateFromParameter p hcoverage point hpoint α ε hα hexpected hsafe)

variable [DecidableEq F]

/-- A successful safe system run represents each covered nonsingular base-field root at the
geometric root belonging to its actually selected moment-curve parameter. -/
theorem run_eq_ok_representsCoveredPoint
    {n expectedDegree : ℕ} {system : Fin n → CMvPolynomial n F}
    {α : F} {parameters : List F} {output : SafeMacaulayMap.Output n F}
    (hrun : SafeMacaulayMap.run p system α expectedDegree parameters = .ok output)
    (hcoverage : CoversNonsingularAffineRoots system output.perturbation.perturbation)
    (point : Fin n → F) (hpoint : IsNonsingularAffineRoot system point)
    (hα : IsRojasShiftParameter α) (hexpected : 0 < expectedDegree) :
    ∃ ε ∈ parameters,
      output.map.RepresentsPoint (RingHom.id F)
        (geometricProjection (RingHom.id F) (momentCurve ε) point) point := by
  have hcandidate := SafeMacaulayMap.run_eq_ok_candidate (p := p) hrun
  obtain ⟨ε, hε, heq⟩ := hcandidate.2.1
  refine ⟨ε, hε, ?_⟩
  rw [hcandidate.2.2, heq]
  exact produce_representsPoint_of_coverage
    p hcoverage point hpoint α ε hα hexpected (heq ▸ hcandidate.1)

end ArkLib.Rojas.Producer.RootDataCoverage
