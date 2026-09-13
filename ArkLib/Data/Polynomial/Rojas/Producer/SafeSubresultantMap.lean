/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ModularInverse
public import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantCorrectness

/-!
# Denominator-safe Rojas specialization

This module strengthens the executable Step 0--3 support-degree guard with a computed coprimality
test between the Step 4--5 common denominator and its modulus.  A passing candidate therefore has
a denominator that cannot vanish at any geometric root of the modulus, over any field extension.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.SafeSubresultantMap

open CPoly
open CompPoly CompPoly.CPolynomial
open ArkLib.UnivariateRepresentation

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Proof-facing safe-candidate contract: the existing support-degree guard and coprimality of the
actually produced denominator and modulus. -/
def IsSafe (dimension expectedDegree : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) : Prop :=
  HasExpectedSupportDegree p dimension expectedDegree candidate ∧
    IsCoprime
      (SubresultantMap.commonDenominator p dimension α candidate).toPoly
      (SubresultantMap.modulus p candidate).toPoly

/-- Executable safe-candidate guard.  `inverseMod?` computes a normalized extended gcd, so this
does not consume a supplied coprimality certificate. -/
def isSafe (dimension expectedDegree : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) : Bool :=
  hasExpectedSupportDegree p dimension expectedDegree candidate &&
    (inverseMod?
      (SubresultantMap.commonDenominator p dimension α candidate)
      (SubresultantMap.modulus p candidate)).isSome

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The executable guard is exactly the support-and-coprimality proposition. -/
theorem isSafe_eq_true_iff (dimension expectedDegree : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) :
    isSafe p dimension expectedDegree α candidate = true ↔
      IsSafe p dimension expectedDegree α candidate := by
  rw [isSafe, Bool.and_eq_true, hasExpectedSupportDegree_eq_true_iff]
  unfold IsSafe
  rw [Option.isSome_iff_exists, inverseMod_exists_iff_coprime]

/-- Select the first safe candidate from an explicit candidate list. -/
def selectSafe? (dimension expectedDegree : ℕ) (α : F)
    (candidates : List (SpecializationCandidate (F := F))) :
    Option (SpecializationCandidate (F := F)) :=
  candidates.find? (isSafe p dimension expectedDegree α)

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- First-success soundness for the safe candidate scan. -/
theorem selectSafe?_sound
    {dimension expectedDegree : ℕ} {α : F}
    {candidates : List (SpecializationCandidate (F := F))}
    {selected : SpecializationCandidate (F := F)}
    (hselected : selectSafe? p dimension expectedDegree α candidates = some selected) :
    IsSafe p dimension expectedDegree α selected ∧ selected ∈ candidates := by
  rw [selectSafe?, List.find?_eq_some_iff_getElem] at hselected
  obtain ⟨hvalid, i, hi, hget, _⟩ := hselected
  refine ⟨(isSafe_eq_true_iff p dimension expectedDegree α selected).mp hvalid, ?_⟩
  exact hget ▸ List.getElem_mem hi

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The safe scan succeeds exactly when the list contains a passing candidate. -/
theorem selectSafe?_exists_iff (dimension expectedDegree : ℕ) (α : F)
    (candidates : List (SpecializationCandidate (F := F))) :
    (∃ selected, selectSafe? p dimension expectedDegree α candidates = some selected) ↔
      ∃ candidate ∈ candidates, IsSafe p dimension expectedDegree α candidate := by
  rw [← Option.isSome_iff_exists, selectSafe?, List.find?_isSome]
  constructor
  · rintro ⟨candidate, hmem, hvalid⟩
    exact ⟨candidate, hmem,
      (isSafe_eq_true_iff p dimension expectedDegree α candidate).mp hvalid⟩
  · rintro ⟨candidate, hmem, hvalid⟩
    exact ⟨candidate, hmem,
      (isSafe_eq_true_iff p dimension expectedDegree α candidate).mpr hvalid⟩

/-- Compute all moment-curve candidates and select the first one whose produced rational map is
denominator-safe. -/
def selectSafeParameter? {dimension : ℕ} (perturbation : CMvPolynomial (dimension + 1) F)
    (α : F) (expectedDegree : ℕ) (parameters : List F) :
    Option (SpecializationCandidate (F := F)) :=
  selectSafe? p dimension expectedDegree α
    (candidatesFromParameters perturbation α parameters)

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- A successful parameter scan returns an actual moment-curve specialization and proves both
parts of its safe guard. -/
theorem selectSafeParameter?_sound
    {dimension : ℕ} {perturbation : CMvPolynomial (dimension + 1) F}
    {α : F} {expectedDegree : ℕ} {parameters : List F}
    {selected : SpecializationCandidate (F := F)}
    (hselected : selectSafeParameter? p perturbation α expectedDegree parameters = some selected) :
    IsSafe p dimension expectedDegree α selected ∧
      ∃ ε ∈ parameters, selected = candidateFromParameter perturbation α ε := by
  have hsound := selectSafe?_sound (p := p) hselected
  refine ⟨hsound.1, ?_⟩
  obtain ⟨ε, hε, heq⟩ := List.mem_map.mp hsound.2
  exact ⟨ε, hε, heq.symm⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The parameter scan succeeds exactly when one supplied parameter computes a safe candidate. -/
theorem selectSafeParameter?_exists_iff {dimension : ℕ}
    (perturbation : CMvPolynomial (dimension + 1) F) (α : F)
    (expectedDegree : ℕ) (parameters : List F) :
    (∃ selected,
      selectSafeParameter? p perturbation α expectedDegree parameters = some selected) ↔
      ∃ ε ∈ parameters,
        IsSafe p dimension expectedDegree α
          (candidateFromParameter perturbation α ε) := by
  rw [selectSafeParameter?, selectSafe?_exists_iff]
  constructor
  · rintro ⟨candidate, hcandidate, hsafe⟩
    obtain ⟨ε, hε, rfl⟩ := List.mem_map.mp hcandidate
    exact ⟨ε, hε, hsafe⟩
  · rintro ⟨ε, hε, hsafe⟩
    exact ⟨candidateFromParameter perturbation α ε,
      List.mem_map.mpr ⟨ε, hε, rfl⟩, hsafe⟩

/-- Output of the denominator-safe Steps 0--5 producer. -/
structure Output (dimension : ℕ) (F : Type*) [Field F] where
  candidate : SpecializationCandidate (F := F)
  map : MapData (F := F)

/-- Scan moment-curve specializations and construct a coordinate map only from a candidate whose
denominator has passed the computed coprimality test. -/
def run {dimension : ℕ} (perturbation : CMvPolynomial (dimension + 1) F)
    (α : F) (expectedDegree : ℕ) (parameters : List F) :
    Option (Output dimension F) :=
  match selectSafeParameter? p perturbation α expectedDegree parameters with
  | none => none
  | some candidate => some
      { candidate
        map := SubresultantMap.produce p dimension α candidate }

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- Successful composed output exposes the exact selected candidate, map, and safe contract. -/
theorem run_eq_some_sound
    {dimension : ℕ} {perturbation : CMvPolynomial (dimension + 1) F}
    {α : F} {expectedDegree : ℕ} {parameters : List F}
    {output : Output dimension F}
    (hrun : run p perturbation α expectedDegree parameters = some output) :
    IsSafe p dimension expectedDegree α output.candidate ∧
      (∃ ε ∈ parameters,
        output.candidate = candidateFromParameter perturbation α ε) ∧
      output.map = SubresultantMap.produce p dimension α output.candidate := by
  simp only [run] at hrun
  split at hrun <;> rename_i hcandidate
  · contradiction
  · simp only [Option.some.injEq] at hrun
    cases hrun
    have hsound := selectSafeParameter?_sound (p := p) hcandidate
    exact ⟨hsound.1, hsound.2, rfl⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- Coprimality guarantees denominator nonvanishing at every modulus root over any field
extension.  Algebraic closedness is unnecessary. -/
theorem IsSafe.denominator_eval₂_ne_zero
    {dimension expectedDegree : ℕ} {α : F}
    {candidate : SpecializationCandidate (F := F)}
    (hsafe : IsSafe p dimension expectedDegree α candidate)
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (hroot : (SubresultantMap.modulus p candidate).toPoly.eval₂ ι θ = 0) :
    (SubresultantMap.commonDenominator p dimension α candidate).toPoly.eval₂ ι θ ≠ 0 := by
  intro hdenominator
  have hmapped := hsafe.2.map (Polynomial.eval₂RingHom ι θ)
  change IsCoprime
    ((SubresultantMap.commonDenominator p dimension α candidate).toPoly.eval₂ ι θ)
    ((SubresultantMap.modulus p candidate).toPoly.eval₂ ι θ) at hmapped
  rw [hdenominator, hroot] at hmapped
  exact not_isCoprime_zero_zero hmapped

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The denominator of every successful composed output is nonzero at every root of its modulus
over every field extension. -/
theorem run_eq_some_denominator_eval₂_ne_zero
    {dimension : ℕ} {perturbation : CMvPolynomial (dimension + 1) F}
    {α : F} {expectedDegree : ℕ} {parameters : List F}
    {output : Output dimension F}
    (hrun : run p perturbation α expectedDegree parameters = some output)
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (hroot : output.map.modulus.toPoly.eval₂ ι θ = 0) :
    output.map.denominator.toPoly.eval₂ ι θ ≠ 0 := by
  have hsound := run_eq_some_sound (p := p) hrun
  rw [hsound.2.2] at hroot ⊢
  change (SubresultantMap.modulus p output.candidate).toPoly.eval₂ ι θ = 0 at hroot
  change (SubresultantMap.commonDenominator p dimension α output.candidate).toPoly.eval₂
    ι θ ≠ 0
  exact IsSafe.denominator_eval₂_ne_zero (p := p) hsound.1 ι θ hroot

noncomputable section

variable {K : Type*} [Field K]

/-- Common-root data for the direct first-subresultant theorem, before denominator safety is
established.  All fields concern the actual specialized polynomials. -/
structure RootData (dimension : ℕ) (α : F)
    (candidate : SpecializationCandidate (F := F)) (ι : F →+* K)
    (θ : K) (point : Fin dimension → K) : Prop where
  candidate_nonzero : candidate.eliminant ≠ 0
  modulus_root : (SubresultantMap.modulus p candidate).toPoly.eval₂ ι θ = 0
  minus_degree_pos : ∀ i : Fin dimension,
    0 < (SubresultantMap.liftInTheta
      (SubresultantMap.minusPolynomial p dimension candidate i)).natDegree
  plus_degree_pos : ∀ i : Fin dimension,
    0 < (SubresultantMap.affineTransform α
      (SubresultantMap.plusPolynomial p dimension candidate i)).natDegree
  minus_root : ∀ i : Fin dimension,
    (SubresultantMap.specializeTheta ι θ
      (SubresultantMap.liftInTheta
        (SubresultantMap.minusPolynomial p dimension candidate i))).eval
      (θ + point i) = 0
  plus_root : ∀ i : Fin dimension,
    (SubresultantMap.specializeTheta ι θ
      (SubresultantMap.affineTransform α
        (SubresultantMap.plusPolynomial p dimension candidate i))).eval
      (θ + point i) = 0

/-- The computed global coprimality guard supplies every local denominator premise required by
the direct common-root correctness theorem. -/
theorem IsSafe.commonRootsAtPoint
    {dimension expectedDegree : ℕ} {α : F}
    {candidate : SpecializationCandidate (F := F)}
    (hsafe : IsSafe p dimension expectedDegree α candidate)
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (roots : RootData p dimension α candidate ι θ point) :
    SubresultantMap.CommonRootsAtPoint p dimension α candidate ι θ point := by
  classical
  have hcommon : SubresultantMap.coefficientEval ι θ
      (SubresultantMap.commonDenominator p dimension α candidate) ≠ 0 := by
    rw [SubresultantMap.coefficientEval_apply]
    exact IsSafe.denominator_eval₂_ne_zero (p := p) hsafe ι θ roots.modulus_root
  rw [SubresultantMap.coefficientEval_commonDenominator (p := p)
    dimension α candidate ι θ roots.candidate_nonzero roots.modulus_root] at hcommon
  refine
    { candidate_nonzero := roots.candidate_nonzero
      modulus_root := roots.modulus_root
      denominator_ne_zero := ?_
      minus_degree_pos := roots.minus_degree_pos
      plus_degree_pos := roots.plus_degree_pos
      minus_root := roots.minus_root
      plus_root := roots.plus_root }
  exact fun i ↦ Finset.prod_ne_zero_iff.mp hcommon i (Finset.mem_univ i)

/-- A safe candidate represents every point satisfying the actual specialized common-root data;
no gcd association or denominator certificate is supplied by the caller. -/
theorem IsSafe.produce_representsPoint
    {dimension expectedDegree : ℕ} {α : F}
    {candidate : SpecializationCandidate (F := F)}
    (hsafe : IsSafe p dimension expectedDegree α candidate)
    {ι : F →+* K} {θ : K} {point : Fin dimension → K}
    (roots : RootData p dimension α candidate ι θ point) :
    (SubresultantMap.produce p dimension α candidate).RepresentsPoint ι θ point :=
  SubresultantMap.produce_representsPoint_of_commonRoots
    (p := p) (IsSafe.commonRootsAtPoint (p := p) hsafe roots)

end

end ArkLib.Rojas.Producer.SafeSubresultantMap
