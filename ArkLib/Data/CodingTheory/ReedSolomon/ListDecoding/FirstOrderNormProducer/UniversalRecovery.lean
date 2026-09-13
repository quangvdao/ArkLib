/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Producer
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerEmbedding
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder

/-!
# Recovery for universal first-order components

If component descent marks at least the agreement threshold's worth of residuals as universal,
the multiplicity threshold on that component is zero.  This is a success case: the corresponding
message already agrees at enough distinct received positions.  We recover it with executable
position-subset interpolation and embed its constant coefficients into the common tower format.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPolynomial Polynomial Polynomial.JetHornerMachine FullSquarefreeDecomposition.Driver
open ArkLib.FiniteField.ExplicitConstruction

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

omit [BEq F] [LawfulBEq F] in
private theorem coefficientPolynomial_map {K : Type*} [Field K]
    (base : F →+* K) (cs : List F) :
    Polynomial.JetHornerMachine.coefficientPolynomial (cs.map base) =
      (Polynomial.JetHornerMachine.coefficientPolynomial cs).map base := by
  induction cs with
  | nil => simp [Polynomial.JetHornerMachine.coefficientPolynomial]
  | cons c cs ih => simp [Polynomial.JetHornerMachine.coefficientPolynomial_cons, ih]

/-- Regard an ordinary coefficient vector as the constant univariate family indexed by `U = 0`. -/
def constantRepresentation (cs : List F) : FiniteRepresentation F where
  modulus := CPolynomial.X
  coefficients := cs.map CPolynomial.C

/-- Embed an ordinary coefficient vector into the common tower format, with the single point
`(U,V) = (0,0)`. -/
def constantTower (cs : List F) : TowerRepresentation (F := F) :=
  TowerRepresentation.ofUnivariate (constantRepresentation cs)

/-- Fixed-width coefficient vectors give well-formed constant towers. -/
theorem constantTower_wellFormed (cs : List F) {k : ℕ} (hlength : cs.length = k) :
    (constantTower cs).WellFormed k := by
  apply TowerRepresentation.ofUnivariate_wellFormed
  · refine ⟨?_, ?_, by simp [constantRepresentation, hlength], ?_⟩
    · rw [constantRepresentation, CPolynomial.X_toPoly]
      exact Polynomial.monic_X
    · rw [constantRepresentation, CPolynomial.X_toPoly]
      exact Polynomial.irreducible_X.squarefree
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      change (CPolynomial.C a).toPoly.degree < CPolynomial.X.toPoly.degree
      rw [CPolynomial.C_toPoly, CPolynomial.X_toPoly, Polynomial.degree_X]
      exact Polynomial.degree_C_le.trans_lt (by norm_num)
  · simp [constantRepresentation, CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]

/-- The constant tower has its canonical point over every coefficient-field extension. -/
theorem constantTower_point {K : Type*} [Field K] (base : F →+* K) (cs : List F) :
    (constantTower cs).Point base 0 0 := by
  rw [constantTower, TowerRepresentation.ofUnivariate_point_iff]
  simp [constantRepresentation, CPolynomial.X_toPoly]

/-- Specializing the constant tower gives the base change of its coefficient polynomial. -/
theorem constantTower_specialize {K : Type*} [Field K] (base : F →+* K) (cs : List F) :
    (constantTower cs).specialize base 0 0 = (coefficientPolynomial cs).map base := by
  rw [constantTower, TowerRepresentation.ofUnivariate_specialize]
  simp [constantRepresentation, FiniteRepresentation.specialize, List.map_map,
    Function.comp_def, CPolynomial.C_toPoly, coefficientPolynomial_map]

/-- Ordinary interpolation candidates represented as constant towers. -/
def universalRecoveryCandidates [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) : List (TowerRepresentation (F := F)) :=
  (PositionSubsetDecoder.run domain received k A).map constantTower

/-- Every degree-bounded base-field polynomial with enough agreements occurs as a constant
tower in the executable interpolation recovery output. -/
theorem mem_universalRecoveryCandidates_of_agreement {n k A : ℕ}
    [DecidableEq F] (domain : Fin n ↪ F) (received : Fin n → F) (hkA : k ≤ A)
    (P : F[X]) (hdegree : P.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain P) received) :
    ∃ candidate ∈ universalRecoveryCandidates domain received k A,
      ∀ {K : Type*} [Field K] (base : F →+* K),
        candidate.Point base 0 0 ∧ candidate.specialize base 0 0 = P.map base := by
  have hP := ((PositionSubsetDecoder.run_exact domain received k A hkA).2.2.1 P).2
    ⟨hdegree, hagreement⟩
  obtain ⟨cs, hcs, hcsP⟩ := List.mem_map.mp hP
  refine ⟨constantTower cs, List.mem_map.mpr ⟨cs, hcs, rfl⟩, ?_⟩
  intro K _ base
  refine ⟨constantTower_point base cs, ?_⟩
  rw [constantTower_specialize, hcsP]

/-- Every interpolation recovery candidate satisfies the common tower representation contract. -/
theorem universalRecoveryCandidates_wellFormed {n k A : ℕ} [DecidableEq F]
    (domain : Fin n ↪ F) (received : Fin n → F) (hkA : k ≤ A)
    (candidate : TowerRepresentation (F := F))
    (hcandidate : candidate ∈ universalRecoveryCandidates domain received k A) :
    candidate.WellFormed k := by
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hcandidate
  apply constantTower_wellFormed
  exact ((PositionSubsetDecoder.run_exact domain received k A hkA).2.2.2 cs).mp hcs |>.1

/-- Materialize the indexed received word in the format consumed by chart preparation. -/
def indexedReceived {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) : List (F × F) :=
  List.ofFn fun i => (domain i, received i)

/-- Whether actual component descent found a component with at least `A` universal labels. -/
def needsUniversalRecovery {n k A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData F 1 k)
    (domain : Fin n ↪ F) (received : Fin n → F) : Bool :=
  ((prepare chart (indexedReceived domain received)).blocks.any fun block =>
    decide (A ≤ block.component.universal.length))

/-- A large actual universal block enables the interpolation recovery branch. -/
theorem needsUniversalRecovery_eq_true_of_block {n k A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData F 1 k)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (block : ComputedBlock F)
    (hblock : block ∈ (prepare chart (indexedReceived domain received)).blocks)
    (huniversal : A ≤ block.component.universal.length) :
    needsUniversalRecovery (A := A) chart domain received = true := by
  apply List.any_eq_true.mpr
  exact ⟨block, hblock, by simp [huniversal]⟩

/-- The complete producer runs determinant norms on positive-threshold components and activates
ordinary interpolation precisely when actual descent exposes a large universal component. -/
def firstOrderNormCandidatesWithRecovery
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {n k : ℕ} (A : ℕ)
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus) :
    List (TowerRepresentation (F := Carrier modulus)) :=
  firstOrderNormCandidates p modulus M D A chart (indexedReceived domain received) ++
    if needsUniversalRecovery (A := A) chart domain received then
      universalRecoveryCandidates domain received k A
    else []

/-- A wanted base-field polynomial is covered whenever actual descent exposes a component whose
universal label count reaches the agreement threshold. -/
theorem firstOrderNormCandidatesWithRecovery_complete_of_universal_block
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {n k A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (hkA : k ≤ A)
    (block : ComputedBlock (Carrier modulus))
    (hblock : block ∈ (prepare chart (indexedReceived domain received)).blocks)
    (huniversal : A ≤ block.component.universal.length)
    (P : (Carrier modulus)[X]) (hdegree : P.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain P) received) :
    ∃ candidate ∈ firstOrderNormCandidatesWithRecovery
        p modulus M D A chart domain received,
      ∀ {K : Type*} [Field K] (base : Carrier modulus →+* K),
        candidate.Point base 0 0 ∧ candidate.specialize base 0 0 = P.map base := by
  obtain ⟨candidate, hcandidate, hrepresents⟩ :=
    mem_universalRecoveryCandidates_of_agreement domain received hkA P hdegree hagreement
  refine ⟨candidate, ?_, hrepresents⟩
  simp [firstOrderNormCandidatesWithRecovery,
    needsUniversalRecovery_eq_true_of_block chart domain received block hblock huniversal,
    hcandidate]

/-- Component-local coverage with both threshold cases.  A positive component threshold uses
the determinant-norm path at the supplied chart point.  A large universal label set activates
interpolation and represents the same base-field message at the constant tower's point. -/
theorem firstOrderNormCandidatesWithRecovery_complete_of_block
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {n k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (Polynomial.FunctionFieldAlgorithms.ClearDenominators.valueGlobal
        (prepare chart (indexedReceived domain received)).chartPolynomials.equation))
    (hkA : k ≤ A)
    (block : ComputedBlock (Carrier modulus))
    (hblock : block ∈ (prepare chart (indexedReceived domain received)).blocks)
    (positions : Finset (Fin
      (prepare chart (indexedReceived domain received)).agreements.length))
    (hpositions : A ≤ positions.card)
    (hdegree : (prepare chart
      (indexedReceived domain received)).chartPolynomials.equation.natDegree < p)
    (hdenominator : DenominatorRegular chart (indexedReceived domain received))
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hcomponent : Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt
      base u v block.component.modulus = 0)
    (hresidual : ∀ i ∈ positions,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
        (prepare chart (indexedReceived domain received)).agreements[i] = 0)
    (hseparant : TowerRepresentation.evalNested
      (prepare chart (indexedReceived domain received)).chartPolynomials.separant
        base u v ≠ 0)
    (P : (Carrier modulus)[X]) (hPdegree : P.degree < k)
    (hPagreement : A ≤ Code.agree (evalOnPoints domain P) received)
    (htarget :
      Polynomial.JetHornerMachine.coefficientPolynomial
        ((List.ofFn
          (prepare chart (indexedReceived domain received)).chartPolynomials.numerators).map
            fun numerator => TowerRepresentation.evalNested numerator base u v /
              TowerRepresentation.evalNested
                (prepare chart
                  (indexedReceived domain received)).chartPolynomials.denominator base u v) =
        P.map base) :
    ∃ candidate ∈ firstOrderNormCandidatesWithRecovery
        p modulus M D A chart domain received,
      ∃ x y : K, candidate.Point base x y ∧
        candidate.specialize base x y = P.map base := by
  by_cases huniversal : A ≤ block.component.universal.length
  · obtain ⟨candidate, hcandidate, hrepresents⟩ :=
      firstOrderNormCandidatesWithRecovery_complete_of_universal_block
        p modulus M D chart domain received hkA block hblock huniversal
          P hPdegree hPagreement
    exact ⟨candidate, hcandidate, 0, 0, hrepresents base⟩
  · have huniversalLt : block.component.universal.length < A := Nat.lt_of_not_ge huniversal
    obtain ⟨candidate, hcandidate, hpoint, hspecialize⟩ :=
      produceComputedBlock_point_complete_of_universal_lt
        p modulus M D chart (indexedReceived domain received) hnormal hgenericSquarefree
          block hblock huniversalLt positions hpositions hdegree hdenominator
          base u v hcomponent hresidual hseparant
    refine ⟨candidate, ?_, u, v, hpoint, hspecialize.trans htarget⟩
    simp only [firstOrderNormCandidatesWithRecovery, List.mem_append]
    exact Or.inl (by
      simp only [firstOrderNormCandidates, List.mem_flatMap]
      exact ⟨block, hblock, hcandidate⟩)

/-- Every candidate emitted by the producer with universal recovery satisfies the common tower
contract.  The interpolation branch gets its width from the exact position-subset decoder. -/
theorem firstOrderNormCandidatesWithRecovery_wellFormed
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {n k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (hnormal : chart.NormalForms b L)
    (hdegree : (ChartPolynomials.ofChart chart).equation.natDegree < p)
    (hkA : k ≤ A)
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈ firstOrderNormCandidatesWithRecovery
      p modulus M D A chart domain received) :
    candidate.WellFormed k := by
  unfold firstOrderNormCandidatesWithRecovery at hcandidate
  rw [List.mem_append] at hcandidate
  rcases hcandidate with hnorm | hrecovery
  · exact firstOrderNormCandidates_wellFormed p modulus M D A chart
      (indexedReceived domain received) hnormal hdegree candidate hnorm
  · split at hrecovery
    · exact universalRecoveryCandidates_wellFormed domain received hkA candidate hrecovery
    · simp at hrecovery

end ReedSolomon.ListDecoding.FirstOrderNormProducer
