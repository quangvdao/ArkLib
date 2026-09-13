/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Producer
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.BatchedTowerCorrectness
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract

/-!
# Executable first-order chart recovery

This file is the application seam from verified first-order Taylor charts to the existing norm
producer and tower agreement recovery.  A packet contains only the normal-form and fiber-degree
facts needed to package the producer's actual output as well-formed tower components.  Global
chart coverage is deliberately separate: it is supplied by the stage/component construction
layer, not stored in this executable adapter.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder.FirstOrderPipeline

open CompPoly CPoly Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer
open ArkLib.FiniteField.ExplicitConstruction

variable {p n k : ℕ}

/-- A constructor-produced chart with the two certificates required by the norm consumer. -/
structure ChartPacket (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)] (k : ℕ) where
  chart : ChartData (Carrier modulus) 1 k
  fiberDegree : ℕ
  normalBudget : ℕ
  normalForms : chart.NormalForms fiberDegree normalBudget
  equationDegree_lt_char : (ChartPolynomials.ofChart chart).equation.natDegree < p

/-- Convert indexed received data to the rows consumed by the first-order norm producer. -/
def receivedRows {E : Type*} {n : ℕ} (domain : Fin n ↪ E) (received : Fin n → E) :
    List (E × E) :=
  List.ofFn fun i => (domain i, received i)

/-- The reduced denominator returned by the Taylor constructor is nonzero at every regular point
of its actual chart.  This is the evaluation-level contract needed by the norm materializer; it
does not replace the stored denominator by the unreduced separant power. -/
theorem constructed_denominator_ne_zero {E L : Type} [Field E] [DecidableEq E]
    [BEq E] [LawfulBEq E] [Field L] {p k Bjet : ℕ} [CharP E p]
    (center : E) (equation : CMvPolynomial 3 E) (component : CMvPolynomial 2 E)
    (values : List E) (chart : ChartData E 1 k)
    (hv : 0 < (semanticEquation equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (hchart : construct? p 1 k Bjet center equation component values = some chart)
    (base : E →+* L) (u v : L)
    (hequation : TowerRepresentation.evalNested
      (ChartPolynomials.ofChart chart).equation base u v = 0)
    (hseparant : TowerRepresentation.evalNested
      (ChartPolynomials.ofChart chart).separant base u v ≠ 0) :
    TowerRepresentation.evalNested
      (ChartPolynomials.ofChart chart).denominator base u v ≠ 0 := by
  change TowerRepresentation.evalNested
    (ChartPolynomials.bivariatePolynomial chart.equation) base u v = 0 at hequation
  change TowerRepresentation.evalNested
    (ChartPolynomials.bivariatePolynomial chart.separant) base u v ≠ 0 at hseparant
  change TowerRepresentation.evalNested
    (ChartPolynomials.bivariatePolynomial chart.denominator) base u v ≠ 0
  have hequation' : CMvPolynomial.eval₂ base ![u, v] chart.equation = 0 :=
    (FirstOrderNormProducer.evalNested_bivariatePolynomial base u v chart.equation).symm.trans
      hequation
  have hseparant' : CMvPolynomial.eval₂ base ![u, v] chart.separant ≠ 0 := by
    intro hz
    exact hseparant
      ((FirstOrderNormProducer.evalNested_bivariatePolynomial base u v chart.separant).trans hz)
  have hglobal := construct?_cleared_global p Bjet center equation component values hv hB
    chart hchart base ![u, v] hequation'
  have hgeometry := construct?_geometry p 1 k Bjet center equation component values chart hchart
  have hdenominator : CMvPolynomial.eval₂ base ![u, v] chart.denominator =
      CMvPolynomial.eval₂ base ![u, v] chart.separant ^ (2 * k) := by
    rw [hglobal.1]
    have hstoredPow : toCMvPolynomial
        (initialJetSeparant center (semanticEquation equation) ^ (2 * k)) =
        toCMvPolynomial (initialJetSeparant center (semanticEquation equation)) ^ (2 * k) := by
      exact (CPoly.polyRingEquiv (n := 2) (R := E)).symm.map_pow
        (initialJetSeparant center (semanticEquation equation)) (2 * k)
    rw [hstoredPow]
    have hprojectPow (P : CMvPolynomial 2 E) (m : ℕ) :
        Geometry.projectPolynomial chart.projection (P ^ m) =
          Geometry.projectPolynomial chart.projection P ^ m := by
      rw [Geometry.projectPolynomial, Geometry.projectPolynomial,
        CPoly.CMvPolynomial.bind₁_eq_aeval, CPoly.CMvPolynomial.bind₁_eq_aeval]
      simpa [CPoly.CMvPolynomial.aeval] using
        (CMvPolynomial.eval₂Hom (algebraMap E (CMvPolynomial 2 E))
          (Geometry.linearCoordinate chart.projection)).map_pow P m
    rw [hprojectPow, ← initialSeparant_semantics, toCMvPolynomial_fromCMvPolynomial,
      ← hgeometry.2.2.2.2.2.2.2]
    rw [show CMvPolynomial.eval₂ base ![u, v]
        (chart.separant ^ (2 * k)) =
        CMvPolynomial.eval₂ base ![u, v]
          chart.separant ^ (2 * k) by
      exact (CMvPolynomial.eval₂Hom base ![u, v]).map_pow _ _]
  intro hz
  have hz' : CMvPolynomial.eval₂ base ![u, v] chart.denominator = 0 :=
    (FirstOrderNormProducer.evalNested_bivariatePolynomial base u v chart.denominator).symm.trans hz
  rw [hdenominator] at hz'
  exact pow_ne_zero _ hseparant' hz'

/-- Run the actual norm producer for one certified chart and package every emitted tower with its
proved well-formedness.  The attached membership proof is erased by execution. -/
def packetFamilies (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext (Carrier modulus))
    (D : CPolynomial.ModContext (Carrier modulus))
    {n k : ℕ} (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (A : ℕ) (packet : ChartPacket p modulus k) :
    List (AgreementRecovery.Tower.Component (Carrier modulus) k) :=
  (firstOrderNormCandidates p modulus M D A packet.chart
      (receivedRows domain received)).attach.map fun candidate =>
    ⟨candidate.1, firstOrderNormCandidates_wellFormed p modulus M D A packet.chart
      (receivedRows domain received) packet.normalForms packet.equationDegree_lt_char
      candidate.1 candidate.2⟩

/-- Flatten the real candidate families from every successful first-order chart. -/
def candidateFamilies (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext (Carrier modulus))
    (D : CPolynomial.ModContext (Carrier modulus))
    {n k : ℕ} (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (A : ℕ) (packets : List (ChartPacket p modulus k)) :
    List (AgreementRecovery.Tower.Component (Carrier modulus) k) :=
  packets.flatMap (packetFamilies p modulus M D domain received A)

/-- Execute tower splitting, interpolation, final degree/agreement checks and deduplication on the
actual first-order norm candidates. -/
def decode (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext (Carrier modulus))
    (D : CPolynomial.ModContext (Carrier modulus))
    {n k : ℕ} (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (A : ℕ) (packets : List (ChartPacket p modulus k)) : List (List (Carrier modulus)) :=
  AgreementRecovery.BatchedTower.recoverAgreement M D (RingHom.id _) domain received k A
    (candidateFamilies p modulus M D domain received A packets)

/-- Every public first-order output passes the requested width, degree and full-agreement checks,
independently of the still-separate global component coverage proof. -/
theorem mem_decode_properties (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext (Carrier modulus))
    (D : CPolynomial.ModContext (Carrier modulus))
    {n k : ℕ} (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (A : ℕ) (packets : List (ChartPacket p modulus k)) (cs : List (Carrier modulus))
    (hcs : cs ∈ decode p modulus M D domain received A packets) :
    cs.length = k ∧ (Polynomial.JetHornerMachine.coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree
        (evalOnPoints domain (Polynomial.JetHornerMachine.coefficientPolynomial cs)) received := by
  exact AgreementRecovery.BatchedTower.mem_recoverAgreement_properties
    M D (RingHom.id _) domain received k A _ cs hcs

/-- Once the stage/component layer proves coverage of these actual packaged towers, the same
executed decoder satisfies the repository's complete duplicate-free output contract. -/
theorem decode_exact_of_coverage (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext (Carrier modulus))
    (D : CPolynomial.ModContext (Carrier modulus))
    {n k : ℕ} (domain : Fin n ↪ Carrier modulus) (received : Fin n → Carrier modulus)
    (A : ℕ) (hAk : k ≤ A) (packets : List (ChartPacket p modulus k))
    (hcover : ∀ message : (Carrier modulus)[X], message.degree < k →
      A ≤ Code.agree (evalOnPoints domain message) received →
        AgreementRecovery.Tower.RepresentedBy (RingHom.id _) (RingHom.id _) k
          (candidateFamilies p modulus M D domain received A packets) message) :
    ExactOutput domain received k A (decode p modulus M D domain received A packets) := by
  exact AgreementRecovery.BatchedTower.recoverAgreement_exact_of_coverage
    M D (RingHom.id _) (RingHom.id _) domain received k A hAk _ hcover

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder.FirstOrderPipeline
