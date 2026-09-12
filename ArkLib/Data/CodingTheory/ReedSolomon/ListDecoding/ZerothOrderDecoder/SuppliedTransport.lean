/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedAdapter
public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedCenters
public import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.Basic
import CompPoly.ToMathlib.MvPolynomial.Equiv

/-!
# Transporting the zeroth-order decoder to supplied quadratic center fields

The supplied-center dispatcher may return centers in the presented field or in one of two
computed quadratic extensions.  This file executes the same regular-fiber decoder in all three
successful branches.  Coefficients of the normalized equation and its obstruction are mapped by
the branch embedding, while agreement recovery continues to interpolate and return coefficients
in the original supplied field.

The executable function takes no center list, good-center witness, capacity proof, or coefficient
recovery callback.  Capacity failure remains an explicit `none` result at this low-level boundary.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport

open CompPoly Polynomial
open ArkLib ConfluentAlgebra
open ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms
open ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open ReedSolomon.ListDecoding.ZerothOrderDecoder

variable {F E : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E]

/-- Executable coefficient transport for a stored bivariate polynomial. -/
def mapBivariate (embedding : F →+* E) (T : CBivariate F) : CBivariate E :=
  mapCoefficients (mapCoefficientsHom embedding) T

/-- The regular equation after transporting every stored coefficient. -/
def mapRegularEquation (embedding : F →+* E) (T : CBivariate F) : CPoly.CMvPolynomial 2 E :=
  CBivariate.toOrdinaryCMv (mapBivariate embedding T)

/-- The obstruction polynomial transported to the field in which centers are enumerated. -/
def mapObstruction (embedding : F →+* E) (obstruction : CPolynomial F) : CPolynomial E :=
  mapCoefficients embedding obstruction

/-- The ordinary `[X,Y]` conversion preserves the stored outer (`Y`) degree. -/
theorem degreeOf_one_toOrdinaryCMv (T : CBivariate F) :
    (CBivariate.toOrdinaryCMv T).degreeOf 1 = T.natDegree := by
  have hdegree := congrFun (CPoly.degreeOf_equiv (S := F)
    (p := CBivariate.toOrdinaryCMv T)) (1 : Fin 2)
  rw [hdegree, MvPolynomial.degreeOf_eq_sup]
  simp only [CBivariate.toOrdinaryCMv, CPoly.CMvPolynomial.fromCMvPolynomial_sum,
    CPoly.CMvPolynomial.fromCMvPolynomial_monomial,
    CBivariate.toFinsupp_ordinaryMonomial]
  let S : MvPolynomial (Fin 2) F :=
    ∑ j ∈ T.supportY,
      ∑ i ∈ (T.val.coeff j).support,
        MvPolynomial.monomial
          (Finsupp.single 0 i + Finsupp.single 1 j)
          (CPolynomial.coeff (T.val.coeff j) i)
  change S.support.sup (fun m => m 1) = T.natDegree
  have hcoeff (i j : ℕ) :
      MvPolynomial.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) S =
        CPolynomial.coeff (T.val.coeff j) i := by
    have heq (i' j' : ℕ) :
        Finsupp.single (0 : Fin 2) i' + Finsupp.single 1 j' =
          Finsupp.single 0 i + Finsupp.single 1 j ↔ i' = i ∧ j' = j := by
      constructor
      · intro h
        constructor
        · have h0 := congrArg (fun s => s (0 : Fin 2)) h
          simpa using h0
        · have h1 := congrArg (fun s => s (1 : Fin 2)) h
          simpa using h1
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [S, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, heq]
    by_cases hj : j ∈ T.supportY
    · rw [Finset.sum_eq_single j]
      · by_cases hi : i ∈ (T.val.coeff j).support
        · rw [Finset.sum_eq_single i]
          · simp
          · intro b hb hbi
            simp [hbi]
          · intro hnot
            exact (hnot hi).elim
        · rw [Finset.sum_eq_zero]
          · symm
            simpa [CPolynomial.mem_support_iff] using hi
          · intro b hb
            simp [show b ≠ i from fun h => hi (h ▸ hb)]
      · intro b hb hbj
        apply Finset.sum_eq_zero
        intro a ha
        simp [hbj]
      · intro hnot
        exact (hnot hj).elim
    · rw [Finset.sum_eq_zero]
      · have hcoefficient : T.val.coeff j = 0 := by
          simpa [CBivariate.supportY, CPolynomial.mem_support_iff] using hj
        rw [hcoefficient, CPolynomial.coeff_zero]
      · intro b hb
        apply Finset.sum_eq_zero
        intro a ha
        simp [show b ≠ j from fun h => hj (h ▸ hb)]
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro exponent hexponent
    have houter : exponent ∈ T.supportY.biUnion fun j =>
        (∑ i ∈ (T.val.coeff j).support,
          MvPolynomial.monomial
            (Finsupp.single 0 i + Finsupp.single 1 j)
            (CPolynomial.coeff (T.val.coeff j) i)).support := by
      exact (MvPolynomial.support_sum (s := T.supportY)
        (f := fun j => ∑ i ∈ (T.val.coeff j).support,
          MvPolynomial.monomial
            (Finsupp.single 0 i + Finsupp.single 1 j)
            (CPolynomial.coeff (T.val.coeff j) i))) (by simpa [S] using hexponent)
    rcases Finset.mem_biUnion.mp houter with ⟨j, hj, hinner⟩
    have hterms : exponent ∈ (T.val.coeff j).support.biUnion fun i =>
        (MvPolynomial.monomial
          (Finsupp.single 0 i + Finsupp.single 1 j)
          (CPolynomial.coeff (T.val.coeff j) i)).support :=
      (MvPolynomial.support_sum (s := (T.val.coeff j).support)
        (f := fun i => MvPolynomial.monomial
          (Finsupp.single 0 i + Finsupp.single 1 j)
          (CPolynomial.coeff (T.val.coeff j) i))) hinner
    rcases Finset.mem_biUnion.mp hterms with ⟨i, hi, hmonomial⟩
    have hcoefficient : CPolynomial.coeff (T.val.coeff j) i ≠ 0 :=
      (CPolynomial.mem_support_iff _ _).mp hi
    have heq : exponent = Finsupp.single 0 i + Finsupp.single 1 j := by
      rw [MvPolynomial.support_monomial, if_neg hcoefficient] at hmonomial
      simpa using hmonomial
    rw [heq]
    simpa using CPolynomial.le_natDegree_of_ne_zero
      ((CPolynomial.mem_support_iff T j).mp (by simpa [CBivariate.supportY] using hj))
  · by_cases hT : T = 0
    · subst T
      change 0 ≤ S.support.sup (fun m => m 1)
      omega
    · have hj : T.natDegree ∈ T.supportY := by
        simpa [CBivariate.supportY] using CPolynomial.natDegree_mem_support_of_nonzero hT
      have hcoefficient : T.val.coeff T.natDegree ≠ 0 :=
        (CPolynomial.mem_support_iff T T.natDegree).mp (by
          simpa [CBivariate.supportY] using hj)
      let i := (T.val.coeff T.natDegree).natDegree
      have hi : i ∈ (T.val.coeff T.natDegree).support :=
        CPolynomial.natDegree_mem_support_of_nonzero hcoefficient
      have hscalar : CPolynomial.coeff (T.val.coeff T.natDegree) i ≠ 0 :=
        (CPolynomial.mem_support_iff _ _).mp hi
      have hmem : Finsupp.single (0 : Fin 2) i + Finsupp.single 1 T.natDegree ∈ S.support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        exact hscalar
      have hle := Finset.le_sup (f := fun m : Fin 2 →₀ ℕ => m 1) hmem
      simpa using hle

/-- The stored univariate coefficient map is injective for a field embedding. -/
theorem mapCoefficientsHom_injective (embedding : F →+* E) :
    Function.Injective (mapCoefficientsHom embedding) := by
  intro a b hab
  change mapCoefficients embedding a = mapCoefficients embedding b at hab
  apply CPolynomial.toPoly_injective
  apply Polynomial.map_injective embedding embedding.injective
  simpa only [toPoly_mapCoefficients] using congrArg CPolynomial.toPoly hab

/-- Semantic bivariate conversion commutes with the executable nested coefficient map. -/
theorem toPoly_mapBivariate (embedding : F →+* E) (T : CBivariate F) :
    CBivariate.toPoly (mapBivariate embedding T) =
      (CBivariate.toPoly T).map (Polynomial.mapRingHom embedding) := by
  apply Polynomial.ext
  intro j
  rw [CBivariate.coeff_toPoly_Y, Polynomial.coeff_map, CBivariate.coeff_toPoly_Y]
  have h := congrArg (fun q : Polynomial (CPolynomial E) => q.coeff j)
    (toPoly_mapCoefficients (mapCoefficientsHom embedding) T)
  have hout : (mapBivariate embedding T).val.coeff j =
      mapCoefficients embedding (T.val.coeff j) := by
    rw [Polynomial.coeff_map] at h
    simp only [mapBivariate]
    rw [← CPolynomial.Raw.coeff_toPoly, ← CPolynomial.Raw.coeff_toPoly]
    rw [show (mapCoefficients (mapCoefficientsHom embedding) T).val.toPoly =
      CPolynomial.toPoly (R := CPolynomial E)
        (mapCoefficients (mapCoefficientsHom embedding) T) by
          unfold CPolynomial.toPoly
          rfl,
      show T.val.toPoly = CPolynomial.toPoly (R := CPolynomial F) T by
        unfold CPolynomial.toPoly
        rfl]
    change _ = mapCoefficients embedding _
    change _ = mapCoefficients embedding _ at h
    exact h
  rw [hout, toPoly_mapCoefficients]
  rfl

/-- Polynomial-graph evaluation commutes with supplied-field transport. -/
theorem eval_mapBivariate (embedding : F →+* E) (T : CBivariate F)
    (P : Polynomial F) :
    (CBivariate.toPoly (mapBivariate embedding T)).eval (P.map embedding) =
      Polynomial.map embedding ((CBivariate.toPoly T).eval P) := by
  rw [toPoly_mapBivariate, Polynomial.map_mapRingHom_eval_map]

/-- A base-field graph equation therefore remains a graph equation in every chosen center field. -/
theorem solution_mapRegularEquation (embedding : F →+* E) (T : CBivariate F)
    (P : Polynomial F)
    (hsolution : MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
      (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map embedding]
      (CPoly.fromCMvPolynomial (mapRegularEquation embedding T)) = 0 := by
  have hbase : (CBivariate.toPoly T).eval P = 0 := by
    rw [← CBivariate.eval₂_fromCMvPolynomial_toOrdinaryCMv]
    exact hsolution
  rw [mapRegularEquation, CBivariate.eval₂_fromCMvPolynomial_toOrdinaryCMv,
    eval_mapBivariate, hbase, Polynomial.map_zero]

/-- Injective coefficient transport preserves the stored outer degree. -/
theorem natDegree_mapBivariate (embedding : F →+* E) (T : CBivariate F) :
    (mapBivariate embedding T).natDegree = T.natDegree := by
  unfold mapBivariate
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    toPoly_mapCoefficients, Polynomial.natDegree_map_eq_of_injective]
  exact mapCoefficientsHom_injective embedding

/-- The executable mapped obstruction is precisely the obstruction of the mapped regular part. -/
theorem mapObstruction_eq (embedding : F →+* E) (T : CBivariate F) :
    mapObstruction embedding (RegularCenterObstruction.obstruction T) =
      RegularCenterObstruction.obstruction (mapBivariate embedding T) := by
  apply CPolynomial.toPoly_injective
  rw [mapObstruction, toPoly_mapCoefficients,
    RegularCenterObstruction.map_obstruction_toPoly]
  rw [RegularCenterObstruction.obstruction_toPoly, toPoly_mapBivariate,
    natDegree_mapBivariate]

/-- Injective transport preserves the obstruction's degree and nonzeroness. -/
theorem natDegree_mapObstruction (embedding : F →+* E) (obstruction : CPolynomial F) :
    (mapObstruction embedding obstruction).natDegree = obstruction.natDegree := by
  rw [CPolynomial.natDegree_toPoly (mapObstruction embedding obstruction),
    CPolynomial.natDegree_toPoly obstruction, mapObstruction, toPoly_mapCoefficients,
    Polynomial.natDegree_map_eq_of_injective embedding.injective]

theorem mapObstruction_ne_zero (embedding : F →+* E) {obstruction : CPolynomial F}
    (hne : obstruction ≠ 0) : mapObstruction embedding obstruction ≠ 0 := by
  intro hz
  have hpoly := congrArg CPolynomial.toPoly hz
  apply hne
  apply CPolynomial.toPoly_injective
  apply Polynomial.map_injective embedding embedding.injective
  simpa only [mapObstruction, toPoly_mapCoefficients, CPolynomial.toPoly_zero,
    Polynomial.map_zero] using hpoly

/-- Search the supplied centers, then run ordinary lifting and base-field agreement recovery. -/
def runOver {n : ℕ} (embedding : F →+* E) (T : CBivariate F)
    (obstruction : CPolynomial F) (centers : List E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) : Option (List (List F)) :=
  (selectObstructionCenter (mapObstruction embedding obstruction) centers).bind fun center ↦
    RegularFiber.run? embedding domain received k A (mapRegularEquation embedding T) center

/-- The proof-only facts a normalized regular part contributes to center search. -/
structure RegularData (T : CBivariate F) (obstruction : CPolynomial F) : Prop where
  positive : 0 < T.natDegree
  obstruction_eq : obstruction = RegularCenterObstruction.obstruction T
  obstruction_ne_zero : obstruction ≠ 0

/-- A regular package and an exact center prefix force the transported search and lift to run. -/
theorem runOver_exact {n : ℕ} (embedding : F →+* E) (T : CBivariate F)
    (obstruction : CPolynomial F) (facts : RegularData T obstruction)
    (centers : List E) (hnodup : centers.Nodup)
    (hlength : centers.length = obstruction.natDegree + 1)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, runOver embedding T obstruction centers domain received k A = some output ∧
      ExactOutput domain received k A output := by
  letI : DecidableEq E := instDecidableEqOfLawfulBEq
  have hdegree : (mapObstruction embedding obstruction).natDegree < centers.length := by
    rw [natDegree_mapObstruction, hlength]
    omega
  obtain ⟨center, hcenter⟩ := selectObstructionCenter_exists
    (mapObstruction embedding obstruction) centers
    (mapObstruction_ne_zero embedding facts.obstruction_ne_zero) hnodup hdegree
  have hcenterEval : (mapObstruction embedding obstruction).eval center ≠ 0 :=
    (selectObstructionCenter_sound _ _ _ hcenter).2
  have hmappedObstruction : mapObstruction embedding obstruction =
      RegularCenterObstruction.obstruction (mapBivariate embedding T) := by
    rw [facts.obstruction_eq, mapObstruction_eq]
  have hpositive : 0 < (mapBivariate embedding T).natDegree := by
    rw [natDegree_mapBivariate]
    exact facts.positive
  have hfacts := RegularCenterObstruction.fiberFacts_of_eval_obstruction_ne_zero
    (mapBivariate embedding T) center hpositive (by rwa [← hmappedObstruction])
  have hgood : goodCenter (mapRegularEquation embedding T) center = true :=
    SuppliedAdapter.goodCenter_regularEquation
      (by simpa only [mapRegularEquation] using
        degreeOf_one_toOrdinaryCMv (mapBivariate embedding T)) hfacts
  obtain ⟨output, hrun, hexact⟩ := RegularFiber.run?_exact embedding domain received k A hAk
    (mapRegularEquation embedding T) center hgood (fun P hd ha ↦
      solution_mapRegularEquation embedding T P (hsolutions P hd ha))
  exact ⟨output, by simp [runOver, hcenter, hrun], hexact⟩

section Supplied

variable (p : ℕ) [Fact p.Prime]
variable (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]

abbrev SuppliedField := Carrier f

/-- Run the branch chosen by `SuppliedCenters.suppliedRun`.  Both quadratic branches map the
equation into the computed extension but recover coefficient vectors over `Carrier f`. -/
def run? {n : ℕ} (T : CBivariate (Carrier f)) (obstruction : CPolynomial (Carrier f))
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f) (k A : ℕ) :
    Option (List (List (Carrier f))) :=
  let count := obstruction.natDegree + 1
  match SuppliedCenters.suppliedRun p f count with
  | .base capacity =>
      runOver (RingHom.id (Carrier f)) T obstruction
        (suppliedCenterPrefix p f count capacity) domain received k A
  | .oddQuadratic data =>
      runOver data.embedding T obstruction (data.centers (suppliedIndex p f))
        domain received k A
  | .binaryQuadratic characteristic _ data =>
      let _ : CharP (Carrier f) 2 := characteristic
      runOver data.embedding T obstruction (data.centers (suppliedIndex p f))
        domain received k A
  | .insufficientCapacity _ _ => none

/-- Exactness in the base-center branch, with the branch certificate supplying capacity. -/
theorem run?_exact_base {n : ℕ} (T : CBivariate (Carrier f))
    (obstruction : CPolynomial (Carrier f))
    (facts : RegularData T obstruction)
    (capacity : obstruction.natDegree + 1 ≤ p ^ f.natDegree)
    (hbranch : SuppliedCenters.suppliedRun p f (obstruction.natDegree + 1) = .base capacity)
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : (Carrier f)[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, run? p f T obstruction domain received k A = some output ∧
      ExactOutput domain received k A output := by
  rw [run?, hbranch]
  apply runOver_exact (RingHom.id (Carrier f)) T obstruction facts
  · exact suppliedCenterPrefix_nodup p f _ _
  · exact suppliedCenterPrefix_length p f _ _
  · exact hAk
  · exact hsolutions

/-- Exactness in the computed odd-characteristic quadratic branch. -/
theorem run?_exact_oddQuadratic {n : ℕ} (T : CBivariate (Carrier f))
    (obstruction : CPolynomial (Carrier f))
    (data : OddCenters.QuadraticData (Carrier f) (p ^ f.natDegree)
      (obstruction.natDegree + 1))
    (facts : RegularData T obstruction)
    (hbranch : SuppliedCenters.suppliedRun p f (obstruction.natDegree + 1) =
      .oddQuadratic data)
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : (Carrier f)[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, run? p f T obstruction domain received k A = some output ∧
      ExactOutput domain received k A output := by
  rw [run?, hbranch]
  apply runOver_exact data.embedding T obstruction facts
  · exact data.centers_nodup (suppliedIndex p f)
  · exact data.centers_length (suppliedIndex p f)
  · exact hAk
  · exact hsolutions

/-- Exactness in the computed binary Artin--Schreier quadratic branch. -/
theorem run?_exact_binaryQuadratic {n : ℕ} (T : CBivariate (Carrier f))
    (obstruction : CPolynomial (Carrier f))
    (characteristic : CharP (Carrier f) 2) (cardinality_eq : p ^ f.natDegree = 2 ^ f.natDegree)
    (data : @ArtinSchreierCenters.QuadraticData (Carrier f) _ characteristic
      (p ^ f.natDegree) (obstruction.natDegree + 1) f.natDegree)
    (facts : RegularData T obstruction)
    (hbranch : SuppliedCenters.suppliedRun p f (obstruction.natDegree + 1) =
      .binaryQuadratic characteristic cardinality_eq data)
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : (Carrier f)[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, run? p f T obstruction domain received k A = some output ∧
      ExactOutput domain received k A output := by
  rw [run?, hbranch]
  let _ : CharP (Carrier f) 2 := characteristic
  apply runOver_exact data.embedding T obstruction facts
  · exact data.centers_nodup (suppliedIndex p f)
  · exact data.centers_length (suppliedIndex p f)
  · exact hAk
  · exact hsolutions

/-- Unified success and exactness whenever the automatically requested center prefix fits in the
quadratic field.  The proof inspects the actual supplied dispatcher result; callers do not choose
a branch, center list, or capacity certificate for a particular construction. -/
theorem run?_exact {n : ℕ} (T : CBivariate (Carrier f))
    (obstruction : CPolynomial (Carrier f)) (facts : RegularData T obstruction)
    (hcapacity : obstruction.natDegree + 1 ≤ (p ^ f.natDegree) ^ 2)
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : (Carrier f)[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv T)) = 0) :
    ∃ output, run? p f T obstruction domain received k A = some output ∧
      ExactOutput domain received k A output := by
  generalize hresult : SuppliedCenters.suppliedRun p f (obstruction.natDegree + 1) = result
  cases result with
  | base capacity =>
      rw [run?, hresult]
      apply runOver_exact (RingHom.id (Carrier f)) T obstruction facts
      · exact suppliedCenterPrefix_nodup p f _ _
      · exact suppliedCenterPrefix_length p f _ _
      · exact hAk
      · exact hsolutions
  | oddQuadratic data =>
      rw [run?, hresult]
      apply runOver_exact data.embedding T obstruction facts
      · exact data.centers_nodup (suppliedIndex p f)
      · exact data.centers_length (suppliedIndex p f)
      · exact hAk
      · exact hsolutions
  | binaryQuadratic characteristic cardinality_eq data =>
      rw [run?, hresult]
      let _ : CharP (Carrier f) 2 := characteristic
      apply runOver_exact data.embedding T obstruction facts
      · exact data.centers_nodup (suppliedIndex p f)
      · exact data.centers_length (suppliedIndex p f)
      · exact hAk
      · exact hsolutions
  | insufficientCapacity base_insufficient capacity =>
      have hfailure := (SuppliedCenters.suppliedRun_capacity_iff p f
        (obstruction.natDegree + 1)).mp (congrArg SuppliedCenters.Result.branch hresult)
      omega

end Supplied

end ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport
