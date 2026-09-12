/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ConstantDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.BatchedCenter
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.RegularFiber
public import ArkLib.Data.FiniteField.ExplicitConstruction.OddCenters
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization

/-!
# Supplied-field boundary for zeroth-order decoding

This file connects three already executable components: ordinary normalization, supplied
finite-field coordinates, and characteristic-free regular-fiber lifting.  It deliberately keeps
the inverse-Frobenius callback needed by normalization and any binary extension-center producer
outside the adapter.  A checked normalization result can be packaged whenever a concrete center
list has enough distinct entries; the actual obstruction search then selects the fiber.

The dimension-one path is independent: it runs the exact frequency decoder before inspecting a
normalization result.  For larger dimensions this file states only conditional exactness from a
successful checked normalization and its graph-coverage premise.  It does not claim normalization
cannot fail or that every requested supplied field has enough centers.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedAdapter

open CompPoly Polynomial
open Polynomial.FunctionFieldAlgorithms
open ArkLib.FiniteField.ExplicitConstruction
open ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

abbrev NormalizationData := OrdinaryNormalization.Data

/-- Convert the returned nested polynomial to the ordinary decoder's `[X,Y]` equation. -/
def regularEquation (data : NormalizationData E) : CPoly.CMvPolynomial 2 E :=
  CBivariate.toOrdinaryCMv data.regular

/-- One more center than the obstruction degree is sufficient for deterministic selection. -/
def requiredCenters (data : NormalizationData E) : ℕ :=
  data.obstruction.natDegree + 1

/-- The ordinary concrete equation has exactly the stored specialized fiber. -/
theorem sectionPolynomial_regularEquation (T : CBivariate E) (center : E) :
    sectionPolynomial (CBivariate.toOrdinaryCMv T) center =
      RegularCenterObstruction.fiber T center := by
  apply CPolynomial.toPoly_injective
  rw [RegularCenterObstruction.fiber_toPoly]
  ext j
  rw [sectionPolynomial, CPoly.eval₂_equiv]
  simp only [CBivariate.toOrdinaryCMv, CPoly.CMvPolynomial.fromCMvPolynomial_sum,
    CPoly.CMvPolynomial.fromCMvPolynomial_monomial, CBivariate.toFinsupp_ordinaryMonomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial, Polynomial.coeff_map]
  have hprod (i d : ℕ) :
      (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) d).prod
          (fun index exponent => ![CPolynomial.C center, CPolynomial.X] index ^ exponent) =
        CPolynomial.C (center ^ i) * CPolynomial.X ^ d := by
    rw [Finsupp.prod_add_index]
    · rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      congr 1
      exact (map_pow CPolynomial.CHom center i).symm
    · intro index _
      simp
    · intro index _ left right
      exact pow_add _ left right
  simp_rw [hprod]
  have hcoeff (a : E) (b d : ℕ) :
      ((CPolynomial.CHom a *
          (CPolynomial.C (center ^ b) * CPolynomial.X ^ d)).toPoly).coeff j =
        if d = j then a * center ^ b else 0 := by
    change ((CPolynomial.C a *
      (CPolynomial.C (center ^ b) * CPolynomial.X ^ d)).toPoly).coeff j = _
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
      CPolynomial.C_toPoly, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    simp [eq_comm]
  rw [CBivariate.coeff_toPoly_Y]
  change _ = (T.val.coeff j).toPoly.eval center
  rw [← CPolynomial.eval_toPoly, CPolynomial.eval_eq_sum_support]
  simp only [CPolynomial.toPoly_sum, Polynomial.finsetSum_coeff]
  simp_rw [hcoeff]
  by_cases hj : j ∈ T.supportY
  · rw [Finset.sum_eq_single j]
    · simp only [if_true]
    · intro x hx hne
      simp [hne]
    · intro hnot
      exact (hnot hj).elim
  · have hj' : j ∉ (CBivariate.toPoly T).support := by
      rwa [CBivariate.support_toPoly_outer]
    have hzpoly : (CBivariate.toPoly T).coeff j = 0 :=
      Polynomial.notMem_support_iff.mp hj'
    rw [CBivariate.coeff_toPoly_Y] at hzpoly
    have hz : T.val.coeff j = 0 := (CPolynomial.toPoly_eq_zero_iff _).mp hzpoly
    rw [hz, (CPolynomial.support_empty_iff (0 : CPolynomial E)).mpr rfl, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro x hx
    have hne : x ≠ j := fun h => hj (h ▸ hx)
    simp [hne]

/-- The obstruction producer's checked fiber facts discharge the decoder's executable test. -/
theorem goodCenter_regularEquation {T : CBivariate E} {center : E}
    (hdegree : (CBivariate.toOrdinaryCMv T).degreeOf 1 = T.natDegree)
    (facts : RegularCenterObstruction.FiberFacts T center) :
    goodCenter (CBivariate.toOrdinaryCMv T) center = true := by
  rw [goodCenter_iff, sectionPolynomial_regularEquation]
  refine ⟨facts.fiber_ne_zero, facts.degree_eq.trans hdegree.symm, ?_⟩
  rw [CPolynomial.inverseMod_exists_iff_coprime]
  rw [RegularFiber.slope_toPoly, sectionPolynomial_regularEquation]
  simpa only [CPolynomial.derivative_toPoly] using
    ((CPolynomial.inverseMod_exists_iff_coprime _ _).mp facts.inverse)

/-- Checked producer output consumed by the obstruction selector and regular-fiber decoder. -/
structure CheckedInput (E : Type*) [Field E] [BEq E] [LawfulBEq E] where
  data : NormalizationData E
  centers : List E
  obstruction_ne_zero : data.obstruction ≠ 0
  centers_nodup : centers.Nodup
  obstruction_degree_lt : data.obstruction.natDegree < centers.length
  equation_degree : (regularEquation data).degreeOf 1 = data.regular.natDegree
  obstruction_good : ∀ center, data.obstruction.eval center ≠ 0 →
    goodCenter (regularEquation data) center = true

/-- Package an actual successful normalization result with any sufficient distinct center list. -/
def checkedOfNormalized (p : ℕ) (inverse : E → E) (Q : CPoly.CMvPolynomial 2 E)
    (data : NormalizationData E) (hrun : OrdinaryNormalization.run p inverse Q = .normalized data)
    (centers : List E) (hnodup : centers.Nodup)
    (hdegree : data.obstruction.natDegree < centers.length)
    (hequationDegree : (regularEquation data).degreeOf 1 = data.regular.natDegree) :
    CheckedInput E where
  data := data
  centers := centers
  obstruction_ne_zero := (OrdinaryNormalization.run_normalized_guards p inverse Q data hrun).2.2.2
  centers_nodup := hnodup
  obstruction_degree_lt := hdegree
  equation_degree := hequationDegree
  obstruction_good center hcenter :=
    goodCenter_regularEquation hequationDegree (OrdinaryNormalization.run_normalized_fiber
      p inverse Q data hrun center hcenter)

/-- Select the first nonzero obstruction value from the packaged center list. -/
def CheckedInput.selectCenter (input : CheckedInput E) : Option E :=
  selectObstructionCenter input.data.obstruction input.centers

/-- A checked package makes the actual batched obstruction search succeed. -/
theorem CheckedInput.selectCenter_exists (input : CheckedInput E) :
    ∃ center, input.selectCenter = some center :=
  selectObstructionCenter_exists input.data.obstruction input.centers
    input.obstruction_ne_zero input.centers_nodup input.obstruction_degree_lt

/-- Every selected center passes the concrete regular-fiber guard. -/
theorem CheckedInput.selectCenter_good (input : CheckedInput E) {center : E}
    (hcenter : input.selectCenter = some center) :
    goodCenter (regularEquation input.data) center = true :=
  input.obstruction_good center
    (selectObstructionCenter_sound input.data.obstruction input.centers center hcenter).2

/-- Characteristic-free ordinary lifting and recovery from a checked normalization package. -/
def CheckedInput.run? {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {n : ℕ} (input : CheckedInput E) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) : Option (List (List F)) :=
  input.selectCenter.bind fun center =>
    RegularFiber.run? base domain received k A (regularEquation input.data) center

/-- Conditional exactness of the composed nonconstant path.  Graph coverage remains an explicit
normalization-correctness obligation. -/
theorem CheckedInput.run?_exact {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {n : ℕ} (input : CheckedInput E) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial (regularEquation input.data)) = 0) :
    ∃ output, input.run? base domain received k A = some output ∧
      ExactOutput domain received k A output := by
  obtain ⟨center, hcenter⟩ := input.selectCenter_exists
  obtain ⟨output, hrun, hexact⟩ := RegularFiber.run?_exact base domain received k A hAk
    (regularEquation input.data) center (input.selectCenter_good hcenter) hsolutions
  exact ⟨output, by simp [CheckedInput.run?, hcenter, hrun], hexact⟩

section SuppliedBase

variable (p : ℕ) [Fact p.Prime]
variable (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]

/-- The actual supplied polynomial-basis field's prefix at the required obstruction budget. -/
def suppliedBaseCenters (data : NormalizationData (Carrier f))
    (hcapacity : requiredCenters data ≤ p ^ f.natDegree) : List (Carrier f) :=
  suppliedCenterPrefix p f (requiredCenters data) hcapacity

@[simp] theorem suppliedBaseCenters_length (data : NormalizationData (Carrier f))
    (hcapacity : requiredCenters data ≤ p ^ f.natDegree) :
    (suppliedBaseCenters p f data hcapacity).length = requiredCenters data :=
  suppliedCenterPrefix_length p f _ _

theorem suppliedBaseCenters_nodup (data : NormalizationData (Carrier f))
    (hcapacity : requiredCenters data ≤ p ^ f.natDegree) :
    (suppliedBaseCenters p f data hcapacity).Nodup :=
  suppliedCenterPrefix_nodup p f _ _

/-- Instantiate the checked consumer boundary directly in the supplied polynomial-basis field. -/
def checkedSuppliedBase (inverse : Carrier f → Carrier f)
    (Q : CPoly.CMvPolynomial 2 (Carrier f)) (data : NormalizationData (Carrier f))
    (hrun : OrdinaryNormalization.run p inverse Q = .normalized data)
    (hcapacity : requiredCenters data ≤ p ^ f.natDegree)
    (hequationDegree : (regularEquation data).degreeOf 1 = data.regular.natDegree) :
    CheckedInput (Carrier f) :=
  checkedOfNormalized p inverse Q data hrun (suppliedBaseCenters p f data hcapacity)
    (suppliedBaseCenters_nodup p f data hcapacity) (by
      rw [suppliedBaseCenters_length]
      simp [requiredCenters]) hequationDegree

/-- The odd-center producer's base branch is exactly the capacity needed by this adapter. -/
theorem oddCenters_base_capacity (data : NormalizationData (Carrier f)) (hodd : p ≠ 2)
    (hbranch : (OddCenters.suppliedRun p f (requiredCenters data) hodd).branch =
      .base) : requiredCenters data ≤ p ^ f.natDegree :=
  (OddCenters.suppliedRun_base_iff p f (requiredCenters data) hodd).mp hbranch

/-- Instantiate directly from an observed base-success branch of the immutable odd-center
producer.  Its quadratic branch is intentionally left to the extension-field mapping adapter. -/
def checkedSuppliedOddBase (inverse : Carrier f → Carrier f)
    (Q : CPoly.CMvPolynomial 2 (Carrier f)) (data : NormalizationData (Carrier f))
    (hrun : OrdinaryNormalization.run p inverse Q = .normalized data) (hodd : p ≠ 2)
    (hbranch : (OddCenters.suppliedRun p f (requiredCenters data) hodd).branch = .base)
    (hequationDegree : (regularEquation data).degreeOf 1 = data.regular.natDegree) :
    CheckedInput (Carrier f) :=
  checkedSuppliedBase p f inverse Q data hrun (oddCenters_base_capacity p f data hodd hbranch)
    hequationDegree

end SuppliedBase

section Dispatch

variable {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
variable (cmp : F → F → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Dimension-one frequency decoding precedes the optional ordinary normalization package. -/
def run? {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (input : Option (CheckedInput E)) : Option (List (List F)) :=
  if k = 1 then some (ConstantDecoder.run cmp A received)
  else input.bind fun checked => checked.run? base domain received k A

omit [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- The `k = 1` branch ignores normalization and executes frequency counting. -/
@[simp] theorem run?_one {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (A : ℕ) (input : Option (CheckedInput E)) :
    run? cmp base domain received 1 A input = some (ConstantDecoder.run cmp A received) := by
  simp [run?]

/-- The constant branch has the literal exact-output contract for every positive threshold. -/
theorem run?_one_exact {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (A : ℕ) (hA : 1 ≤ A) (input : Option (CheckedInput E)) :
    ∃ output, run? cmp base domain received 1 A input = some output ∧
      ExactOutput domain received 1 A output :=
  ⟨ConstantDecoder.run cmp A received, run?_one cmp base domain received A input,
    ConstantDecoder.run_exact cmp domain received A hA⟩

omit [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- For every other dimension, dispatch preserves the characteristic-free checked path. -/
theorem run?_of_ne_one {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (input : CheckedInput E) (hk : k ≠ 1) :
    run? cmp base domain received k A (some input) = input.run? base domain received k A := by
  simp [run?, hk]

omit [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- Conditional exactness for the nonconstant dispatch branch. -/
theorem run?_exact_of_ne_one {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (input : CheckedInput E) (hk : k ≠ 1)
    (hAk : k ≤ A)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial (regularEquation input.data)) = 0) :
    ∃ output, run? cmp base domain received k A (some input) = some output ∧
      ExactOutput domain received k A output := by
  rw [run?_of_ne_one cmp base domain received k A input hk]
  exact input.run?_exact base domain received k A hAk hsolutions

end Dispatch

end ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedAdapter
