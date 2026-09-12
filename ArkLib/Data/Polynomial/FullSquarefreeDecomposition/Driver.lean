/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Residues
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Frobenius
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.TreeRefinement
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.StoredFraction
public import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-!
# Recursive multiplicity-labelled decomposition

The executable path runs the residue calculation, balanced weighted product, exact division,
coefficientwise inverse Frobenius, and recursive-factor tree refinement. It never enumerates
irreducible factors. Matching a routed destination with its original multiplicity uses polynomial
equality, not an all-pairs gcd loop.

The checked arithmetic outcomes are explicit. The input/output reconstruction theorem below
concerns this program; general completeness and multiplicity classification require the residue
classification and weighted tree invariants, and are not inferred from reconstruction alone.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver

open Polynomial.FunctionFieldAlgorithms

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Labelled product used to state exact integer-multiplicity reconstruction. -/
def factorProduct (factors : List (ℕ × CPolynomial F)) : CPolynomial F :=
  (factors.map fun z => z.2 ^ z.1).prod

/-- Insert one factor into its multiplicity class, removing neutral factors. No gcd is used. -/
def insertFactor (z : ℕ × CPolynomial F) :
    List (ℕ × CPolynomial F) → List (ℕ × CPolynomial F)
  | [] => if z.2 == 1 then [] else [z]
  | a :: rest =>
    if z.2 == 1 then a :: rest
    else if z.1 == a.1 then (a.1, z.2 * a.2) :: rest
    else a :: insertFactor z rest

/-- Multiply all pieces with the same integer label. -/
def groupFactors (factors : List (ℕ × CPolynomial F)) : List (ℕ × CPolynomial F) :=
  factors.foldr insertFactor []

/-- Combining equal labels preserves their weighted product. -/
theorem factorProduct_insertFactor (z : ℕ × CPolynomial F)
    (factors : List (ℕ × CPolynomial F)) :
    factorProduct (insertFactor z factors) = z.2 ^ z.1 * factorProduct factors := by
  induction factors with
  | nil =>
    by_cases hz : z.2 = 1 <;> simp [insertFactor, factorProduct, hz]
  | cons a rest ih =>
    by_cases hz : z.2 = 1
    · simp [insertFactor, factorProduct, hz]
    · by_cases hm : z.1 = a.1
      · simp [insertFactor, factorProduct, hz, hm, mul_pow, mul_assoc]
      · simp only [insertFactor, beq_iff_eq, hz, ↓reduceIte, hm,
          factorProduct, List.map_cons, List.prod_cons] at *
        rw [ih]
        ring

/-- Grouping labels is an exact algebraic operation. -/
theorem factorProduct_groupFactors (factors : List (ℕ × CPolynomial F)) :
    factorProduct (groupFactors factors) = factorProduct factors := by
  induction factors with
  | nil => rfl
  | cons z rest ih =>
    change factorProduct (insertFactor z (groupFactors rest)) = _
    rw [factorProduct_insertFactor, ih]
    rfl

/-- Recover the integer multiplicity attached to a routed recursive modulus. -/
def destinationLabel? (recursive : List (ℕ × CPolynomial F)) (q : CPolynomial F) : Option ℕ :=
  (recursive.find? fun z => z.2 == q).map Prod.fst

/-- Label an intersection by `r + p*a`, retaining the residue and recursive labels. -/
def labelIntersections (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F)) :
    Option (List (ℕ × CPolynomial F)) :=
  routed.mapM fun z =>
    match destinationLabel? recursive z.2.1 with
    | none => none
    | some a => some (z.1 + p * a, z.2.2)

/-- Remove from each recursive factor its routed intersections. This scans destination labels;
all intersection gcds were already performed by the batch/remainder tree. -/
def recursiveOnly (p : ℕ) (M : MulContext F)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F)) :
    Option (List (ℕ × CPolynomial F)) :=
  recursive.mapM fun z => do
    let intersections := (routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2)
    let d ← exactDivide z.2 (weightedProduct M intersections)
    pure (p * z.1, d)

/-- The appendix's final overlap refinement, including residue-only and recursive-only pieces. -/
def refineFactors (p : ℕ) (M : MulContext F) (D : ModContext F)
    (strata recursive : List (ℕ × CPolynomial F)) : Option (List (ℕ × CPolynomial F)) := do
  if recursive.isEmpty then
    pure (groupFactors strata)
  else
    let [tree] := BatchRemainder.build M (recursive.map Prod.snd) | none
    let refined := refineRoot M D tree strata
    let mixed ← labelIntersections p recursive refined.1
    let onlyRecursive ← recursiveOnly p M recursive refined.1
    pure (groupFactors (refined.2 ++ mixed ++ onlyRecursive))

/-- Distinguish zero input and genuine checked arithmetic failures. -/
inductive Failure where
  | zeroInput
  | invalidCharacteristic
  | nonmonicInput
  | residueInverse
  | unfinishedResidues
  | inexactStratumDivision
  | nonFrobeniusQuotient
  | nondecreasingContraction
  | treeRefinement
  | reconstruction
  | factorCertificate
  deriving DecidableEq, BEq, Repr

/-- One actual recursive residue/Frobenius step. -/
structure Stage where
  inputDegree : ℕ
  contractedDegree : ℕ
  residueLabels : List ℕ
  deriving Repr

/-- Monic factors and the contraction transcript returned by the recursive calculation. -/
structure MonicOutput (F : Type*) [Zero F] where
  factors : List (ℕ × CPolynomial F)
  stages : List Stage

/-- The computed residue strata and contracted repeated part for one recursive call. -/
structure Preparation (F : Type*) [Zero F] where
  strata : List (ℕ × CPolynomial F)
  contracted : CPolynomial F

/-- Execute the residue calculation, balanced stratum product, exact division and contraction. -/
def prepare (p : ℕ) (inverse : F → F) (M : MulContext F) (f : CPolynomial F) :
    Except Failure (Preparation F) :=
  match FullSquarefreeDecomposition.run p f with
  | none => .error .residueInverse
  | some residues =>
    if residues.residual != 1 then .error .unfinishedResidues else
      let strata := pruneTagged residues.strata
      match exactDivide f (weightedProduct M strata) with
      | none => .error .inexactStratumDivision
      | some repeated =>
        if repeated.derivative != 0 then .error .nonFrobeniusQuotient else
          .ok ⟨strata, contractWith p inverse repeated⟩

/-- Execute the characteristic-safe recursion. The degree guard is the explicit recursive
termination check; every recursive call operates on the computed Frobenius contraction. -/
def decomposeMonic (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) : Except Failure (MonicOutput F) := do
  if p ≤ 1 then throw .invalidCharacteristic
  if !f.monic then throw .nonmonicInput
  if f == 1 then return ⟨[], []⟩
  let prepared ← prepare p inverse M f
  if _hc : prepared.contracted.natDegree < f.natDegree then
    let recursive ← decomposeMonic p inverse M D prepared.contracted
    let some factors := refineFactors p M D prepared.strata recursive.factors
      | throw .treeRefinement
    if factorProduct factors != f then throw .reconstruction
    return ⟨factors, ⟨f.natDegree, prepared.contracted.natDegree,
      prepared.strata.map Prod.fst⟩ :: recursive.stages⟩
  else throw .nondecreasingContraction
termination_by f.natDegree
decreasing_by exact _hc

/-- The scalar unit and normalized multiplicity factors of a nonzero input. -/
structure Output (F : Type*) [Zero F] where
  scalar : F
  factors : List (ℕ × CPolynomial F)
  stages : List Stage

/-- One derivative gcd checks joint squarefreeness of all output factors. No pairwise gcd
verification is performed; positivity and monicity are checked individually. -/
def checkFactors (M : MulContext F) (factors : List (ℕ × CPolynomial F)) : Bool :=
  factors.all (fun z => decide (0 < z.1) && z.2.monic && z.2 != 1) &&
    let support := weightedProduct M (factors.map fun z => (1, z.2))
    gcdFactor support support.derivative == 1

/-- Normalize the leading scalar, execute the recursive producer, and verify reconstruction. -/
def decompose (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) : Except Failure (Output F) :=
  if f == 0 then .error .zeroInput else
    match decomposeMonic p inverse M D (f.leadingCoeff⁻¹ • f) with
    | .error err => .error err
    | .ok out =>
      if !checkFactors M out.factors then .error .factorCertificate else
      if C f.leadingCoeff * factorProduct out.factors != f then .error .reconstruction
      else .ok ⟨f.leadingCoeff, out.factors, out.stages⟩

/-- Retain exactly the factors whose actual integer multiplicity meets the threshold. -/
def thresholdProduct (M : MulContext F) (threshold : ℕ) (out : Output F) : CPolynomial F :=
  weightedProduct M ((out.factors.filter fun z => threshold ≤ z.1).map fun z => (1, z.2))

/-- Every successful public result reconstructs the exact input, including its scalar unit. -/
theorem decompose_reconstruct (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out) :
    C out.scalar * factorProduct out.factors = f := by
  unfold decompose at hout
  split at hout
  · simp at hout
  · cases hr : decomposeMonic p inverse M D (f.leadingCoeff⁻¹ • f) with
    | error err => simp [hr] at hout
    | ok result =>
      simp only [hr] at hout
      split at hout
      · simp at hout
      · split at hout
        · simp at hout
        · rename_i heq
          have heq' : C f.leadingCoeff * factorProduct result.factors = f := by simpa using heq
          have ho : out = ⟨f.leadingCoeff, result.factors, result.stages⟩ := by
            simpa using hout.symm
          subst out
          exact heq'

/-- One computed residue/contraction step has the exact characteristic-power identity.
The coefficient callback is certified only over the base coefficient field. -/
theorem prepare_reconstruct (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) (M : MulContext F)
    (f : CPolynomial F) (out : Preparation F) (hout : prepare p inverse M f = .ok out) :
    weightedProduct M out.strata * out.contracted ^ p = f := by
  unfold prepare at hout
  cases hr : FullSquarefreeDecomposition.run p f with
  | none => simp [hr] at hout
  | some residues =>
    simp only [hr] at hout
    split at hout
    · simp at hout
    · cases hd : exactDivide f (weightedProduct M (pruneTagged residues.strata)) with
      | none => simp [hd] at hout
      | some repeated =>
        simp only [hd] at hout
        split at hout
        · simp at hout
        · rename_i hderiv
          have hderiv' : repeated.derivative = 0 := by simpa using hderiv
          have ho : out = ⟨pruneTagged residues.strata, contractWith p inverse repeated⟩ := by
            simpa using hout.symm
          subst out
          rw [contractWith_pow_eq p inverse hinverse repeated hderiv', mul_comm]
          exact ((exactDivide_eq_some_iff _ _ _).mp hd).2

private theorem coprime_of_gcdFactor_one (a b : CPolynomial F) (h : gcdFactor a b = 1) :
    IsCoprime a.toPoly b.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  apply IsRelPrime.isCoprime
  intro d hda hdb
  apply isUnit_of_dvd_one
  rw [← toPoly_one, ← h, gcdFactor_toPoly, dvd_normalize_iff]
  exact EuclideanDomain.dvd_gcd hda hdb

/-- The single global derivative gcd certifies squarefreeness of the output support. -/
theorem checkFactors_spec (M : MulContext F) (factors : List (ℕ × CPolynomial F))
    (hc : checkFactors M factors = true) :
    (∀ z ∈ factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1) ∧
      Squarefree ((factors.map Prod.snd).prod).toPoly := by
  have hparts : factors.all (fun z => decide (0 < z.1) && z.2.monic && z.2 != 1) = true ∧
      (let support := weightedProduct M (factors.map fun z => (1, z.2));
        gcdFactor support support.derivative == 1) = true := by
    simpa only [checkFactors, Bool.and_eq_true] using hc
  have hshape : ∀ z ∈ factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1 := by
    intro z hz
    have ht := List.all_eq_true.mp hparts.1 z hz
    simpa [Bool.and_eq_true, and_assoc, bne_iff_ne] using ht
  refine ⟨hshape, ?_⟩
  let support := weightedProduct M (factors.map fun z => (1, z.2))
  have hg : gcdFactor support support.derivative = 1 := by
    simpa only [beq_iff_eq] using hparts.2
  have hsep : support.toPoly.Separable := by
    change IsCoprime support.toPoly support.toPoly.derivative
    rw [← derivative_toPoly]
    exact coprime_of_gcdFactor_one _ _ hg
  have hp : support = (factors.map Prod.snd).prod := by
    dsimp [support]
    rw [weightedProduct_eq]
    · simp [List.map_map, Function.comp_def]
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact (hshape a ha).2.1
  rw [← hp]
  exact hsep.squarefree

private theorem toPoly_dvd_prod_of_mem (a : CPolynomial F) (ps : List (CPolynomial F))
    (ha : a ∈ ps) : a.toPoly ∣ ps.prod.toPoly := by
  obtain ⟨q, hq⟩ := List.dvd_prod ha
  exact ⟨q.toPoly, by rw [hq, toPoly_mul]⟩

/-- Squarefreeness of the whole support implies pairwise coprimality of its pieces. -/
theorem pairwise_of_squarefree_product (ps : List (CPolynomial F))
    (hs : Squarefree ps.prod.toPoly) :
    ps.Pairwise (fun a b => IsCoprime a.toPoly b.toPoly) := by
  induction ps with
  | nil => simp
  | cons a rest ih =>
    rw [List.prod_cons, toPoly_mul] at hs
    rw [List.pairwise_cons]
    refine ⟨?_, ih (hs.squarefree_of_dvd (dvd_mul_left _ _))⟩
    intro b hb
    exact (IsRelPrime.of_squarefree_mul hs).isCoprime.of_isCoprime_of_dvd_right
      (toPoly_dvd_prod_of_mem b rest hb)

/-- Certified output factors are individually squarefree and pairwise coprime. -/
theorem checkFactors_squarefree_pairwise (M : MulContext F)
    (factors : List (ℕ × CPolynomial F)) (hc : checkFactors M factors = true) :
    (∀ z ∈ factors, Squarefree z.2.toPoly) ∧
      factors.Pairwise (fun a b => IsCoprime a.2.toPoly b.2.toPoly) := by
  have hs := (checkFactors_spec M factors hc).2
  refine ⟨?_, ?_⟩
  · intro z hz
    exact hs.squarefree_of_dvd (toPoly_dvd_prod_of_mem z.2 _ (List.mem_map.mpr ⟨z, hz, rfl⟩))
  · simpa only [List.pairwise_map] using
      pairwise_of_squarefree_product (factors.map Prod.snd) hs

/-- Successful public output has passed the single global support certificate. -/
theorem decompose_checked (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out) :
    checkFactors M out.factors = true := by
  unfold decompose at hout
  split at hout
  · simp at hout
  · cases hr : decomposeMonic p inverse M D (f.leadingCoeff⁻¹ • f) with
    | error err => simp [hr] at hout
    | ok result =>
      simp only [hr] at hout
      split at hout
      · simp at hout
      · rename_i hcheck
        split at hout
        · simp at hout
        · have ho : out = ⟨f.leadingCoeff, result.factors, result.stages⟩ := by
            simpa using hout.symm
          subst out
          simpa using hcheck

/-- Semantic labelled factorization: positive integer multiplicities, normalized nonconstant
squarefree factors, pairwise coprimality, scalar unit, and exact weighted reconstruction. -/
def IsDecomposition (f : CPolynomial F) (out : Output F) : Prop :=
  out.scalar ≠ 0 ∧
    (∀ z ∈ out.factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1 ∧ Squarefree z.2.toPoly) ∧
    out.factors.Pairwise (fun a b => IsCoprime a.2.toPoly b.2.toPoly) ∧
    C out.scalar * factorProduct out.factors = f

/-- No successful result represents the zero polynomial. -/
theorem decompose_input_ne_zero (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out) : f ≠ 0 := by
  intro hz
  subst f
  simp [decompose] at hout

/-- Every result returned by the actual recursive program is a full labelled factorization.
This soundness theorem does not assert that the checked failure branches are unreachable. -/
theorem decompose_sound (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out) :
    IsDecomposition f out := by
  have hc := decompose_checked p inverse M D f out hout
  have hshape := (checkFactors_spec M out.factors hc).1
  obtain ⟨hs, hp⟩ := checkFactors_squarefree_pairwise M out.factors hc
  have heq := decompose_reconstruct p inverse M D f out hout
  refine ⟨?_, ?_, hp, heq⟩
  · intro hz
    apply decompose_input_ne_zero p inverse M D f out hout
    simpa [hz] using heq.symm
  · intro z hz
    exact ⟨(hshape z hz).1, (hshape z hz).2.1, (hshape z hz).2.2, hs z hz⟩

/-- Prime fields instantiate the executable inverse coefficient operation by the identity. -/
def decomposePrime (p : ℕ) [Fact p.Prime]
    (M : MulContext (ZMod p)) (D : ModContext (ZMod p)) (f : CPolynomial (ZMod p)) :
    Except Failure (Output (ZMod p)) := decompose p id M D f

/-- Threshold extraction multiplies the actual labelled factors and removes their multiplicities. -/
theorem thresholdProduct_eq (M : MulContext F) (threshold : ℕ) (out : Output F)
    (hm : ∀ z ∈ out.factors, z.2.monic) :
    thresholdProduct M threshold out =
      ((out.factors.filter fun z => threshold ≤ z.1).map Prod.snd).prod := by
  rw [thresholdProduct, weightedProduct_eq]
  · simp [List.map_map, Function.comp_def]
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hm a (List.mem_filter.mp ha).1

/-- Every successful nonconstant preparation strictly decreases degree. Thus the explicit
recursive guard cannot reject a correctly computed characteristic-power preparation. -/
theorem prepare_degree_lt (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) (M : MulContext F)
    (f : CPolynomial F) (out : Preparation F) (hdegree : 0 < f.natDegree)
    (hout : prepare p inverse M f = .ok out) : out.contracted.natDegree < f.natDegree := by
  have heq := congrArg CPolynomial.toPoly (prepare_reconstruct p inverse hinverse M f out hout)
  rw [toPoly_mul, toPoly_pow] at heq
  have hf : f.toPoly ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    rw [Polynomial.natDegree_zero, ← natDegree_toPoly] at hd
    omega
  have hprod : (weightedProduct M out.strata).toPoly * out.contracted.toPoly ^ p ≠ 0 := by
    rw [heq]
    exact hf
  have hd := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_mul (mul_ne_zero_iff.mp hprod).1 (mul_ne_zero_iff.mp hprod).2,
    Polynomial.natDegree_pow, ← natDegree_toPoly, ← natDegree_toPoly, ← natDegree_toPoly] at hd
  have hp := (Fact.out : Nat.Prime p).two_le
  have hmul := Nat.mul_le_mul_right out.contracted.natDegree hp
  by_cases hz : out.contracted.natDegree = 0
  · omega
  · omega

private theorem coprime_factorProduct (a : Polynomial F) (factors : List (ℕ × CPolynomial F))
    (hc : ∀ z ∈ factors, IsCoprime a z.2.toPoly) :
    IsCoprime a (factorProduct factors).toPoly := by
  induction factors with
  | nil => simpa only [factorProduct, List.map_nil, List.prod_nil, toPoly_one] using
      (isCoprime_one_right (x := a))
  | cons z rest ih =>
    change IsCoprime a (z.2 ^ z.1 * factorProduct rest).toPoly
    rw [toPoly_mul, toPoly_pow]
    exact (hc z (by simp)).pow_right.mul_right (ih (fun b hb => hc b (by simp [hb])))

/-- Pairwise factorization isolates any labelled component from a coprime cofactor. -/
theorem factorProduct_cofactor (factors : List (ℕ × CPolynomial F))
    (hp : factors.Pairwise (fun a b => IsCoprime a.2.toPoly b.2.toPoly))
    (z : ℕ × CPolynomial F) (hz : z ∈ factors) :
    ∃ q : Polynomial F, (factorProduct factors).toPoly = z.2.toPoly ^ z.1 * q ∧
      IsCoprime z.2.toPoly q := by
  induction factors with
  | nil => simp at hz
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hz with rfl | hz
    · refine ⟨(factorProduct rest).toPoly, ?_, coprime_factorProduct _ rest hhead⟩
      change (z.2 ^ z.1 * factorProduct rest).toPoly = _
      rw [toPoly_mul, toPoly_pow]
    · obtain ⟨q, hq, hc⟩ := ih htail hz
      refine ⟨a.2.toPoly ^ a.1 * q, ?_, (hhead z hz).symm.pow_right.mul_right hc⟩
      change (a.2 ^ a.1 * factorProduct rest).toPoly = _
      rw [toPoly_mul, toPoly_pow, hq]
      ring

/-- Each returned integer label is an exact component multiplicity: its factor raised to that
label has a coprime cofactor. This includes multiplicities divisible by the characteristic. -/
theorem decompose_factor_cofactor (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out)
    (z : ℕ × CPolynomial F) (hz : z ∈ out.factors) :
    ∃ q : Polynomial F, f.toPoly = z.2.toPoly ^ z.1 * q ∧ IsCoprime z.2.toPoly q := by
  obtain ⟨hs, _, hp, heq⟩ := decompose_sound p inverse M D f out hout
  obtain ⟨q, hq, hc⟩ := factorProduct_cofactor out.factors hp z hz
  have hu : IsCoprime z.2.toPoly (Polynomial.C out.scalar) := by
    refine ⟨0, Polynomial.C out.scalar⁻¹, ?_⟩
    simp [← Polynomial.C_mul, inv_mul_cancel₀ hs]
  refine ⟨Polynomial.C out.scalar * q, ?_, hu.mul_right hc⟩
  rw [← heq, toPoly_mul, C_toPoly, hq]
  ring

/-- A returned nonconstant factor cannot divide the input to a greater exponent than its label. -/
theorem decompose_exact_power (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (f : CPolynomial F) (out : Output F) (hout : decompose p inverse M D f = .ok out)
    (z : ℕ × CPolynomial F) (hz : z ∈ out.factors) :
    z.2.toPoly ^ z.1 ∣ f.toPoly ∧ ¬z.2.toPoly ^ (z.1 + 1) ∣ f.toPoly := by
  obtain ⟨q, heq, hc⟩ := decompose_factor_cofactor p inverse M D f out hout z hz
  have hshape := (decompose_sound p inverse M D f out hout).2.1 z hz
  have hm := (monic_toPoly_iff z.2).mp hshape.2.1
  refine ⟨⟨q, heq⟩, ?_⟩
  intro hd
  rw [heq, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hm.ne_zero)] at hd
  have hu := hm.eq_one_of_isUnit (hc.isUnit_of_dvd hd)
  apply hshape.2.2.1
  apply toPoly_injective
  simpa only [toPoly_one] using hu

/-- The residue loop uses consecutive positive labels and never wraps beyond its supplied fuel. -/
theorem residueLoop_label_bounds (fuel r : ℕ) (a q : CPolynomial F) :
    ∀ z ∈ (residueLoop fuel r a q).strata, r ≤ z.1 ∧ z.1 < r + fuel := by
  induction fuel generalizing r a q with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    simp only [residueLoop]
    split
    · simp
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · have hb := ih (r + 1) _ _ z hz
        omega

/-- The actual residue producer returns labels in `1,...,p-1`, also bounded by input degree. -/
theorem residue_run_label_bounds (p : ℕ) (f : CPolynomial F) (out : ResidueOutput F)
    (hout : FullSquarefreeDecomposition.run p f = some out) :
    ∀ z ∈ out.strata, 0 < z.1 ∧ z.1 < p ∧ z.1 ≤ f.natDegree := by
  unfold FullSquarefreeDecomposition.run at hout
  split at hout
  · simp at hout
  · cases hq : residuePolynomial? f with
    | none => simp [hq] at hout
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at hout
      subst out
      intro z hz
      have hb := residueLoop_label_bounds (min (p - 1) f.natDegree) 1 _ q z hz
      omega

/-- Every preparation records the actual residue result, exact quotient and contraction input. -/
theorem prepare_spec (p : ℕ) (inverse : F → F) (M : MulContext F)
    (f : CPolynomial F) (out : Preparation F) (hout : prepare p inverse M f = .ok out) :
    ∃ residues repeated,
      FullSquarefreeDecomposition.run p f = some residues ∧ residues.residual = 1 ∧
      out.strata = pruneTagged residues.strata ∧
      exactDivide f (weightedProduct M out.strata) = some repeated ∧
      repeated.derivative = 0 ∧ out.contracted = contractWith p inverse repeated := by
  unfold prepare at hout
  cases hr : FullSquarefreeDecomposition.run p f with
  | none => simp [hr] at hout
  | some residues =>
    simp only [hr] at hout
    split at hout
    · simp at hout
    · rename_i hresidual
      cases hd : exactDivide f (weightedProduct M (pruneTagged residues.strata)) with
      | none => simp [hd] at hout
      | some repeated =>
        simp only [hd] at hout
        split at hout
        · simp at hout
        · rename_i hderiv
          have ho : out = ⟨pruneTagged residues.strata, contractWith p inverse repeated⟩ := by
            simpa using hout.symm
          subst out
          exact ⟨residues, repeated, rfl, by simpa using hresidual, rfl, hd,
            by simpa using hderiv, rfl⟩

/-- Prepared residue labels are genuine nonzero characteristic residues, never truncated labels. -/
theorem prepare_label_bounds (p : ℕ) (inverse : F → F) (M : MulContext F)
    (f : CPolynomial F) (out : Preparation F) (hout : prepare p inverse M f = .ok out) :
    ∀ z ∈ out.strata, 0 < z.1 ∧ z.1 < p ∧ z.1 ≤ f.natDegree := by
  obtain ⟨residues, _, hr, _, hs, _⟩ := prepare_spec p inverse M f out hout
  rw [hs]
  intro z hz
  exact residue_run_label_bounds p f residues hr z (List.mem_filter.mp hz).1

private theorem residue_run_monic (p : ℕ) (f : CPolynomial F) (out : ResidueOutput F)
    (hf : f.monic) (hout : FullSquarefreeDecomposition.run p f = some out) :
    ∀ z ∈ out.strata, z.2.monic := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [FullSquarefreeDecomposition.run, beq_iff_eq, hn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    exact residueLoop_strata_monic _ _ _ q (gcdComplement_monic hf)

private theorem factorProduct_monic (factors : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ factors, z.2.monic) : (factorProduct factors).monic := by
  rw [monic_toPoly_iff]
  induction factors with
  | nil => simp [factorProduct, toPoly_one]
  | cons z rest ih =>
    change (z.2 ^ z.1 * factorProduct rest).toPoly.Monic
    rw [toPoly_mul, toPoly_pow]
    exact (((monic_toPoly_iff z.2).mp (hm z (by simp))).pow z.1).mul
      (ih (fun a ha => hm a (by simp [ha])))

/-- Prepared strata and the contracted recursive input remain monic on the certified domain. -/
theorem prepare_monic (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (hinverse : ∀ a, inverse a ^ p = a) (M : MulContext F)
    (f : CPolynomial F) (out : Preparation F) (hf : f.monic)
    (hout : prepare p inverse M f = .ok out) :
    (∀ z ∈ out.strata, z.2.monic) ∧ out.contracted.monic := by
  obtain ⟨residues, repeated, hr, _, hstrata, hd, hderiv, hcontract⟩ :=
    prepare_spec p inverse M f out hout
  have hm : ∀ z ∈ out.strata, z.2.monic := by
    rw [hstrata]
    intro z hz
    exact residue_run_monic p f residues hf hr z (List.mem_filter.mp hz).1
  refine ⟨hm, ?_⟩
  have hb : (weightedProduct M out.strata).toPoly.Monic := by
    rw [weightedProduct_eq M out.strata hm]
    exact (monic_toPoly_iff _).mp (factorProduct_monic out.strata hm)
  have heq := congrArg CPolynomial.toPoly ((exactDivide_eq_some_iff _ _ _).mp hd).2
  rw [toPoly_mul] at heq
  have hrep : repeated.toPoly.Monic := hb.of_mul_monic_left (by
    rw [mul_comm, heq]
    exact (monic_toPoly_iff _).mp hf)
  rw [hcontract, monic_toPoly_iff]
  have hpow := congrArg CPolynomial.toPoly
    (contractWith_pow_eq p inverse hinverse repeated hderiv)
  rw [toPoly_pow] at hpow
  have hl := congrArg Polynomial.leadingCoeff hpow
  rw [Polynomial.leadingCoeff_pow, hrep.leadingCoeff] at hl
  apply frobenius_inj F p
  simpa only [frobenius_def, map_one] using hl

namespace Multiplicity

open Polynomial
variable {K : Type*} [Field K]

/-- Local logarithmic derivative coefficient after cancelling the root power. -/
theorem local_derivative_residue (x : K) (n : ℕ) (A B w : Polynomial K)
    (h : Polynomial.derivative ((Polynomial.X - Polynomial.C x) ^ (n + 1) * A) =
      (Polynomial.X - Polynomial.C x) ^ n * (B * w)) :
    B.eval x * w.eval x = ((n + 1 : ℕ) : K) * A.eval x := by
  have he : (Polynomial.X - Polynomial.C x) ^ n *
      (Polynomial.C ((n + 1 : ℕ) : K) * A +
        (Polynomial.X - Polynomial.C x) * Polynomial.derivative A) =
      (Polynomial.X - Polynomial.C x) ^ n * (B * w) := by
    rw [← h, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow]
    simp only [Nat.add_sub_cancel]
    ring
  have hc := mul_left_cancel₀ (pow_ne_zero n (monic_X_sub_C x).ne_zero) he
  have hv := congrArg (fun q : Polynomial K => q.eval x) hc
  simpa using hv.symm

/-- The computed residue equals the integer multiplicity at a simple quotient root. -/
theorem local_residue_eq_multiplicity (x : K) (n : ℕ) (A B w v q c : Polynomial K)
    (hder : Polynomial.derivative ((Polynomial.X - Polynomial.C x) ^ (n + 1) * A) =
      (Polynomial.X - Polynomial.C x) ^ n * (B * w))
    (hA : A = B * c) (hv : v = (Polynomial.X - Polynomial.C x) * c)
    (hB : B.eval x ≠ 0) (hc : c.eval x ≠ 0)
    (hq : q.eval x * v.derivative.eval x = w.eval x) :
    q.eval x = ((n + 1 : ℕ) : K) := by
  have hd := local_derivative_residue x n A B w hder
  have hvd : v.derivative.eval x = c.eval x := by
    simp [hv, Polynomial.derivative_mul]
  rw [hA, Polynomial.eval_mul] at hd
  rw [hvd] at hq
  apply mul_right_cancel₀ hc
  rw [hq]
  apply mul_left_cancel₀ hB
  calc
    B.eval x * w.eval x = ((n + 1 : ℕ) : K) * (B.eval x * c.eval x) := hd
    _ = B.eval x * (((n + 1 : ℕ) : K) * c.eval x) := by ring

variable [DecidableEq K]

theorem rootMultiplicity_gcd_of_nonzero (f g : Polynomial K) (hf : f ≠ 0) (hg : g ≠ 0)
    (x : K) : (gcd f g).rootMultiplicity x =
      min (f.rootMultiplicity x) (g.rootMultiplicity x) := by
  have hfg : gcd f g ≠ 0 := by
    intro h
    exact hf ((gcd_eq_zero_iff f g).mp h).1
  apply le_antisymm
  · exact le_min (rootMultiplicity_le_rootMultiplicity_of_dvd hf (gcd_dvd_left f g) x)
      (rootMultiplicity_le_rootMultiplicity_of_dvd hg (gcd_dvd_right f g) x)
  · apply (le_rootMultiplicity_iff hfg).mpr
    exact dvd_gcd
      ((pow_dvd_pow _ (min_le_left _ _)).trans (f.pow_rootMultiplicity_dvd x))
      ((pow_dvd_pow _ (min_le_right _ _)).trans (g.pow_rootMultiplicity_dvd x))

theorem rootMultiplicity_derivative_gcd (f : Polynomial K) (hf : f ≠ 0) (x : K)
    (hx : f.IsRoot x) (hm : (f.rootMultiplicity x : K) ≠ 0) :
    (gcd f f.derivative).rootMultiplicity x = f.rootMultiplicity x - 1 := by
  have hd := derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hx
    (mem_nonZeroDivisors_iff_ne_zero.mpr hm)
  have hdn : f.derivative ≠ 0 := by
    intro hz
    have hdiv : (Polynomial.X - Polynomial.C x) ^ f.rootMultiplicity x ∣
        f.derivative := by simp [hz]
    obtain ⟨A, hA, hAn⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
    have hpos : 0 < f.rootMultiplicity x := (rootMultiplicity_pos hf).mpr hx
    have he := congrArg (fun q : Polynomial K => q.derivative) hA
    rw [hz, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow] at he
    have hcancel : Polynomial.C (f.rootMultiplicity x : K) * A +
        (Polynomial.X - Polynomial.C x) * A.derivative = 0 := by
      apply (mul_eq_zero.mp (show (Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1) *
          (Polynomial.C (f.rootMultiplicity x : K) * A +
            (Polynomial.X - Polynomial.C x) * A.derivative) = 0 from ?_)).resolve_left
        (pow_ne_zero _ (monic_X_sub_C x).ne_zero)
      calc
        _ = Polynomial.C (f.rootMultiplicity x : K) *
              (Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1) * A +
            (Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1 + 1) * A.derivative := by
              ring
        _ = 0 := by rw [Nat.sub_add_cancel hpos]; exact he.symm
    have hev := congrArg (fun q : Polynomial K => q.eval x) hcancel
    have : A.eval x = 0 := (mul_eq_zero.mp (by simpa using hev)).resolve_left hm
    exact hAn (dvd_iff_isRoot.mpr this)
  rw [rootMultiplicity_gcd_of_nonzero f f.derivative hf hdn x, hd]
  exact min_eq_right (Nat.sub_le _ _)

/-- The derivative quotient has a simple root whenever its multiplicity is nonzero in the field. -/
theorem derivative_quotient_rootMultiplicity (f v : Polynomial K) (hf : f ≠ 0) (x : K)
    (hx : f.IsRoot x) (hm : (f.rootMultiplicity x : K) ≠ 0)
    (hfv : gcd f f.derivative * v = f) : v.rootMultiplicity x = 1 := by
  have hg := rootMultiplicity_derivative_gcd f hf x hx hm
  have hprod : gcd f f.derivative * v ≠ 0 := by rwa [hfv]
  have hadd := rootMultiplicity_mul (x := x) hprod
  rw [hfv, hg] at hadd
  have hpos := (rootMultiplicity_pos hf).mpr hx
  omega

/-- Roots whose multiplicity vanishes in the coefficient field are absent from the
derivative quotient. -/
theorem derivative_quotient_rootMultiplicity_zero (f v : Polynomial K) (hf : f ≠ 0) (x : K)
    (hm : (f.rootMultiplicity x : K) = 0)
    (hfv : gcd f f.derivative * v = f) : v.rootMultiplicity x = 0 := by
  obtain ⟨A, hA, _⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
  have hd : (Polynomial.X - Polynomial.C x) ^ f.rootMultiplicity x ∣ f.derivative := by
    refine ⟨A.derivative, ?_⟩
    conv_lhs => rw [hA, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow]
    simp [hm]
  have hgn : gcd f f.derivative ≠ 0 := by
    intro hz
    exact hf ((gcd_eq_zero_iff f f.derivative).mp hz).1
  have hge := (le_rootMultiplicity_iff hgn).mpr
    (dvd_gcd (f.pow_rootMultiplicity_dvd x) hd)
  have hle := rootMultiplicity_le_rootMultiplicity_of_dvd hf (gcd_dvd_left f f.derivative) x
  have hprod : gcd f f.derivative * v ≠ 0 := by rwa [hfv]
  have hadd := rootMultiplicity_mul (x := x) hprod
  rw [hfv] at hadd
  omega

/-- The derivative-gcd residue is the true integer multiplicity at each quotient root. -/
theorem gcd_residue_eq_rootMultiplicity (f v w q : Polynomial K) (hf : f ≠ 0) (x : K)
    (hfv : gcd f f.derivative * v = f)
    (hfw : gcd f f.derivative * w = f.derivative)
    (hx : v.IsRoot x) (hq : q.eval x * v.derivative.eval x = w.eval x) :
    q.eval x = (f.rootMultiplicity x : K) := by
  have hu : gcd f f.derivative ≠ 0 := by
    intro hz
    exact hf ((gcd_eq_zero_iff f f.derivative).mp hz).1
  have hv : v ≠ 0 := by intro hz; simp [hz] at hfv; exact hf hfv.symm
  have hfx : f.IsRoot x := by
    rw [← hfv, IsRoot, Polynomial.eval_mul]
    simp [show v.eval x = 0 from hx]
  have hmpos : 0 < f.rootMultiplicity x := (rootMultiplicity_pos hf).mpr hfx
  have hm : (f.rootMultiplicity x : K) ≠ 0 := by
    intro hz
    have hzero := derivative_quotient_rootMultiplicity_zero f v hf x hz hfv
    have hpos := (rootMultiplicity_pos hv).mpr hx
    omega
  have hum := rootMultiplicity_derivative_gcd f hf x hfx hm
  have hvm := derivative_quotient_rootMultiplicity f v hf x hfx hm hfv
  obtain ⟨A, hA, _⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
  obtain ⟨B, hB, hBn⟩ :=
    (gcd f f.derivative).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hu x
  obtain ⟨c, hc, hcn⟩ := v.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hv x
  rw [hum] at hB
  rw [hvm, pow_one] at hc
  have hAc : A = B * c := by
    apply mul_left_cancel₀ (pow_ne_zero (f.rootMultiplicity x) (monic_X_sub_C x).ne_zero)
    calc
      _ = f := hA.symm
      _ = ((Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1) * B) *
          ((Polynomial.X - Polynomial.C x) * c) := by rw [← hB, ← hc, hfv]
      _ = (Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1 + 1) *
          (B * c) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hmpos]
  have hder : Polynomial.derivative
        ((Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1 + 1) * A) =
      (Polynomial.X - Polynomial.C x)^(f.rootMultiplicity x - 1) * (B * w) := by
    rw [Nat.sub_add_cancel hmpos, ← hA, ← hfw, hB]
    ring
  have he := local_residue_eq_multiplicity x (f.rootMultiplicity x - 1) A B w v q c
    hder hAc hc (by intro hz; exact hBn (dvd_iff_isRoot.mpr hz))
    (by intro hz; exact hcn (dvd_iff_isRoot.mpr hz)) hq
  simpa only [Nat.sub_add_cancel hmpos] using he

end Multiplicity

/-- The executable monic gcd refines the normalized polynomial gcd. -/
private theorem gcdFactor_eq_polynomial_gcd [DecidableEq F] (f g : CPolynomial F) :
    (gcdFactor f g).toPoly = gcd f.toPoly g.toPoly := by
  rw [gcdFactor_toPoly]
  have hass : Associated (EuclideanDomain.gcd f.toPoly g.toPoly) (gcd f.toPoly g.toPoly) :=
    associated_of_dvd_dvd
      (dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _))
      (EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  calc
    _ = normalize (gcd f.toPoly g.toPoly) := normalize_eq_normalize_iff_associated.mpr hass
    _ = _ := StrongNormalizedGCDMonoid.normalize_gcd _ _

/-- At every derivative-quotient root, the actual residue output is the true integer
multiplicity. -/
theorem residuePolynomial?_eval_eq_rootMultiplicity (f q : CPolynomial F)
    (hf : f.monic) (x : F)
    (hx : (gcdComplement f f.derivative).toPoly.IsRoot x)
    (hq : residuePolynomial? f = some q) :
    q.toPoly.eval x = (f.toPoly.rootMultiplicity x : F) := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hfn : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hfv := congrArg CPolynomial.toPoly (derivativeParts_exact hfn)
  have hfw : (gcdFactor f f.derivative).toPoly *
      (f.derivative.divByMonic (gcdFactor f f.derivative)).toPoly = f.derivative.toPoly := by
    rw [divByMonic_toPoly_eq_divByMonic _ _ (gcdFactor_monic hfn)]
    have hm := Polynomial.modByMonic_eq_zero_iff_dvd
      ((monic_toPoly_iff _).mp (gcdFactor_monic hfn)) |>.mpr
        (gcdFactor_dvd_right f f.derivative)
    simpa only [hm, zero_add] using
      Polynomial.modByMonic_add_div f.derivative.toPoly (gcdFactor f f.derivative).toPoly
  have hi := residuePolynomial?_root_identity (RingHom.id F) x
    (gcdComplement_monic hf)
    (by simpa only [derivativeParts, gcdComplement, Polynomial.eval₂_id,
      Polynomial.IsRoot] using hx) hq
  apply Multiplicity.gcd_residue_eq_rootMultiplicity f.toPoly
    (gcdComplement f f.derivative).toPoly
    (f.derivative.divByMonic (gcdFactor f f.derivative)).toPoly q.toPoly
    ((monic_toPoly_iff f).mp hf).ne_zero x
  · simpa only [derivativeParts, gcdComplement, toPoly_mul,
      gcdFactor_eq_polynomial_gcd, derivative_toPoly] using hfv
  · simpa only [gcdFactor_eq_polynomial_gcd, derivative_toPoly] using hfw
  · exact hx
  · simpa only [Polynomial.eval₂_id, derivative_toPoly, derivativeParts,
      gcdComplement] using hi

/-! ## Concrete supplied-field entrypoint -/

/-- Execute the full decomposition over a supplied polynomial-basis finite field.
The inverse-Frobenius callback is the concrete gcd/regrouping implementation owned by the
explicit-field layer; callers supply neither an inverse oracle nor its correctness proof. -/
def decomposeSupplied (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : ModContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (f : CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)) :
    Except Failure (Output (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)) :=
  decompose p (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius p modulus) M D f

/-- Every returned supplied-field result has the full labelled-decomposition certificate. -/
theorem decomposeSupplied_sound (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : ModContext (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (f : CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (out : Output (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hout : decomposeSupplied p modulus M D f = .ok out) : IsDecomposition f out :=
  decompose_sound p
    (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius p modulus) M D f out hout

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
