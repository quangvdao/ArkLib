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

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
