/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.BivariateFactorDegrees
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ClearDenominators
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularCenterObstruction

/-!
# Ordinary normalization from stored interpolants

The producer works in `[X,Y]` order, removes Y content, saturates the visible factors
using both partial derivatives, and descends every function-field gcd through computed
canonical denominator clearing. Joint Frobenius contraction is restricted to base coefficients.
The final regular part and its discarded inseparable factor remain explicit in the output.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization

open CompPoly CPolynomial CPoly BivariateReducedSupport

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Descend the executed function-field gcd to a primitive global polynomial. -/
def globalGcd (A B : CBivariate F) : CBivariate F :=
  ClearDenominators.primitivePart <| ClearDenominators.descended <|
    FunctionFieldEuclid.gcd (ClearDenominators.embed A) (ClearDenominators.embed B)

/-- Exact function-field division followed by executable primitive descent. -/
def quotientPrimitive (A B : CBivariate F) : Option (CBivariate F) :=
  (FunctionFieldEuclid.divide (ClearDenominators.embed A) (ClearDenominators.embed B)).map
    fun q => ClearDenominators.primitivePart (ClearDenominators.descended q)

private theorem valueGlobal_injective :
    Function.Injective (ClearDenominators.valueGlobal (F := F)) := by
  classical
  intro A B h
  apply CBivariate.ringEquiv.injective
  exact Polynomial.map_injective _ (RatFunc.algebraMap_injective F) h

open scoped Classical in
/-- The descended gcd is associated to the actual Euclidean gcd over the function field. -/
theorem globalGcd_associated (A B : CBivariate F) :
    Associated (ClearDenominators.valueGlobal (globalGcd A B))
      (EuclideanDomain.gcd (ClearDenominators.valueGlobal A)
        (ClearDenominators.valueGlobal B)) := by
  classical
  have h := ClearDenominators.clear_primitive_associated
    (FunctionFieldEuclid.gcd (ClearDenominators.embed A) (ClearDenominators.embed B))
  rw [FunctionFieldEuclid.value_gcd, ClearDenominators.value_embed,
    ClearDenominators.value_embed] at h
  exact h.trans (normalize_associated _)

/-- Nonzero input gives a nonzero gcd, and primitive Gauss descent makes its divisibility
valid globally in `F[X][Y]`, without excluding denominator-zero fibers. -/
theorem globalGcd_dvd (A B : CBivariate F) (hA : A ≠ 0) :
    CBivariate.toPoly (globalGcd A B) ∣ CBivariate.toPoly A ∧
      CBivariate.toPoly (globalGcd A B) ∣ CBivariate.toPoly B := by
  classical
  let g := FunctionFieldEuclid.gcd (ClearDenominators.embed A) (ClearDenominators.embed B)
  have ha : ClearDenominators.valueGlobal A ≠ 0 := by
    intro hz
    apply hA
    apply (valueGlobal_injective (F := F))
    simpa [ClearDenominators.valueGlobal_zero] using hz
  have hdA : FunctionFieldEuclid.value g ∣ ClearDenominators.valueGlobal A := by
    rw [FunctionFieldEuclid.value_gcd, ClearDenominators.value_embed,
      ClearDenominators.value_embed, normalize_dvd_iff]
    exact EuclideanDomain.gcd_dvd_left _ _
  have hdB : FunctionFieldEuclid.value g ∣ ClearDenominators.valueGlobal B := by
    rw [FunctionFieldEuclid.value_gcd, ClearDenominators.value_embed,
      ClearDenominators.value_embed, normalize_dvd_iff]
    exact EuclideanDomain.gcd_dvd_right _ _
  have hg : FunctionFieldEuclid.value g ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdA
    exact ha hdA
  exact ⟨ClearDenominators.clear_primitive_dvd_global hg hdA,
    ClearDenominators.clear_primitive_dvd_global hg hdB⟩

/-- Primitive exact division carries a global cross-product identity, before localization.
In particular it remains an equality on fibers where its clearing scalar vanishes. -/
theorem quotientPrimitive_global_identity (A B R : CPolynomial (CPolynomial F))
    (h : quotientPrimitive A B = some R) :
    ∃ (scale content : CPolynomial F), scale.toPoly ≠ 0 ∧ content.toPoly ≠ 0 ∧
      (CPolynomial.C content : CBivariate F) * B * R =
        (CPolynomial.C scale : CBivariate F) * A := by
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    let result := ClearDenominators.clear q
    refine ⟨result.scale, result.content, result.scale_ne_zero,
      ClearDenominators.primitiveContent_ne_zero _, ?_⟩
    apply (valueGlobal_injective (F := F))
    rw [ClearDenominators.valueGlobal_mul, ClearDenominators.valueGlobal_mul,
      ClearDenominators.valueGlobal_mul, ClearDenominators.valueGlobal_C,
      ClearDenominators.valueGlobal_C]
    have hclear := ClearDenominators.clear_combined_identity q
    have hdiv := ((FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq).2
    rw [ClearDenominators.value_embed, ClearDenominators.value_embed] at hdiv
    change Polynomial.C _ * ClearDenominators.valueGlobal B *
        ClearDenominators.valueGlobal result.primitive =
      Polynomial.C _ * ClearDenominators.valueGlobal A
    calc
      _ = ClearDenominators.valueGlobal B *
          (Polynomial.C _ * ClearDenominators.valueGlobal result.primitive) := by ring
      _ = ClearDenominators.valueGlobal B *
          (Polynomial.C _ * FunctionFieldEuclid.value q) := by rw [hclear]
      _ = Polynomial.C _ * (FunctionFieldEuclid.value q *
          ClearDenominators.valueGlobal B) := by ring
      _ = _ := by rw [hdiv]

/-- The exact global cross-product identity gives polynomial graph equivalence for division. -/
theorem quotientPrimitive_graph (A B R : CPolynomial (CPolynomial F))
    (h : quotientPrimitive A B = some R) (P : Polynomial F) :
    (CBivariate.toPoly B).eval P * (CBivariate.toPoly R).eval P = 0 ↔
      (CBivariate.toPoly A).eval P = 0 := by
  classical
  obtain ⟨scale, content, hs, hc, hid⟩ := quotientPrimitive_global_identity A B R h
  have heval := congrArg (fun T : CPolynomial (CPolynomial F) =>
    (CBivariate.toPoly T).eval P) hid
  rw [CBivariate.toPoly_mul, CBivariate.toPoly_mul, CBivariate.toPoly_mul,
    Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul] at heval
  have hC (c : CPolynomial F) :
      (CBivariate.toPoly (CPolynomial.C c : CPolynomial (CPolynomial F))).eval P = c.toPoly := by
    rw [CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, Polynomial.map_C, Polynomial.eval_C]
    exact CPolynomial.ringEquiv_apply c
  rw [hC, hC, mul_assoc] at heval
  have hzero := congrArg (fun v : Polynomial F => v = 0) heval
  simpa only [mul_eq_zero, hc, hs, false_or] using Iff.of_eq hzero

/-- A nonzero primitive quotient has the standard primitive-polynomial certificate. -/
theorem quotientPrimitive_isPrimitive (A B R : CPolynomial (CPolynomial F))
    (h : quotientPrimitive A B = some R) (hR : R ≠ 0) :
    (CBivariate.toPoly R).IsPrimitive := by
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    apply ClearDenominators.clear_primitive_isPrimitive
    intro hz
    have hv := (ClearDenominators.clear_primitive_associated q).eq_zero_iff.mpr hz
    apply hR
    apply (valueGlobal_injective (F := F))
    exact hv.trans (by simp [ClearDenominators.valueGlobal, CBivariate.toPoly_zero])

/-- A nonzero executed primitive quotient divides its input in the global polynomial ring. -/
theorem quotientPrimitive_dvd_left_global (A B R : CBivariate F)
    (h : quotientPrimitive A B = some R) (hR : R ≠ 0) :
    CBivariate.toPoly R ∣ CBivariate.toPoly A := by
  classical
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    have hn : FunctionFieldEuclid.value q ≠ 0 := by
      intro hz
      have hp := (ClearDenominators.clear_primitive_associated q).eq_zero_iff.mpr hz
      apply hR
      apply CBivariate.ringEquiv.injective
      apply Polynomial.map_injective (algebraMap (Polynomial F) (RatFunc F))
        (RatFunc.algebraMap_injective F)
      change (CBivariate.toPoly (ClearDenominators.primitivePart
        (ClearDenominators.descended q))).map _ = (CBivariate.toPoly 0).map _
      simpa only [ClearDenominators.valueGlobal, ClearDenominators.clear,
        CBivariate.toPoly_zero, Polynomial.map_zero] using hp
    apply ClearDenominators.clear_primitive_dvd_global hn
    have hd := ((FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq).2
    rw [ClearDenominators.value_embed, ClearDenominators.value_embed] at hd
    exact ⟨ClearDenominators.valueGlobal B, hd.symm⟩

/-- Primitive division cannot increase the Y degree of a nonzero input. -/
theorem quotientPrimitive_natDegree_le (A B R : CBivariate F)
    (h : quotientPrimitive A B = some R) (hA : A ≠ 0) :
    (CBivariate.toPoly R).natDegree ≤ (CBivariate.toPoly A).natDegree := by
  classical
  by_cases hR : R = 0
  · simp [hR, CBivariate.toPoly_zero]
  apply Polynomial.natDegree_le_of_dvd (quotientPrimitive_dvd_left_global A B R h hR)
  intro hz
  apply hA
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly A = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using hz

/-- Primitive division cannot increase the X degree of a nonzero input. -/
theorem quotientPrimitive_degreeX_le (A B R : CBivariate F)
    (h : quotientPrimitive A B = some R) (hA : A ≠ 0) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly R) ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly A) := by
  classical
  by_cases hR : R = 0
  · simp [hR, CBivariate.toPoly_zero, Polynomial.Bivariate.degreeX]
  apply Polynomial.Bivariate.degreeX_le_of_dvd (quotientPrimitive_dvd_left_global A B R h hR)
  intro hz
  apply hA
  apply CBivariate.ringEquiv.injective
  change CBivariate.toPoly A = CBivariate.toPoly 0
  simpa only [CBivariate.toPoly_zero] using hz

/-- A nonzero returned primitive quotient certifies that its dividend was nonzero. -/
theorem quotientPrimitive_input_ne_zero (A B R : CBivariate F)
    (h : quotientPrimitive A B = some R) (hR : R ≠ 0) : A ≠ 0 := by
  classical
  unfold quotientPrimitive at h
  cases hq : FunctionFieldEuclid.divide (ClearDenominators.embed A)
      (ClearDenominators.embed B) with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    subst R
    have hn : FunctionFieldEuclid.value q ≠ 0 := by
      intro hz
      have hp := (ClearDenominators.clear_primitive_associated q).eq_zero_iff.mpr hz
      apply hR
      apply CBivariate.ringEquiv.injective
      apply Polynomial.map_injective (algebraMap (Polynomial F) (RatFunc F))
        (RatFunc.algebraMap_injective F)
      change (CBivariate.toPoly (ClearDenominators.primitivePart
        (ClearDenominators.descended q))).map _ = (CBivariate.toPoly 0).map _
      simpa only [ClearDenominators.valueGlobal, ClearDenominators.clear,
        CBivariate.toPoly_zero, Polynomial.map_zero] using hp
    have hd := (FunctionFieldEuclid.divide_eq_some_iff _ _ q).mp hq
    intro hA
    have heq := hd.2
    rw [ClearDenominators.value_embed, ClearDenominators.value_embed,
      hA, ClearDenominators.valueGlobal_zero] at heq
    have hB : ClearDenominators.valueGlobal B ≠ 0 := by
      rw [← ClearDenominators.value_embed]
      intro hz
      apply hd.1
      apply FunctionFieldEuclid.value_injective
      simpa only [FunctionFieldEuclid.value, CPolynomial.toPoly_zero,
        Polynomial.map_zero] using hz
    exact (mul_ne_zero hn hB) heq

/-- Merge two supports without retaining their common factors twice. -/
def mergeSupports (A B : CBivariate F) : Option (CBivariate F) :=
  quotientPrimitive (A * B) (globalGcd A B)

/-- Concrete arithmetic stages retained when a checked computation fails. -/
inductive Failure where
  | degreeBound
  | nondecreasingRoot
  | jointRoot
  | quotient
  | merge
  | regularity
  | obstruction
  deriving BEq, Repr

/-- One inspected saturation step of the revised Radical algorithm. -/
structure Saturation (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- Common gcd of the input and both partial derivatives. -/
  common : CBivariate F
  /-- Factors with multiplicity visible to differentiation. -/
  visible : CBivariate F
  /-- The divisor removing all copies of visible factors. -/
  removed : CBivariate F
  /-- The residual on which joint Frobenius contraction is permitted. -/
  residual : CBivariate F

/-- Compute V=H/gcd(H,H_X,H_Y), then R=H/gcd(H,V^ell), with primitive descent. -/
def saturate (ell : ℕ) (H : CBivariate F) : Except Failure (Saturation F) := do
  let _ : DecidableEq F := instDecidableEqOfLawfulBEq
  let common := globalGcd H (globalGcd (CBivariate.partialDerivX H)
    (CBivariate.partialDerivY H))
  let some visible := quotientPrimitive H common | throw .quotient
  let removed := globalGcd H (visible ^ ell)
  let some residual := quotientPrimitive H removed | throw .quotient
  return ⟨common, visible, removed, residual⟩

/-- Saturated Radical from the revised paper. All recursion is on the computed joint root
of the saturated residual, never on the unsaturated repeated gcd. The degree guard certifies
termination; proving that it and the arithmetic failures are unreachable remains separate. -/
def radical (p : ℕ) (inverse : F → F) (ell : ℕ) (H : CBivariate F) :
    Except Failure (CBivariate F) := do
  if H.natDegree > ell then throw .degreeBound
  if H.natDegree == 0 then return 1
  let step ← saturate ell H
  if step.residual.natDegree == 0 then return step.visible
  if ell < p then throw .degreeBound
  let some root := jointRoot p inverse step.residual | throw .jointRoot
  if _hprogress : root.natDegree < H.natDegree then
    let recursive ← radical p inverse ell root
    return step.visible * recursive
  else throw .nondecreasingRoot
termination_by H.natDegree
decreasing_by exact _hprogress

/-- Inspectable output of regular-part normalization, including the discarded factor. -/
structure Data (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The actual converted original interpolant. -/
  original : CBivariate F
  /-- The recursively computed global reduced support. -/
  support : CBivariate F
  /-- The derivative-common factor removed from that support. -/
  discarded : CBivariate F
  /-- The final primitive regular polynomial. -/
  regular : CBivariate F
  /-- The computed Sylvester obstruction. -/
  obstruction : CPolynomial F

/-- The raw producer distinguishes zero input, constant regular part and arithmetic errors.
The `constantRegularPart` branch still requires a no-graph proof before application use. -/
inductive Result (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  | zeroInput
  | constantRegularPart (data : Data F)
  | normalized (data : Data F)
  | arithmeticFailure (reason : Failure)

/-- Primitive SeparablePart of an already computed global radical. -/
def separablePart (support : CBivariate F) : Option (CBivariate F) :=
  quotientPrimitive support (globalGcd support (CBivariate.partialDerivY support))

/-- Compute the regular quotient, keeping the discarded part and all arithmetic checks. -/
def finish (original support : CBivariate F) : Result F :=
  let discarded := globalGcd support (CBivariate.partialDerivY support)
  match separablePart support with
  | none => .arithmeticFailure .quotient
  | some regular =>
    let obstruction := RegularCenterObstruction.obstruction regular
    let data : Data F := ⟨original, support, discarded, regular, obstruction⟩
    if regular.natDegree == 0 then .constantRegularPart data
    else
      let image := ClearDenominators.embed regular
      if FunctionFieldEuclid.gcd image image.derivative != 1 then
        .arithmeticFailure .regularity
      else if obstruction == 0 then .arithmeticFailure .obstruction
      else .normalized data

/-- Execute saturated Radical, SeparablePart and the actual stored obstruction.
The base-coefficient callback is a conditional interface to Personal 3's supplied-field
inverse-Frobenius implementation; it is not a completed field constructor. -/
def run (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F) : Result F :=
  let original := fromOrdinaryCMv Q
  if original == 0 then .zeroInput
  else match radical p inverse original.natDegree (ClearDenominators.primitivePart original) with
    | .error e => .arithmeticFailure e
    | .ok support => finish original support

/-- Characteristic-bound conditional interface for the supplied-field implementation.
Personal 3 must supply this callback concretely when `p` is at most the Y-degree bound.
The characteristic proof is tied to the actual coefficient field and erased at runtime. -/
def runCertified (p : ℕ) [Fact p.Prime] [CharP F p] (inverse : F → F)
    (Q : CMvPolynomial 2 F)
    (_hinverse : p ≤ (fromOrdinaryCMv Q).natDegree → ∀ a, inverse a ^ p = a) : Result F :=
  run p inverse Q

/-- A returned nonconstant result passed its actual regularity and obstruction checks. -/
theorem finish_normalized_guards (original support : CBivariate F) (data : Data F)
    (h : finish original support = .normalized data) :
    0 < data.regular.natDegree ∧
      FunctionFieldEuclid.gcd (ClearDenominators.embed data.regular)
        (ClearDenominators.embed data.regular).derivative = 1 ∧
      data.obstruction = RegularCenterObstruction.obstruction data.regular ∧
      data.obstruction ≠ 0 := by
  unfold finish at h
  dsimp only at h
  split at h
  · cases h
  · rename_i regular hq
    split at h
    · cases h
    · rename_i hd
      split at h
      · cases h
      · rename_i hg
        split at h
        · cases h
        · rename_i ho
          cases h
          refine ⟨?_, ?_, rfl, ?_⟩
          · have : regular.natDegree ≠ 0 := by simpa using hd
            exact Nat.pos_of_ne_zero this
          · simpa using hg
          · simpa using ho

/-- Returned data records the executed regular quotient of the computed support. -/
theorem finish_normalized_provenance (original support : CBivariate F) (data : Data F)
    (h : finish original support = .normalized data) :
    data.original = original ∧ data.support = support ∧
      data.discarded = globalGcd support (CBivariate.partialDerivY support) ∧
      quotientPrimitive data.support data.discarded = some data.regular := by
  unfold finish at h
  dsimp only at h
  split at h
  · cases h
  · rename_i regular hq
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨rfl, rfl, rfl, hq⟩

/-- Final normalization retains an explicit global scalar product identity. -/
theorem finish_normalized_global_identity (original support : CBivariate F) (data : Data F)
    (h : finish original support = .normalized data) :
    ∃ (scale content : CPolynomial F), scale.toPoly ≠ 0 ∧ content.toPoly ≠ 0 ∧
      (CPolynomial.C content : CPolynomial (CPolynomial F)) *
          (show CPolynomial (CPolynomial F) from data.discarded) *
          (show CPolynomial (CPolynomial F) from data.regular) =
        (CPolynomial.C scale : CPolynomial (CPolynomial F)) *
          (show CPolynomial (CPolynomial F) from data.support) := by
  exact quotientPrimitive_global_identity _ _ _
    (finish_normalized_provenance original support data h).2.2.2

/-- The same checked facts hold for the actual interpolant-to-normalization program. -/
theorem run_normalized_guards (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) :
    0 < data.regular.natDegree ∧
      FunctionFieldEuclid.gcd (ClearDenominators.embed data.regular)
        (ClearDenominators.embed data.regular).derivative = 1 ∧
      data.obstruction = RegularCenterObstruction.obstruction data.regular ∧
      data.obstruction ≠ 0 := by
  unfold run at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact finish_normalized_guards _ _ data h

/-- Successful output records both the actual radical call and its final primitive quotient. -/
theorem run_normalized_provenance (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) :
    data.original = fromOrdinaryCMv Q ∧
      radical p inverse (fromOrdinaryCMv Q).natDegree
        (ClearDenominators.primitivePart (fromOrdinaryCMv Q)) = .ok data.support ∧
      quotientPrimitive data.support data.discarded = some data.regular := by
  unfold run at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i support hs
      obtain ⟨ho, hsup, _, hq⟩ := finish_normalized_provenance _ _ data h
      exact ⟨ho, hsup ▸ hs, hq⟩

/-- The actual regular output divides its computed support globally and obeys both degree
bounds relative to that support. Original-relative bounds still need the radical invariant. -/
theorem run_normalized_divisibility_bounds (p : ℕ) (inverse : F → F)
    (Q : CMvPolynomial 2 F) (data : Data F) (h : run p inverse Q = .normalized data) :
    data.support ≠ 0 ∧
      CBivariate.toPoly data.regular ∣ CBivariate.toPoly data.support ∧
      (CBivariate.toPoly data.regular).natDegree ≤ (CBivariate.toPoly data.support).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly data.support) := by
  have hd := (run_normalized_guards p inverse Q data h).1
  have hn : data.regular ≠ 0 := by
    intro hz
    rw [hz, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
      Polynomial.natDegree_zero] at hd
    omega
  have hq := (run_normalized_provenance p inverse Q data h).2.2
  have hs := quotientPrimitive_input_ne_zero _ _ _ hq hn
  exact ⟨hs, quotientPrimitive_dvd_left_global _ _ _ hq hn,
    quotientPrimitive_natDegree_le _ _ _ hq hs, quotientPrimitive_degreeX_le _ _ _ hq hs⟩

/-- Every returned regular polynomial has a function-field image coprime to its derivative. -/
theorem run_normalized_coprime (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) :
    IsCoprime (ClearDenominators.valueGlobal data.regular)
      (ClearDenominators.valueGlobal data.regular).derivative := by
  classical
  have hg := (run_normalized_guards p inverse Q data h).2.1
  have hv := congrArg FunctionFieldEuclid.value hg
  rw [FunctionFieldEuclid.value_gcd] at hv
  have h1 : FunctionFieldEuclid.value (1 : CPolynomial (StoredField.Carrier F)) = 1 := by
    simp only [FunctionFieldEuclid.value, CPolynomial.toPoly_one, Polynomial.map_one]
  rw [h1] at hv
  have hderiv (f : CPolynomial (StoredField.Carrier F)) :
      FunctionFieldEuclid.value f.derivative = (FunctionFieldEuclid.value f).derivative := by
    simp only [FunctionFieldEuclid.value, CPolynomial.derivative_toPoly,
      Polynomial.derivative_map]
  rw [hderiv, ClearDenominators.value_embed] at hv
  apply IsRelPrime.isCoprime
  intro d hda hdb
  apply isUnit_of_dvd_one
  rw [← hv, dvd_normalize_iff]
  exact EuclideanDomain.dvd_gcd hda hdb

/-- A returned nonconstant polynomial is primitive over the base polynomial ring. -/
theorem run_normalized_isPrimitive (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) :
    (CBivariate.toPoly data.regular).IsPrimitive := by
  have hd := (run_normalized_guards p inverse Q data h).1
  have hn : data.regular ≠ 0 := by
    intro hz
    rw [hz, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
      Polynomial.natDegree_zero] at hd
    omega
  unfold run at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact quotientPrimitive_isPrimitive _ _ _
        (finish_normalized_provenance _ _ data h).2.2.2 hn

/-- The actual returned data supplies the full input record of the obstruction producer.
The unresolved coverage theorem concerns reaching this result and its original graph roots. -/
def certifiedInput (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) :
    RegularCenterObstruction.Input F :=
  ⟨data.regular, run_normalized_isPrimitive p inverse Q data h,
    (run_normalized_guards p inverse Q data h).1, run_normalized_coprime p inverse Q data h⟩

/-- The computed obstruction returned by normalization satisfies the explicit degree bound. -/
theorem run_normalized_obstruction_degree (p : ℕ) (inverse : F → F)
    (Q : CMvPolynomial 2 F) (data : Data F) (h : run p inverse Q = .normalized data) :
    data.obstruction.natDegree ≤ 2 * data.regular.natDegree *
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) := by
  obtain ⟨hd, _, heq, _⟩ := run_normalized_guards p inverse Q data h
  rw [heq]
  exact RegularCenterObstruction.obstruction_natDegree_le _ hd

/-- Nonzero values of an actually returned obstruction certify all regular fiber facts. -/
theorem run_normalized_fiber (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F)
    (data : Data F) (h : run p inverse Q = .normalized data) (c : F)
    (hc : data.obstruction.eval c ≠ 0) :
    RegularCenterObstruction.FiberFacts data.regular c := by
  obtain ⟨hd, _, heq, _⟩ := run_normalized_guards p inverse Q data h
  apply RegularCenterObstruction.fiberFacts_of_eval_obstruction_ne_zero _ c hd
  rwa [← heq]

end Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization
