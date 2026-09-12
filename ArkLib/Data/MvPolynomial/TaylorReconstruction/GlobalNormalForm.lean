/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.LocalEquation
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.ClearedCoefficients
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Recover global normal forms from a confluent sample

Recovery executes inverse affine shifts on the stored coefficient array. Local
specialization always roundtrips. Equality to a particular global polynomial and
its small total-degree bound require explicit bounded polynomial provenance; a
local coefficient array alone does not certify that global claim.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction.GlobalNormalForm

open CompPoly ArkLib.ConfluentAlgebra

variable {E : Type*} [CommRing E] [BEq E] [LawfulBEq E]
variable {r N : ℕ}

/-- Inverse-shift the canonical box coefficient using no factorial divisions. -/
def recoverParameter (a : Fin r → E) (b : BoxAlgebra.Carrier r N E) : CMvPolynomial r E :=
  shift (fun i => -a i) b.val

private theorem box_zero_val : (0 : BoxAlgebra.Carrier r N E).val = 0 := by
  apply eq_iff_fromCMvPolynomial.mpr
  apply MvPolynomial.ext
  intro m
  change MvPolynomial.coeff m (fromCMvPolynomial (BoxTruncation.truncate N 0)) = _
  rw [BoxTruncation.coeff_semantics, CPoly.map_zero]
  simp


@[simp] theorem recoverParameter_zero (a : Fin r → E) :
    recoverParameter (N := N) a 0 = 0 := by
  rw [recoverParameter, box_zero_val]
  exact (shiftHom (fun i => -a i)).map_zero

/-- Local specialization recovers every canonical coefficient, without a degree claim. -/
@[simp] theorem parameterHom_recoverParameter (a : Fin r → E) (b : BoxAlgebra.Carrier r N E) :
    parameterHom N a (recoverParameter a b) = b := by
  change BoxAlgebra.reduce (shift a (shift (fun i => -a i) b.val)) = b
  have he := shift_neg_shift (fun i => -a i) b.val
  simp only [neg_neg] at he
  rw [he, BoxAlgebra.reduce_val]

/-- Inverse shifting cannot turn a nonzero canonical coefficient into zero. -/
theorem recoverParameter_eq_zero_iff (a : Fin r → E) (b : BoxAlgebra.Carrier r N E) :
    recoverParameter a b = 0 ↔ b = 0 := by
  constructor
  · intro hb
    have he := congrArg (parameterHom N a) hb
    simpa using he
  · rintro rfl
    exact recoverParameter_zero a

/-- A bounded polynomial is recovered exactly from its shifted box image. -/
theorem recoverParameter_parameterHom [Nontrivial E] (L : ℕ) (hNL : L < N) (a : Fin r → E)
    (p : CMvPolynomial r E) (hp : (fromCMvPolynomial p).totalDegree ≤ L) :
    recoverParameter a (parameterHom N a p) = p :=
  recover_shiftToBox N L hNL a p hp

variable [DecidableEq E] [Nontrivial E] [Fact (0 < N)]

/-- Recover the univariate coefficient array while preserving the distinguished last variable. -/
def recover (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) :
    CPolynomial (CMvPolynomial r E) :=
  CPolynomial.ofArray (p.val.map (recoverParameter a))

omit [Nontrivial E] [Fact (0 < N)] in
/-- Every output coefficient is the executed inverse shift of its stored local coefficient. -/
theorem coeff_recover (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) (i : ℕ) :
    (recover a p).coeff i = recoverParameter a (p.coeff i) := by
  change (CPolynomial.ofArray (p.val.map (recoverParameter a))).coeff i = _
  rw [CPolynomial.coeff_ofArray]
  change (p.val.map (recoverParameter a)).getD i 0 = recoverParameter a (p.val.getD i 0)
  simp only [Array.getD, Array.size_map]
  split_ifs <;> simp

omit [Nontrivial E] [Fact (0 < N)] in
/-- Recovery preserves the strict last-variable degree, including zero polynomials. -/
theorem degree_recover (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) :
    (recover a p).toPoly.degree = p.toPoly.degree := by
  have hs : (recover a p).toPoly.support = p.toPoly.support := by
    ext i
    simp only [Polynomial.mem_support_iff, ← CPolynomial.coeff_toPoly, coeff_recover]
    exact not_congr (recoverParameter_eq_zero_iff a (p.coeff i))
  exact congrArg (fun s : Finset ℕ => s.sup (fun n => (n : WithBot ℕ))) hs

/-- Re-specializing the recovered array gives the exact original local array. -/
theorem map_recover (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) :
    mapCoefficients (parameterHom N a) (recover a p) = p := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [toPoly_mapCoefficients, Polynomial.coeff_map]
  simp only [← CPolynomial.coeff_toPoly, coeff_recover, parameterHom_recoverParameter]

omit [Fact (0 < N)] in
/-- Bounded polynomial provenance supplies the converse roundtrip coefficient by coefficient. -/
theorem recover_map (L : ℕ) (hNL : L < N) (a : Fin r → E)
    (P : CPolynomial (CMvPolynomial r E))
    (hP : ∀ i, (fromCMvPolynomial (P.coeff i)).totalDegree ≤ L) :
    recover a (mapCoefficients (parameterHom N a) P) = P := by
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [← CPolynomial.coeff_toPoly, coeff_recover]
  have hc : (mapCoefficients (parameterHom N a) P).coeff i = parameterHom N a (P.coeff i) := by
    rw [CPolynomial.coeff_toPoly, toPoly_mapCoefficients, Polynomial.coeff_map,
      ← CPolynomial.coeff_toPoly]
  rw [hc, recoverParameter_parameterHom L hNL a _ (hP i), CPolynomial.coeff_toPoly]

/-- Return a flat global polynomial in the established parameter/last-variable order. -/
def recoverFlat (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) :
    CMvPolynomial (r + 1) E := flattenLast (recover a p)

/-- The actual recovered flat polynomial specializes exactly to the local coefficient array. -/
theorem localEquation_recoverFlat (a : Fin r → E) (p : CPolynomial (BoxAlgebra.Carrier r N E)) :
    localEquation N a (recoverFlat a p) = p := by
  rw [localEquation, recoverFlat, splitLast_flattenLast, map_recover]

omit [Fact (0 < N)] in
/-- Degree-bounded global provenance identifies the executed recovered polynomial exactly. -/
theorem recoverFlat_eq_of_provenance (L : ℕ) (hNL : L < N) (a : Fin r → E)
    (p : CPolynomial (BoxAlgebra.Carrier r N E)) (P : CPolynomial (CMvPolynomial r E))
    (hlocal : p = mapCoefficients (parameterHom N a) P)
    (hP : ∀ i, (fromCMvPolynomial (P.coeff i)).totalDegree ≤ L) :
    recoverFlat a p = flattenLast P := by
  rw [recoverFlat, hlocal, recover_map L hNL a P hP]

omit [Fact (0 < N)] in
/-- The small global degree follows from bounded provenance, not merely local recovery. -/
theorem totalDegree_recoverFlat_le_of_provenance (L : ℕ) (hNL : L < N) (a : Fin r → E)
    (p : CPolynomial (BoxAlgebra.Carrier r N E)) (P : CPolynomial (CMvPolynomial r E))
    (hlocal : p = mapCoefficients (parameterHom N a) P)
    (hcoeff : ∀ i, (fromCMvPolynomial (P.coeff i)).totalDegree ≤ L)
    (hdegree : (fromCMvPolynomial (flattenLast P)).totalDegree ≤ L) :
    (fromCMvPolynomial (recoverFlat a p)).totalDegree ≤ L := by
  rw [recoverFlat_eq_of_provenance L hNL a p P hlocal hcoeff]
  exact hdegree

variable (h : CPolynomial (BoxAlgebra.Carrier r N E)) [Fact h.monic]

/-- Canonical monic reduction followed by recovery retains the strict last-variable bound. -/
theorem z_degree_recoverFlat_lt (a : Fin r → E) (p : Representative h) :
    (splitLast (recoverFlat a p.val)).toPoly.degree < h.toPoly.degree := by
  rw [recoverFlat, splitLast_flattenLast, degree_recover]
  exact degree_representative_lt h Fact.out p

/-- Compute the cleared packet and recover its denominator and each numerator globally. -/
def recoverCleared {k : ℕ} (a : Fin r → E) (separant : Representative h)
    (coefficients : Fin k → Representative h) :
    CMvPolynomial (r + 1) E × (Fin k → CMvPolynomial (r + 1) E) :=
  let cleared := ClearedCoefficients.clear separant coefficients
  (recoverFlat a cleared.1.val, fun j => recoverFlat a (cleared.2 j).val)

/-- The recovered denominator specializes to the computed separant power exactly. -/
theorem localEquation_recoverCleared_denominator {k : ℕ} (a : Fin r → E)
    (separant : Representative h) (coefficients : Fin k → Representative h) :
    localEquation N a (recoverCleared h a separant coefficients).1 =
      (ClearedCoefficients.denominator k separant).val :=
  localEquation_recoverFlat a _

/-- Every recovered numerator specializes to the executed cleared product exactly. -/
theorem localEquation_recoverCleared_numerator {k : ℕ} (a : Fin r → E)
    (separant : Representative h) (coefficients : Fin k → Representative h) (j : Fin k) :
    localEquation N a ((recoverCleared h a separant coefficients).2 j) =
      (ClearedCoefficients.numerators separant coefficients j).val :=
  localEquation_recoverFlat a _

end CPoly.TaylorReconstruction.GlobalNormalForm
