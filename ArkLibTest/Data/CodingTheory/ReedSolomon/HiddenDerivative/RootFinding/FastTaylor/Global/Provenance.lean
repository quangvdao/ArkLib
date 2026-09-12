/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Global.Provenance

/-! A literal first-order differential recurrence over any commutative rational algebra. -/

namespace ClearedProvenanceTests

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.FastTaylor.Global

private noncomputable def equation : DifferentialPolynomial ℚ 1 := X (some 1) - X (some 0)

private theorem separant_one : initialJetSeparant 0 equation = 1 := by
  simp [initialJetSeparant, equation, separant]

private theorem residual_intercept :
    (optionEquivLeft ℚ (Fin 2) (universalTaylorResidual 2 0 equation)).coeff 1 = -X 1 := by
  simp [equation, universalTaylorResidual, optionEquivLeft_universalTaylorJet,
    universalTaylorPolynomial, Fin.sum_univ_two]

/-- This checks the concrete literal numerator at a later index, with a target that is
only a commutative ring. In particular the initial coefficient may be nilpotent. -/
example {A : Type*} [CommRing A] (f : ℚ →+* A) (e : A) :
    let φ := eval₂Hom f (fun _ : Fin 2 => e)
    φ (commonTaylorNumerator 0 equation 3 (2 : Fin 3)) = f (1 / 2) * e := by
  let φ := eval₂Hom f (fun _ : Fin 2 => e)
  let c : ℕ → A := fun l => if l = 2 then f (1 / 2) * e else e
  have hinit : ∀ l < 3, ∀ hl : l < 1 + 1, c l = φ (X ⟨l, hl⟩) := by
    intro l _ hl
    simp [c, φ, show l ≠ 2 by omega]
  have hbin : ∀ l < 3, 1 < l → (l.choose 1 : ℚ) ≠ 0 := by
    intro l hl hr
    have he : l = 2 := by omega
    subst l
    norm_num
  have hres : ∀ l < 3, 1 < l →
      eval₂ (φ.comp C) (fun i : Fin l => c i.val)
        ((optionEquivLeft ℚ (Fin l) (universalTaylorResidual l 0 equation)).coeff (l - 1)) +
        ((φ.comp C) (l.choose 1 : ℚ) * c l) * φ (initialJetSeparant 0 equation) = 0 := by
    intro l hl hr
    have he : l = 2 := by omega
    subst l
    rw [show 2 - 1 = 1 from rfl, residual_intercept, separant_one]
    suffices -e + f 2 * (f (2⁻¹) * e) = 0 by simpa [φ, c] using this
    have hinv : f 2 * f (2⁻¹) = 1 := by
      rw [← map_mul]
      norm_num
    rw [← mul_assoc, hinv, one_mul, neg_add_cancel]
  have ht := map_commonTaylorNumerator_two_mul 0 equation φ c 3 hinit hbin hres (2 : Fin 3)
  simpa [φ, c, separant_one] using ht

end ClearedProvenanceTests
