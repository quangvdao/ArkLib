/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity

/-! Public-import checks for the saturation multiplicity interface. -/

namespace NormalizationMultiplicityTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization NormalizationMultiplicity

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example (H : CBivariate (ZMod 3)) (step : Saturation (ZMod 3))
    (hH : H ≠ 0) (hexec : saturate 7 H = .ok step) :
    step.visible ≠ 0 ∧ step.residual ≠ 0 :=
  saturate_outputs_ne_zero 7 H step hH hexec

example (H : CBivariate (ZMod 3)) (step : Saturation (ZMod 3))
    (hH : H ≠ 0) (hdegree : (CBivariate.toPoly H).natDegree ≤ 7)
    (hexec : saturate 7 H = .ok step)
    (hpartialY : CBivariate.partialDerivY step.residual = 0)
    (hpos : 0 < (CBivariate.toPoly step.residual).natDegree) : 3 ≤ 7 :=
  p_le_ell_of_saturated_residual 3 7 H step hH hdegree hexec hpartialY hpos

example (H : CBivariate (ZMod 3)) (hH : H ≠ 0)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ 7) :
    localized H ∣ localizedRadical H ^ 7 :=
  localized_dvd_localizedRadical_pow 7 H hH hdegree

example (H : CBivariate (ZMod 3)) (step : Saturation (ZMod 3))
    (hexec : saturate 7 H = .ok step) :
    Associated (localized step.visible * localized step.common) (localized H) ∧
      Associated (localized step.residual * localized step.removed) (localized H) :=
  saturate_localized_identities 7 H step hexec

example (inverse : ZMod 3 → ZMod 3) (H : CBivariate (ZMod 3))
    (step : Saturation (ZMod 3)) (hexec : saturate 7 H = .ok step)
    (hH : H ≠ 0) (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree ≤ 7)
    (hinverse : 3 ≤ 7 → ∀ a, inverse a ^ 3 = a) :
    SaturationCertificate 3 7 inverse H step :=
  saturationCertificate 3 7 inverse H step hexec hH hprimitive hdegree hinverse

#print axioms SaturationCertificate
#print axioms saturate_provenance
#print axioms saturate_outputs_dvd
#print axioms normalizedFactor_multiplicity_le
#print axioms polynomial_dvd_radical_pow_natDegree
#print axioms localized_dvd_localizedRadical_pow
#print axioms saturate_localized_identities
#print axioms saturate_localized_classification
#print axioms saturate_residual_partials
#print axioms p_le_ell_of_saturated_residual
#print axioms saturationCertificate
#print axioms SaturationCertificate.input_dvd_radical_pow
#print axioms SaturationCertificate.outputs_dvd

end NormalizationMultiplicityTests
