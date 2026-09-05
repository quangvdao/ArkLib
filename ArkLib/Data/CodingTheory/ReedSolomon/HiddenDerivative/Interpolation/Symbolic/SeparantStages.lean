/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.BandCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix


/-!
# Symbolic interpolation certificates and actual derivative stages

The existing interpolation certificate supplies the concrete nonzero symbolic equation,
height bound, and differential identities needed by separant descent. Its stage list
retains actual derivative orders and individual exponent budgets.
-/

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open Polynomial MvPolynomial SymbolicSeparantChain

universe u

variable {F : Type u} [Field F] {n A k ν d : ℕ}
  {domain : Fin n ↪ F} {f g : Fin n → F}

/-- A symbolic certificate's equation is nonzero before any challenge specialization. -/
theorem Certificate.nonzero (cert : Certificate.{u, u} F A k ν d domain f g) : cert.Q ≠ 0 := by
  intro hzero
  have h := (cert.specialization_sound (RingHom.id F) 0).1
  rw [hzero, map_zero] at h
  exact h rfl

/-- The support bound in the interpolation certificate bounds the actual symbolic jet weight. -/
theorem Certificate.jetWeight_le (cert : Certificate.{u, u} F A k ν d domain f g) :
    jetWeight cert.Q ≤ ν := by
  apply Finset.sup_le_iff.mpr
  intro u hu
  have h := cert.totalJetDegree_le u hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.weight_apply,
    Finsupp.sum_fintype] using h

/-- Strict coefficient height gives the integral terminal-obstruction budget. -/
theorem Certificate.challengeHeight_le (cert : Certificate.{u, u} F A k ν d domain f g) :
    ∀ u, (MvPolynomial.coeff u cert.Q).natDegree ≤ 338 * ν - 1 :=
  fun u ↦ Nat.le_sub_one_of_lt (cert.challengeDegree_lt u)

/-- Construct actual symbolic derivative stages directly from a proved interpolation certificate. -/
theorem Certificate.exists_separant_chain (cert : Certificate.{u, u} F A k ν d domain f g)
    (hchar : ringChar F = 0 ∨ ν < ringChar F) :
    ∃ stages terminal, Chain cert.Q stages terminal := by
  apply exists_symbolic_chain cert.Q cert.nonzero
  exact hchar.imp_right (fun h ↦ cert.jetWeight_le.trans_lt h)

/-- One height-bounded exceptional set gives regular-stage coverage of every close
polynomial, uniformly over every extension field and every challenge outside the set. -/
theorem Certificate.exists_exceptional_stage_coverage
    (cert : Certificate.{u, u} F A k ν d domain f g)
    {stages : List (Stage F[X] d)} {terminal : DifferentialPolynomial F[X] d}
    (hc : Chain cert.Q stages terminal)
    {E : Type u} [Field E] (iota : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ 338 * ν - 1 ∧
      ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
        P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (iota (domain i)) = iota (f i) + z * iota (g i)) →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1)
              stage.2) P ≠ 0 := by
  obtain ⟨exceptional, hcard, hcover⟩ :=
    hc.exists_exceptional_regular_coverage cert.challengeHeight_le iota
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz indices P hdegree hcard hagree
  exact hcover z hz P ((cert.specialization_sound iota z).2.2 indices P
    hdegree hcard hagree)

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
