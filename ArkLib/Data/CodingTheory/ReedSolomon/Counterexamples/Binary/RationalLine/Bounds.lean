/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# The rational-line agreement contract

The property records exact singleton agreement lists and simultaneous source-agreement
bounds for the same two words and the same explicit family of explaining polynomials.
It concerns this line only, not every received word of a code.
-/

namespace ReedSolomon.Binary

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Exact singleton agreement lists and bounds on common source agreement.
The parameter `k` is the message dimension and `A` is the agreement threshold. -/
structure RationalLineBounds (k A : ℕ) (f g : F → F) (p : F → F[X]) : Prop where
  /-- The full list of qualifying polynomials is the singleton containing the explanation. -/
  exactList : ∀ (z : F) (P : F[X]),
    (P.degree < k ∧ A ≤ Code.agree (fun x ↦ f x + z * g x) (fun x ↦ P.eval x)) ↔ P = p z
  /-- The explanation has exactly `A` agreements, with no extra coordinate. -/
  exactAgreement : ∀ z,
    Code.agree (fun x ↦ f x + z * g x) (fun x ↦ (p z).eval x) = A
  /-- Every pair of message polynomials has at most `k + 1` common source agreements. -/
  commonUpper : ∀ P Q : F[X], P.degree < k → Q.degree < k →
    (commonPolynomialAgreementSet (Function.Embedding.refl F) f g P Q).card ≤ k + 1
  /-- Some pair of message polynomials attains at least `k` common source agreements. -/
  commonLower : ∃ P Q : F[X], P.degree < k ∧ Q.degree < k ∧
    k ≤ (commonPolynomialAgreementSet (Function.Embedding.refl F) f g P Q).card

namespace RationalLineBounds

variable {k A : ℕ} {f g : F → F} {p : F → F[X]}

/-- Each explicit explanation is a message polynomial. -/
theorem degree_lt (h : RationalLineBounds k A f g p) (z : F) : (p z).degree < k :=
  ((h.exactList z (p z)).mpr rfl).1

/-- No message polynomial exceeds the agreement attained by the explicit explanation. -/
theorem agree_le (h : RationalLineBounds k A f g p) (z : F) (P : F[X])
    (hP : P.degree < k) :
    Code.agree (fun x ↦ f x + z * g x) (fun x ↦ P.eval x) ≤ A := by
  by_cases ha : A ≤ Code.agree (fun x ↦ f x + z * g x) (fun x ↦ P.eval x)
  · rw [(h.exactList z P).mp ⟨hP, ha⟩, h.exactAgreement]
  · exact (lt_of_not_ge ha).le

/-- The explicit explanation is the unique polynomial with at least `A` agreements. -/
theorem existsUnique (h : RationalLineBounds k A f g p) (z : F) :
    ∃! P : F[X], P.degree < k ∧
      A ≤ Code.agree (fun x ↦ f x + z * g x) (fun x ↦ P.eval x) := by
  exact ⟨p z, (h.exactList z (p z)).mpr rfl, fun P hP ↦ (h.exactList z P).mp hP⟩

end RationalLineBounds

end ReedSolomon.Binary
