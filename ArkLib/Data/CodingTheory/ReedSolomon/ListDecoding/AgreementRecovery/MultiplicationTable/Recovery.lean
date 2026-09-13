/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Correctness
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.ComponentScan
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SampleInterpolation

/-! # Multiplication-table components in the shared agreement scanner -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

open SampleInterpolation Polynomial.JetHornerMachine

variable {F E : Type*} [Field F] [DecidableEq F] [Field E] [DecidableEq E]
  {d n : ℕ}

/-- A factor identity and coefficient coordinates in the original ambient table basis. -/
structure Component (E : Type*) (d : ℕ) where
  identity : Fin d → E
  coefficients : List (Fin d → E)

/-- Materialize coordinates once instead of retaining nested multiplication closures. -/
def materialize (v : Fin d → E) : Fin d → E :=
  let coordinates := Array.ofFn v
  fun i => coordinates[i.val]'(by simp [coordinates])

omit [Field E] [DecidableEq E] in
@[simp] theorem materialize_eq (v : Fin d → E) : materialize v = v := by
  funext i
  simp [materialize]

/-- Restrict all represented values using multiplication by the child identity. -/
def Component.restrict (T : Table E d) (c : Component E d) (p : Fin d → E) :
    Component E d :=
  let p := materialize p
  ⟨p, c.coefficients.map (fun a => materialize (T.mul p a))⟩

/-- Split the residual inside the current factor; zero identities are discarded by the scanner. -/
def splitAt (T : Table E d) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (c : Component E d) (i : Fin n) :
    List (Bool × Component E d) :=
  let residual := c.coefficients.foldl (fun acc a => base (domain i) • acc + a) 0 -
    base (received i) • c.identity
  match T.split? (T.mul c.identity residual) with
  | none => []
  | some out =>
    [(true, c.restrict T (T.mul c.identity out.kernelIdentity)),
     (false, c.restrict T (T.mul c.identity out.imageIdentity))]

/-- Use the existing scanner, including its distinct-position histories and stopping rule. -/
def blocks (T : Table E d) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k : ℕ) (families : List (Component E d)) :=
  ComponentScan.scanMany (fun c => decide (c.identity ≠ 0))
    (splitAt T base domain received) k (List.ofFn (@id (Fin n)))
    (families.map fun c => ⟨c, []⟩)

/-- Reuse base-field interpolation, the full-word check, and fixed-width deduplication. -/
def recoverAgreement (T : Table E d) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (families : List (Component E d)) : List (List F) :=
  ((blocks T base domain received k families).filterMap fun block =>
    checkedCandidate domain received k A block.positions.toFinset).dedup

omit [DecidableEq F] in
/-- Every stopped table component carries exactly the requested number of distinct positions. -/
theorem stopped_card (T : Table E d) (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k : ℕ) (families : List (Component E d))
    (out : ComponentScan.Block (Component E d) (Fin n))
    (hout : out ∈ blocks T base domain received k families) :
    out.positions.toFinset.card = k := by
  simp only [blocks, ComponentScan.scanMany_eq, List.flatMap_map,
    List.mem_flatMap] at hout
  obtain ⟨c, _, hout⟩ := hout
  have hlen := ComponentScan.positions_length (fun c => decide (c.identity ≠ 0))
    (splitAt T base domain received) k _ ⟨c, []⟩ out (by simp) hout
  have hsub := ComponentScan.positions_sublist (fun c => decide (c.identity ≠ 0))
    (splitAt T base domain received) k _ ⟨c, []⟩ out hout
  have hnodup : out.positions.Nodup := hsub.nodup (by
    simpa using (List.nodup_ofFn.mpr (Function.injective_id : Function.Injective (@id (Fin n)))))
  rw [List.toFinset_card_of_nodup hnodup, hlen]

/-- Full-word soundness does not need a geometric coverage assumption or a model oracle. -/
theorem mem_recoverAgreement_properties (T : Table E d) (base : F →+* E)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (families : List (Component E d)) (cs : List F)
    (hcs : cs ∈ recoverAgreement T base domain received k A families) :
    cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  simp only [recoverAgreement, List.mem_dedup, List.mem_filterMap] at hcs
  obtain ⟨block, hblock, hc⟩ := hcs
  have hp := checkedCandidate_properties domain received k A block.positions.toFinset
    (stopped_card T base domain received k families block hblock) cs hc
  exact ⟨hp.1, hp.2.2⟩

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
