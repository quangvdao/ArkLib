/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Geometry
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput

/-! # Exact multiplication-table recovery under geometric constructor coverage -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

open Polynomial Polynomial.JetHornerMachine SampleInterpolation

variable {F E A K : Type*} [Field F] [DecidableEq F] [Field E] [DecidableEq E]
  [CommRing A] [Algebra E A] [IsReduced A] [Field K] {d n : ℕ}

/-- A supplied component has a geometric point representing the base-field message. The point
and model are proof-only; neither is consulted by the executable recovery procedure. -/
def RepresentedBy (T : Table E d) (model : T.Model A) (base : F →+* E)
    (families : List (Component E d)) (p : F[X]) : Prop :=
  ∃ c ∈ families, ∃ phi : A →+* K,
    c.Represents T model phi (p.map ((phi.comp (algebraMap E A)).comp base))

/-- A geometric point with enough agreements reaches an actual stopped interpolation sample. -/
theorem exists_stopped_sample (T : Table E d) (model : T.Model A) (phi : A →+* K)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k threshold : ℕ) (hkt : k ≤ threshold) (c : Component E d) (p : F[X])
    (hp : c.Represents T model phi (p.map ((phi.comp (algebraMap E A)).comp base)))
    (hag : threshold ≤ Code.agree (evalOnPoints domain p) received) :
    ∃ out ∈ ComponentScan.scan (fun c => decide (c.identity ≠ 0))
      (splitAt T base domain received) k (List.ofFn (@id (Fin n))) ⟨c, []⟩,
      ∀ i ∈ out.positions, p.eval (domain i) = received i := by
  classical
  let embedding := (phi.comp (algebraMap E A)).comp base
  let point : Component E d → Unit → Prop := fun c _ =>
    c.Represents T model phi (p.map embedding)
  let good : Unit → Fin n → Prop := fun _ i => p.eval (domain i) = received i
  have halive : ∀ c θ, point c θ → decide (c.identity ≠ 0) = true := by
    intro c θ hc
    apply decide_eq_true
    intro hz
    have h := hc.1
    simp only [hz, map_zero] at h
    exact zero_ne_one h
  have hstep : ∀ c i θ, point c θ → ∃ child ∈ splitAt T base domain received c i,
      point child.2 θ ∧ (child.1 = true ↔ good θ i) := by
    intro c i θ hc
    obtain ⟨child, hchild, hpchild, htag⟩ :=
      splitAt_represents_complete T model phi base domain received c i (p.map embedding) hc
    refine ⟨child, hchild, hpchild, ?_⟩
    rw [htag, Polynomial.eval_map]
    change p.eval₂ embedding (embedding (domain i)) = embedding (received i) ↔ _
    rw [Polynomial.eval₂_at_apply]
    exact embedding.injective.eq_iff
  have hcount : (List.ofFn (@id (Fin n))).countP (fun i => decide (good () i)) =
      Code.agree (evalOnPoints domain p) received := by
    have hcard := (List.nodup_ofFn.mpr
      (Function.injective_id : Function.Injective (@id (Fin n)))).card_eq_countP
      (P := good ())
    have huniv : (List.ofFn (@id (Fin n))).toFinset = Finset.univ := by ext i; simp
    rw [huniv] at hcard
    rw [← hcard]
    rfl
  obtain ⟨out, hout, _, hgood⟩ := ComponentScan.point_complete
    (fun c : Component E d => decide (c.identity ≠ 0))
    (splitAt T base domain received) point good
    halive hstep k (List.ofFn (@id (Fin n))) ⟨c, []⟩ () hp (by simp)
    (by simpa [hcount] using hkt.trans hag)
  exact ⟨out, hout, hgood⟩

/-- Every qualifying geometrically represented message survives interpolation and checking. -/
theorem exists_mem_recoverAgreement_of_representedBy (T : Table E d) (model : T.Model A)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k threshold : ℕ) (hkt : k ≤ threshold) (families : List (Component E d))
    (p : F[X]) (hd : p.degree < k)
    (hag : threshold ≤ Code.agree (evalOnPoints domain p) received)
    (hp : RepresentedBy (K := K) T model base families p) :
    ∃ cs ∈ recoverAgreement T base domain received k threshold families,
      coefficientPolynomial cs = p := by
  obtain ⟨c, hc, phi, hp⟩ := hp
  obtain ⟨out, hout, hgood⟩ :=
    exists_stopped_sample T model phi base domain received k threshold hkt c p hp hag
  have hblock : out ∈ blocks T base domain received k families := by
    simp only [blocks, ComponentScan.scanMany_eq, List.flatMap_map, List.mem_flatMap]
    exact ⟨c, hc, hout⟩
  have hcard := stopped_card T base domain received k families out hblock
  have hinterp := interpolate_eq_of_agrees_on domain received k out.positions.toFinset
    hcard p hd (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood i (List.mem_toFinset.mp hi)⟩)
  have hpoly : coefficientPolynomial
      (sampleCandidate domain received k out.positions.toFinset) = p :=
    (sampleCandidate_polynomial domain received k out.positions.toFinset).trans hinterp
  have hchecked := checkedCandidate_of_agreement domain received k threshold
    out.positions.toFinset hcard (by simpa only [hpoly] using hag)
  refine ⟨sampleCandidate domain received k out.positions.toFinset, ?_, hpoly⟩
  simp only [recoverAgreement, List.mem_dedup]
  exact List.mem_filterMap.mpr ⟨out, hblock, hchecked⟩

/-- Genuine geometric constructor coverage yields the shared exact-output contract. This does
not assume an already decoded list, an interpolation sample, or a successful scanner trace. -/
theorem recoverAgreement_exact_of_coverage (T : Table E d) (model : T.Model A)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k threshold : ℕ) (hkt : k ≤ threshold) (families : List (Component E d))
    (hcover : ∀ p : F[X], p.degree < k →
      threshold ≤ Code.agree (evalOnPoints domain p) received →
        RepresentedBy (K := K) T model base families p) :
    ExactOutput domain received k threshold
      (recoverAgreement T base domain received k threshold families) := by
  apply exactOutput_of_sound_complete
  · exact List.nodup_dedup _
  · exact mem_recoverAgreement_properties T base domain received k threshold families
  · intro p hd ha
    exact exists_mem_recoverAgreement_of_representedBy T model base domain received
      k threshold hkt families p hd ha (hcover p hd ha)

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
