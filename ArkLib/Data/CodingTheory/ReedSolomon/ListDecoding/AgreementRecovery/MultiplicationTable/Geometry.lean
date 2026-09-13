/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Recovery

/-! # Geometric meaning of descending multiplication-table coefficient vectors -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable

open Polynomial Polynomial.JetHornerMachine

variable {E A K : Type*} [Field E] [CommRing A] [Algebra E A] [Field K] {d : ℕ}

/-- A geometric point in a factor represents the descending specialized coefficient polynomial. -/
def Component.Represents (T : Table E d) (model : T.Model A) (phi : A →+* K)
    (c : Component E d) (p : K[X]) : Prop :=
  phi (model.decode c.identity) = 1 ∧
    coefficientPolynomial (c.coefficients.map (fun a => phi (model.decode a))) = p

/-- Specialization commutes with the actual descending Horner loop. -/
theorem specialize_horner (T : Table E d) (model : T.Model A) (phi : A →+* K)
    (cs : List (Fin d → E)) (a : E) (v : Fin d → E) :
    phi (model.decode (cs.foldl (fun acc c => a • acc + c) v)) =
      (cs.map (fun c => phi (model.decode c))).foldl
        (fun acc c => phi (algebraMap E A a) * acc + c) (phi (model.decode v)) := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
    rw [model.decode.map_add, model.decode.map_smul]
    simp only [map_add, Algebra.smul_def, map_mul]

/-- Polynomial evaluation uses exactly the same descending Horner orientation. -/
theorem eval_coefficientPolynomial_foldl (cs : List K) (a : K) :
    (coefficientPolynomial cs).eval a = cs.foldl (fun acc c => a * acc + c) 0 := by
  have aux : ∀ (cs : List K) (q : K[X]),
      (cs.foldl (fun p c => p * X + C c) q).eval a =
        cs.foldl (fun acc c => a * acc + c) (q.eval a) := by
    intro cs
    induction cs with
    | nil => intro q; rfl
    | cons c cs ih =>
      intro q
      simp only [List.foldl_cons, ih, eval_add, eval_mul, eval_X, eval_C, mul_comm]
  simpa only [coefficientPolynomial, eval_zero] using aux cs 0

/-- A represented polynomial evaluates to the specialization of the executable Horner result. -/
theorem Component.Represents.horner (T : Table E d) (model : T.Model A)
    (phi : A →+* K) (c : Component E d) (p : K[X]) (hp : c.Represents T model phi p)
    (a : E) :
    phi (model.decode (c.coefficients.foldl (fun acc b => a • acc + b) 0)) =
      p.eval (phi (algebraMap E A a)) := by
  rw [specialize_horner, ← hp.2, eval_coefficientPolynomial_foldl]
  simp

/-- Restriction preserves all represented values at each retained geometric point. -/
theorem Component.Represents.restrict (T : Table E d) (model : T.Model A)
    (phi : A →+* K) (c : Component E d) (p : K[X]) (hp : c.Represents T model phi p)
    (q : Fin d → E) (hq : phi (model.decode q) = 1) :
    (c.restrict T q).Represents T model phi p := by
  constructor
  · simpa only [Component.restrict, materialize_eq] using hq
  · change coefficientPolynomial
      (((c.restrict T q).coefficients).map (fun a => phi (model.decode a))) = p
    simpa only [Component.restrict, materialize_eq, List.map_map, Function.comp_def,
      model.decode_mul, map_mul, hq, one_mul] using hp.2

variable {F : Type*} [Field F] [DecidableEq E] [IsReduced A] {n : ℕ}

/-- Every represented geometric point follows an actual computed child, with the correct tag. -/
theorem splitAt_represents_complete (T : Table E d) (model : T.Model A)
    (phi : A →+* K) (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (c : Component E d) (i : Fin n) (p : K[X]) (hp : c.Represents T model phi p) :
    ∃ child ∈ splitAt T base domain received c i,
      child.2.Represents T model phi p ∧
        (child.1 = true ↔ p.eval (phi (algebraMap E A (base (domain i)))) =
          phi (algebraMap E A (base (received i)))) := by
  let e := T.mul c.identity
    (c.coefficients.foldl (fun acc a => base (domain i) • acc + a) 0 -
      base (received i) • c.identity)
  obtain ⟨x, hs, _⟩ := T.split?_success model e
  let out := T.splitData e x
  have hs' : T.split? e = some out := hs
  have he : phi (model.decode e) = 0 ↔
      p.eval (phi (algebraMap E A (base (domain i)))) =
        phi (algebraMap E A (base (received i))) := by
    simp only [e, model.decode_mul, map_mul, hp.1, one_mul, map_sub]
    rw [hp.horner T model phi c p, model.decode.map_smul, Algebra.smul_def,
      map_mul, hp.1, mul_one, sub_eq_zero]
  have hpart := T.split_geometric_partition model e out hs' phi
  by_cases hz : phi (model.decode e) = 0
  · let q := T.mul c.identity out.kernelIdentity
    have hq : phi (model.decode q) = 1 := by
      simp only [q, model.decode_mul, map_mul, hp.1, one_mul, hpart.1.mpr hz]
    refine ⟨(true, c.restrict T q), ?_, hp.restrict T model phi c p q hq, ?_⟩
    · change (true, c.restrict T q) ∈
        (match T.split? e with
        | none => []
        | some out => [(true, c.restrict T (T.mul c.identity out.kernelIdentity)),
            (false, c.restrict T (T.mul c.identity out.imageIdentity))])
      simp only [hs', q, List.mem_cons, true_or]
    · exact iff_of_true rfl (he.mp hz)
  · let q := T.mul c.identity out.imageIdentity
    have hq : phi (model.decode q) = 1 := by
      simp only [q, model.decode_mul, map_mul, hp.1, one_mul, hpart.2.mpr hz]
    refine ⟨(false, c.restrict T q), ?_, hp.restrict T model phi c p q hq, ?_⟩
    · change (false, c.restrict T q) ∈
        (match T.split? e with
        | none => []
        | some out => [(true, c.restrict T (T.mul c.identity out.kernelIdentity)),
            (false, c.restrict T (T.mul c.identity out.imageIdentity))])
      simp [hs', q]
    · exact iff_of_false Bool.false_ne_true (fun h => hz (he.mpr h))

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
