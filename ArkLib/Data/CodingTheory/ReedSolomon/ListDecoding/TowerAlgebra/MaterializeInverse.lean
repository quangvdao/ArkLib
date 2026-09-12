/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Inverse

/-!
# Materializing inverses in the decoder tower algebra

This is the decoder-facing adapter for constructive inversion.  It keeps the API entirely in the
same `TowerRepresentation` used by preprocessing and D5 branching: callers provide a tower and a
(reduced) nested polynomial, and receive either a canonical nested inverse representative or an
explicit `none`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The quotient-level statement that `v` is a two-sided inverse of `u` in the tower represented by
`r`.  Equality is expressed through the repository's executable canonical reducer, rather than via
an auxiliary matrix or geometric evaluation tuple. -/
def IsMaterializedInverse (r : TowerRepresentation (F := F))
    (u v : CPolynomial (CPolynomial F)) : Prop :=
  TowerRepresentation.reduceElement r.modulus r.fiber (u * v) =
      TowerRepresentation.reduceElement r.modulus r.fiber 1 ∧
    TowerRepresentation.reduceElement r.modulus r.fiber (v * u) =
      TowerRepresentation.reduceElement r.modulus r.fiber 1

/-- Compute an inverse representative modulo the full tower ideal.

The input is expected to be the canonical reduced representative maintained by the decoder.  The
implementation computes the inverse internally; no inverse witness, multiplication matrix, or
evaluation tuple is supplied by the caller. -/
def materializeInverse (r : TowerRepresentation (F := F))
    (u : CPolynomial (CPolynomial F)) : Option (CPolynomial (CPolynomial F)) :=
  inverseRepresentative? r.modulus r.fiber u

/-- A successful materialization is a genuine two-sided inverse in the represented quotient. -/
theorem materializeInverse_sound
    (r : TowerRepresentation (F := F)) (u v : CPolynomial (CPolynomial F))
    (hv : materializeInverse r u = some v) : IsMaterializedInverse r u v := by
  exact ⟨inverseRepresentative?_mul_eq_one r.modulus r.fiber u v hv,
    inverseRepresentative?_mul_eq_one_right r.modulus r.fiber u v hv⟩

/-- In particular, successful materialization satisfies left multiplication correctness. -/
theorem materializeInverse_mul_eq_one
    (r : TowerRepresentation (F := F)) (u v : CPolynomial (CPolynomial F))
    (hv : materializeInverse r u = some v) :
    TowerRepresentation.reduceElement r.modulus r.fiber (u * v) =
      TowerRepresentation.reduceElement r.modulus r.fiber 1 :=
  (materializeInverse_sound r u v hv).1

/-- Successful materialization also satisfies right multiplication correctness. -/
theorem materializeInverse_mul_eq_one_right
    (r : TowerRepresentation (F := F)) (u v : CPolynomial (CPolynomial F))
    (hv : materializeInverse r u = some v) :
    TowerRepresentation.reduceElement r.modulus r.fiber (v * u) =
      TowerRepresentation.reduceElement r.modulus r.fiber 1 :=
  (materializeInverse_sound r u v hv).2

/-- Returned inverses obey exactly the same bounded-degree canonical-slice invariant as every
other decoder tower element. -/
theorem materializeInverse_elementReduced
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (u v : CPolynomial (CPolynomial F)) (hv : materializeInverse r u = some v) :
    TowerRepresentation.ElementReduced r.modulus r.fiber v := by
  exact inverseRepresentative?_elementReduced hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hv

/-- Materialization depends only on the supplied reduced representative: equal canonical inputs
produce exactly the same executable result. -/
theorem materializeInverse_congr
    (r : TowerRepresentation (F := F))
    {u u' : CPolynomial (CPolynomial F)} (hu : u = u') :
    materializeInverse r u = materializeInverse r u' := by
  subst u'
  rfl

end ReedSolomon.ListDecoding.TowerAlgebra
