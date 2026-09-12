/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Success

/-! # Totality and reconstruction of tree refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
open Polynomial.FunctionFieldAlgorithms Polynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition
open CPolynomial.BatchRemainder
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem factorProduct_append (a b : List (ℕ × CPolynomial F)) :
    factorProduct (a ++ b) = factorProduct a * factorProduct b := by
  simp [factorProduct, List.map_append, List.prod_append]

private theorem split_factorProduct (left : CPolynomial F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    factorProduct (pieces.map fun z => (z.1, gcdFactor z.2 left)) *
      factorProduct (pieces.map fun z => (z.1, gcdComplement z.2 left)) =
        factorProduct pieces := by
  induction pieces with
  | nil => simp [factorProduct]
  | cons z rest ih =>
    simp only [List.map_cons]
    rw [factorProduct, factorProduct, factorProduct]
    simp only [List.map_cons, List.prod_cons]
    simp only [List.map_map, Function.comp_def]
    rw [show gcdFactor z.2 left ^ z.1 *
          (List.map (fun z => (gcdFactor z.2 left) ^ z.1) rest).prod *
          (gcdComplement z.2 left ^ z.1 *
            (List.map (fun z => (gcdComplement z.2 left) ^ z.1) rest).prod) =
        (gcdFactor z.2 left * gcdComplement z.2 left) ^ z.1 *
          ((List.map (fun z => (gcdFactor z.2 left) ^ z.1) rest).prod *
            (List.map (fun z => (gcdComplement z.2 left) ^ z.1) rest).prod) by
      rw [mul_pow]; ring]
    rw [gcdFactor_mul_gcdComplement
      ((toPoly_eq_zero_iff z.2).not.mp
        ((monic_toPoly_iff z.2).mp (hm z (by simp))).ne_zero)]
    have ih' := ih (fun a ha => hm a (by simp [ha]))
    simp only [factorProduct, List.map_map, Function.comp_def] at ih'
    rw [ih']

/-- Batched tagged routing preserves the weighted product, not only the unweighted support. -/
theorem routeTagged_factorProduct_exact
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    factorProduct ((routeTagged M D t pieces).map fun z => (z.1, z.2.2)) =
      factorProduct pieces := by
  induction t generalizing pieces with
  | leaf h =>
    simp only [routeTagged, List.map_map, Function.comp_def]
    have hfun : (fun x : ℕ × CPolynomial F => (x.1, x.2)) = id := by
      funext x
      exact Prod.eta x
    rw [hfun, List.map_id]
    exact factorProduct_pruneTagged pieces
  | node h left right ihl ihr =>
    have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
      fun z hz => hm z (List.mem_filter.mp hz).1
    rw [routeTagged, List.map_append, factorProduct_append,
      batchSplitTagged_eq M D _ _ hp]
    simp only [List.map_map, Function.comp_def]
    rw [ihl _ (fun z hz => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact gcdFactor_monic ((toPoly_eq_zero_iff a.2).not.mp
        ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)),
      ihr _ (fun z hz => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
        exact gcdComplement_monic (hp a ha))]
    exact (split_factorProduct left.product (pruneTagged pieces) hp).trans
      (by rw [factorProduct_pruneTagged])

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
