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

private theorem combinePairs_nonempty (M : MulContext F)
    (trees : List (BatchRemainder.Tree F)) (hne : trees ≠ []) :
    BatchRemainder.combinePairs M trees ≠ [] := by
  cases trees with
  | nil => contradiction
  | cons a rest => cases rest <;> simp [BatchRemainder.combinePairs]

private theorem combinePairs_length_le (M : MulContext F)
    (trees : List (BatchRemainder.Tree F)) :
    (BatchRemainder.combinePairs M trees).length ≤ trees.length := by
  match trees with
  | [] => simp [BatchRemainder.combinePairs]
  | [a] => simp [BatchRemainder.combinePairs]
  | a :: b :: rest =>
      simp only [BatchRemainder.combinePairs, List.length_cons]
      have hle := combinePairs_length_le M rest
      omega

private theorem combinePairs_length_lt (M : MulContext F)
    (trees : List (BatchRemainder.Tree F)) (hlt : 1 < trees.length) :
    (BatchRemainder.combinePairs M trees).length < trees.length := by
  cases trees with
  | nil => simp at hlt
  | cons a rest =>
      cases rest with
      | nil => simp at hlt
      | cons b rest =>
          simp only [BatchRemainder.combinePairs, List.length_cons]
          have hle := combinePairs_length_le M rest
          omega

private theorem buildForest_singleton (M : MulContext F) (fuel : ℕ)
    (tree : BatchRemainder.Tree F) :
    BatchRemainder.buildForest M fuel [tree] = [tree] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [BatchRemainder.buildForest, BatchRemainder.combinePairs]
      exact ih

private theorem buildForest_eq_singleton_of_nonempty_of_length_le
    (M : MulContext F) (fuel : ℕ) (trees : List (BatchRemainder.Tree F))
    (hne : trees ≠ []) (hle : trees.length ≤ fuel + 1) :
    ∃ tree, BatchRemainder.buildForest M fuel trees = [tree] := by
  induction fuel generalizing trees with
  | zero =>
      have hlen : trees.length = 1 := by
        have hpos : 0 < trees.length :=
          Nat.pos_of_ne_zero (fun hz => hne (by simpa using hz))
        omega
      obtain ⟨tree, rfl⟩ := List.length_eq_one_iff.mp hlen
      exact ⟨tree, rfl⟩
  | succ fuel ih =>
      by_cases hone : trees.length = 1
      · obtain ⟨tree, rfl⟩ := List.length_eq_one_iff.mp hone
        exact ⟨tree, buildForest_singleton M _ tree⟩
      · have hlt : 1 < trees.length := by
          have hpos : 0 < trees.length :=
            Nat.pos_of_ne_zero (fun hz => hne (by simpa using hz))
          omega
        have hcne := combinePairs_nonempty M trees hne
        have hclt := combinePairs_length_lt M trees hlt
        have hcle : (BatchRemainder.combinePairs M trees).length ≤ fuel + 1 := by omega
        obtain ⟨tree, htree⟩ := ih _ hcne hcle
        exact ⟨tree, by simpa only [BatchRemainder.buildForest] using htree⟩

private theorem build_eq_singleton_of_nonempty (M : MulContext F)
    (moduli : List (CPolynomial F)) (hne : moduli ≠ []) :
    ∃ tree, BatchRemainder.build M moduli = [tree] := by
  apply buildForest_eq_singleton_of_nonempty_of_length_le
  · simpa using hne
  · simp

private theorem destinationLabel?_exists_of_mem
    (recursive : List (ℕ × CPolynomial F)) (a : ℕ) (q : CPolynomial F)
    (hmem : (a, q) ∈ recursive) :
    ∃ r, destinationLabel? recursive q = some r := by
  unfold destinationLabel?
  cases hfind : recursive.find? fun z => z.2 == q with
  | none =>
      have hn := (List.find?_eq_none.mp hfind) (a, q) hmem
      simp at hn
  | some z =>
      exact ⟨z.1, by simp⟩

private theorem labelIntersections_exists
    (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (hdest : ∀ z ∈ routed, ∃ a, (a, z.2.1) ∈ recursive) :
    ∃ mixed, labelIntersections p recursive routed = some mixed := by
  induction routed with
  | nil => exact ⟨[], rfl⟩
  | cons z rest ih =>
    obtain ⟨a, ha⟩ := hdest z (by simp)
    obtain ⟨label, hlabel⟩ :=
      destinationLabel?_exists_of_mem recursive a z.2.1 ha
    obtain ⟨tail, htail⟩ := ih (fun b hb => hdest b (by simp [hb]))
    refine ⟨(z.1 + p * label, z.2.2) :: tail, ?_⟩
    unfold labelIntersections at htail ⊢
    simp only [List.mapM_cons, hlabel]
    rw [htail]
    rfl

private theorem routeTagged_leaf_mem
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) :
    ∀ z ∈ routeTagged M D t pieces, z.2.1 ∈ t.leaves := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    simp [BatchRemainder.Tree.leaves]
  | node h left right ihl ihr =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ (ihl _ z hz)
    · exact List.mem_append_right _ (ihr _ z hz)

private theorem labelIntersections_refineRoot_exists
    (p : ℕ) (M : MulContext F) (D : ModContext F)
    (t : BatchRemainder.Tree F) (strata recursive : List (ℕ × CPolynomial F))
    (hleaves : t.leaves = recursive.map Prod.snd) :
    ∃ mixed, labelIntersections p recursive (refineRoot M D t strata).1 = some mixed := by
  apply labelIntersections_exists
  intro z hz
  have hleaf := routeTagged_leaf_mem M D t _ z hz
  rw [hleaves] at hleaf
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hleaf
  rcases a with ⟨label, q⟩
  simp only at heq
  subst q
  exact ⟨label, ha⟩

private theorem routeTagged_piece_monic
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    ∀ z ∈ routeTagged M D t pieces, z.2.2.monic := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hm a (List.mem_filter.mp ha).1
  | node h left right ihl ihr =>
    have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
      fun z hz => hm z (List.mem_filter.mp hz).1
    rw [routeTagged, batchSplitTagged_eq M D _ _ hp]
    simp only [List.map_map, Function.comp_def]
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · apply ihl _ (fun a ha => ?_) z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact gcdFactor_monic ((toPoly_eq_zero_iff b.2).not.mp
        ((monic_toPoly_iff b.2).mp (hp b hb)).ne_zero)
    · apply ihr _ (fun a ha => ?_) z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact gcdComplement_monic (hp b hb)

private theorem refineRoot_routed_monic
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (strata : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ strata, z.2.monic) :
    ∀ z ∈ (refineRoot M D t strata).1, z.2.2.monic := by
  have hp : ∀ z ∈ pruneTagged strata, z.2.monic :=
    fun z hz => hm z (List.mem_filter.mp hz).1
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
  apply routeTagged_piece_monic
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  exact gcdFactor_monic ((toPoly_eq_zero_iff a.2).not.mp
    ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)

private theorem refineRoot_routed_product_squarefree
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (strata : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ strata, z.2.monic)
    (hs : Squarefree ((strata.map Prod.snd).prod).toPoly) :
    Squarefree (((refineRoot M D t strata).1.map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly := by
  have heq := refineRoot_exact M D t strata hm
  have hd : (((refineRoot M D t strata).1.map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly ∣
      ((strata.map Prod.snd).prod).toPoly := by
    refine ⟨((refineRoot M D t strata).2.map Prod.snd).prod.toPoly, ?_⟩
    have heqpoly := congrArg CPolynomial.toPoly heq
    rw [toPoly_mul] at heqpoly
    exact heqpoly.symm
  exact hs.squarefree_of_dvd hd

omit [BEq F] [LawfulBEq F] in
private theorem isCoprime_prod_right
    (a : Polynomial F) (ps : List (Polynomial F))
    (hc : ∀ b ∈ ps, IsCoprime a b) : IsCoprime a ps.prod := by
  induction ps with
  | nil => exact isCoprime_one_right
  | cons b rest ih =>
    rw [List.prod_cons]
    exact (hc b (by simp)).mul_right (ih (fun c hc' => hc c (by simp [hc'])))

omit [BEq F] [LawfulBEq F] in
private theorem prod_dvd_of_pairwise
    (ps : List (Polynomial F)) (q : Polynomial F)
    (hp : ps.Pairwise IsCoprime) (hd : ∀ a ∈ ps, a ∣ q) : ps.prod ∣ q := by
  induction ps with
  | nil => simp
  | cons a rest ih =>
    have hpair := List.pairwise_cons.mp hp
    rw [List.prod_cons]
    exact (isCoprime_prod_right a rest hpair.1).mul_dvd
      (hd a (by simp)) (ih hpair.2 (fun b hb => hd b (by simp [hb])))

private theorem filtered_routed_product_dvd
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (q : CPolynomial F)
    (hs : Squarefree ((routed.map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly)
    (hd : ∀ z ∈ routed, z.2.1 = q → z.2.2.toPoly ∣ q.toPoly) :
    (((routed.filter fun z => z.2.1 == q).map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly ∣
        q.toPoly := by
  let selected := (routed.filter fun z => z.2.1 == q).map
    fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2
  let allPieces := routed.map fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2
  have hsub : selected.Sublist allPieces := by
    exact List.filter_sublist.map _
  have hdSupport : selected.prod.toPoly ∣ allPieces.prod.toPoly := by
    obtain ⟨c, hc⟩ := hsub.prod_dvd_prod
    refine ⟨c.toPoly, ?_⟩
    rw [hc, toPoly_mul]
  have hselectedSquarefree : Squarefree selected.prod.toPoly :=
    hs.squarefree_of_dvd hdSupport
  have hpair : (selected.map CPolynomial.toPoly).Pairwise IsCoprime := by
    simpa only [List.pairwise_map] using pairwise_of_squarefree_product selected
      hselectedSquarefree
  have heach : ∀ a ∈ selected.map CPolynomial.toPoly, a ∣ q.toPoly := by
    intro a ha
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hpiece
    have hz' := List.mem_filter.mp hz
    exact hd z hz'.1 (by simpa only [beq_iff_eq] using hz'.2)
  have hprod := prod_dvd_of_pairwise (selected.map CPolynomial.toPoly) q.toPoly hpair heach
  have htoPoly : selected.prod.toPoly = (selected.map CPolynomial.toPoly).prod := by
    induction selected with
    | nil => simp [toPoly_one]
    | cons a rest ih =>
      rw [List.prod_cons, toPoly_mul, List.map_cons, List.prod_cons, ih]
  rw [htoPoly]
  exact hprod

private theorem recursiveOnly_division_exists
    (M : MulContext F)
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (q : CPolynomial F) (hq : q.monic)
    (hroutedMonic : ∀ z ∈ routed, z.2.2.monic)
    (hs : Squarefree ((routed.map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly)
    (hd : ∀ z ∈ routed, z.2.1 = q → z.2.2.toPoly ∣ q.toPoly) :
    ∃ d, exactDivide q
      (weightedProduct M
        ((routed.filter fun t => t.2.1 == q).map fun t => (1, t.2.2))) = some d := by
  let selected := (routed.filter fun t => t.2.1 == q).map
    fun t : ℕ × CPolynomial F × CPolynomial F => t.2.2
  let factors := (routed.filter fun t => t.2.1 == q).map fun t => (1, t.2.2)
  have hmonic : ∀ z ∈ factors, z.2.monic := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    exact hroutedMonic t (List.mem_filter.mp ht).1
  have hweighted : weightedProduct M factors = selected.prod := by
    rw [weightedProduct_eq M factors hmonic]
    simp only [factors, selected, List.map_map, Function.comp_def, pow_one]
  have hdvd : (weightedProduct M factors).toPoly ∣ q.toPoly := by
    rw [hweighted]
    exact filtered_routed_product_dvd routed q hs hd
  have hdivisor : weightedProduct M factors ≠ 0 := by
    intro hz
    have hzpoly := (toPoly_eq_zero_iff _).mpr hz
    have hqzero : q.toPoly = 0 := zero_dvd_iff.mp (by rw [← hzpoly]; exact hdvd)
    exact ((monic_toPoly_iff q).mp hq).ne_zero hqzero
  refine ⟨q.div (weightedProduct M factors),
    (exactDivide_eq_some_iff _ _ _).mpr ⟨hdivisor, ?_⟩⟩
  apply toPoly_injective
  rw [toPoly_mul, div_toPoly_eq_div, mul_comm]
  exact EuclideanDomain.mul_div_cancel'
    ((toPoly_eq_zero_iff _).not.mpr hdivisor) hdvd

private theorem recursiveOnly_exists
    (p : ℕ) (M : MulContext F)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (hrecursiveMonic : ∀ z ∈ recursive, z.2.monic)
    (hroutedMonic : ∀ z ∈ routed, z.2.2.monic)
    (hs : Squarefree ((routed.map
      fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly)
    (hd : ∀ z ∈ routed, z.2.2.toPoly ∣ z.2.1.toPoly) :
    ∃ only, recursiveOnly p M recursive routed = some only := by
  induction recursive with
  | nil => exact ⟨[], rfl⟩
  | cons z rest ih =>
    obtain ⟨d, hdivide⟩ := recursiveOnly_division_exists M routed z.2
      (hrecursiveMonic z (by simp)) hroutedMonic hs
      (fun t ht heq => by simpa [heq] using hd t ht)
    obtain ⟨tail, htail⟩ := ih (fun a ha => hrecursiveMonic a (by simp [ha]))
    refine ⟨(p * z.1, d) :: tail, ?_⟩
    unfold recursiveOnly at htail ⊢
    simp only [List.mapM_cons, hdivide]
    rw [htail]
    rfl

private theorem cpoly_toPoly_dvd_prod_of_mem (a : CPolynomial F)
    (ps : List (CPolynomial F)) (ha : a ∈ ps) : a.toPoly ∣ ps.prod.toPoly := by
  obtain ⟨q, hq⟩ := List.dvd_prod ha
  exact ⟨q.toPoly, by rw [hq, toPoly_mul]⟩

/-- The executable refinement has no structural or exact-division failure on monic recursive
factors and squarefree monic residue support. -/
theorem refineFactors_succeeds
    (p : ℕ) (M : MulContext F) (D : ModContext F)
    (strata recursive : List (ℕ × CPolynomial F))
    (hstrataMonic : ∀ z ∈ strata, z.2.monic)
    (hstrataSquarefree : Squarefree ((strata.map Prod.snd).prod).toPoly)
    (hrecursiveMonic : ∀ z ∈ recursive, z.2.monic) :
    ∃ factors, refineFactors p M D strata recursive = some factors := by
  by_cases hrecursive : recursive = []
  · subst recursive
    exact ⟨groupFactors strata, by simp [refineFactors]⟩
  · let moduli := recursive.map Prod.snd
    obtain ⟨tree, htree⟩ := build_eq_singleton_of_nonempty M moduli (by simpa [moduli])
    have hleaves : tree.leaves = moduli := by
      have h := BatchRemainder.buildForest_leaves M moduli.length
        (moduli.map BatchRemainder.Tree.leaf)
      rw [← BatchRemainder.build, htree] at h
      have heq : (moduli.map BatchRemainder.Tree.leaf).flatMap
          BatchRemainder.Tree.leaves = moduli := by
        induction moduli with
        | nil => rfl
        | cons q rest ih => simp [BatchRemainder.Tree.leaves, ih]
      simpa using h.trans heq
    have hwell : tree.WellFormed := by
      have hw : ∀ t ∈ BatchRemainder.build M moduli, t.WellFormed := by
        apply BatchRemainder.buildForest_wellFormed
        intro t ht
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
        exact hrecursiveMonic z hz
      exact hw tree (by simp [htree])
    let refined := refineRoot M D tree strata
    obtain ⟨mixed, hmixed⟩ := labelIntersections_refineRoot_exists
      p M D tree strata recursive (by simpa [moduli] using hleaves)
    have hroutedMonic : ∀ z ∈ refined.1, z.2.2.monic :=
      refineRoot_routed_monic M D tree strata hstrataMonic
    have hroutedSquarefree : Squarefree ((refined.1.map
        fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod).toPoly :=
      refineRoot_routed_product_squarefree M D tree strata hstrataMonic hstrataSquarefree
    have hroutedDvd : ∀ z ∈ refined.1, z.2.2.toPoly ∣ z.2.1.toPoly :=
      refineRoot_leaf_dvd M D tree hwell strata hstrataMonic
        (fun z hz => hstrataSquarefree.squarefree_of_dvd
          (cpoly_toPoly_dvd_prod_of_mem z.2 _ (List.mem_map.mpr ⟨z, hz, rfl⟩)))
    obtain ⟨only, honly⟩ := recursiveOnly_exists p M recursive refined.1
      hrecursiveMonic hroutedMonic hroutedSquarefree hroutedDvd
    refine ⟨groupFactors (refined.2 ++ mixed ++ only), ?_⟩
    change BatchRemainder.build M (recursive.map Prod.snd) = [tree] at htree
    have hnotempty : recursive.isEmpty ≠ true := by
      cases recursive with
      | nil => contradiction
      | cons z rest => simp
    unfold refineFactors
    rw [if_neg hnotempty]
    rw [htree]
    simp [hmixed, honly, refined]

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
