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

private theorem supportProduct_insertFactor (z : ℕ × CPolynomial F)
    (factors : List (ℕ × CPolynomial F)) :
    ((insertFactor z factors).map Prod.snd).prod =
      z.2 * (factors.map Prod.snd).prod := by
  induction factors with
  | nil =>
      by_cases hz : z.2 = 1 <;> simp [insertFactor, hz]
  | cons a rest ih =>
      by_cases hz : z.2 = 1
      · simp [insertFactor, hz]
      · by_cases hm : z.1 = a.1
        · simp [insertFactor, hz, hm]
          ring
        · simp only [insertFactor, beq_iff_eq, hz, ↓reduceIte, hm,
            List.map_cons, List.prod_cons]
          rw [ih]
          ring

private theorem supportProduct_groupFactors (factors : List (ℕ × CPolynomial F)) :
    ((groupFactors factors).map Prod.snd).prod = (factors.map Prod.snd).prod := by
  induction factors with
  | nil => rfl
  | cons z rest ih =>
    change ((insertFactor z (groupFactors rest)).map Prod.snd).prod = _
    rw [supportProduct_insertFactor, ih]
    rfl

private theorem cpoly_mul_monic {a b : CPolynomial F} (ha : a.monic) (hb : b.monic) :
    (a * b).monic := by
  rw [monic_toPoly_iff, toPoly_mul]
  exact ((monic_toPoly_iff a).mp ha).mul ((monic_toPoly_iff b).mp hb)

private theorem cpoly_mul_ne_one_of_monic_right_nonunit
    (a b : CPolynomial F) (hb : b.monic) (hbunit : b ≠ 1) : a * b ≠ 1 := by
  intro h
  have hpoly : b.toPoly * a.toPoly = 1 := by
    rw [mul_comm, ← toPoly_mul, h, toPoly_one]
  have hbIsUnit : IsUnit b.toPoly := IsUnit.of_mul_eq_one a.toPoly hpoly
  apply hbunit
  apply toPoly_injective
  simpa [toPoly_one] using ((monic_toPoly_iff b).mp hb).eq_one_of_isUnit hbIsUnit

private theorem insertFactor_positive_monic_nonunit
    (z : ℕ × CPolynomial F) (factors : List (ℕ × CPolynomial F))
    (hzpositive : 0 < z.1) (hzmonic : z.2.monic)
    (hshape : ∀ a ∈ factors, 0 < a.1 ∧ a.2.monic ∧ a.2 ≠ 1) :
    ∀ a ∈ insertFactor z factors, 0 < a.1 ∧ a.2.monic ∧ a.2 ≠ 1 := by
  induction factors with
  | nil =>
      by_cases hzunit : z.2 = 1
      · simp [insertFactor, hzunit]
      · simpa [insertFactor, hzunit] using
          (show 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1 from ⟨hzpositive, hzmonic, hzunit⟩)
  | cons b rest ih =>
      by_cases hzunit : z.2 = 1
      · simpa [insertFactor, hzunit] using hshape
      · by_cases hlabel : z.1 = b.1
        · intro a ha
          simp only [insertFactor, beq_iff_eq, hzunit, ↓reduceIte, hlabel,
            List.mem_cons] at ha
          rcases ha with rfl | ha
          · have hb := hshape b (by simp)
            exact ⟨hb.1, cpoly_mul_monic hzmonic hb.2.1,
              cpoly_mul_ne_one_of_monic_right_nonunit z.2 b.2 hb.2.1 hb.2.2⟩
          · exact hshape a (by simp [ha])
        · intro a ha
          simp only [insertFactor, beq_iff_eq, hzunit, ↓reduceIte, hlabel,
            List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hshape _ (by simp)
          · exact ih (fun c hc => hshape c (by simp [hc])) a ha

private theorem groupFactors_positive_monic_nonunit
    (factors : List (ℕ × CPolynomial F))
    (hshape : ∀ z ∈ factors, 0 < z.1 ∧ z.2.monic) :
    ∀ z ∈ groupFactors factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1 := by
  induction factors with
  | nil => simp [groupFactors]
  | cons z rest ih =>
      change ∀ a ∈ insertFactor z (groupFactors rest), _
      apply insertFactor_positive_monic_nonunit z _
      · exact (hshape z (by simp)).1
      · exact (hshape z (by simp)).2
      · exact ih (fun a ha => hshape a (by simp [ha]))

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

/-- The root split and batched route preserve every residue label and its weighted product. -/
theorem refineRoot_factorProduct_exact
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic) :
    factorProduct ((refineRoot M D t pieces).1.map fun z => (z.1, z.2.2)) *
      factorProduct (refineRoot M D t pieces).2 = factorProduct pieces := by
  have hp : ∀ z ∈ pruneTagged pieces, z.2.monic :=
    fun z hz => hm z (List.mem_filter.mp hz).1
  have hl : ∀ z ∈ (pruneTagged pieces).map
      (fun z => (z.1, gcdFactor z.2 t.product)), z.2.monic := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_monic ((toPoly_eq_zero_iff a.2).not.mp
      ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map,
    Function.comp_def]
  rw [routeTagged_factorProduct_exact M D t _ hl, factorProduct_pruneTagged]
  exact (split_factorProduct t.product (pruneTagged pieces) hp).trans
    (factorProduct_pruneTagged pieces)

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

private theorem destinationLabel?_eq_of_mem
    (recursive : List (ℕ × CPolynomial F)) (a : ℕ) (q : CPolynomial F)
    (hnodup : (recursive.map Prod.snd).Nodup) (hmem : (a, q) ∈ recursive) :
    destinationLabel? recursive q = some a := by
  induction recursive with
  | nil => simp at hmem
  | cons z rest ih =>
      rcases z with ⟨b, s⟩
      rw [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp [destinationLabel?]
      · have hne : s ≠ q := by
          intro heq
          apply hnodup.1
          rw [heq]
          exact List.mem_map.mpr ⟨(a, q), htail, rfl⟩
        unfold destinationLabel?
        rw [List.find?_cons_of_neg (by simpa only [beq_iff_eq] using hne)]
        exact ih hnodup.2 htail

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

private def routedRecursiveContribution (p : ℕ)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F)) : CPolynomial F :=
  factorProduct (routed.map fun z =>
    (p * (destinationLabel? recursive z.2.1).getD 0, z.2.2))

private theorem labelIntersections_factorProduct
    (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (mixed : List (ℕ × CPolynomial F))
    (hmixed : labelIntersections p recursive routed = some mixed) :
    factorProduct mixed =
      factorProduct (routed.map fun z => (z.1, z.2.2)) *
        routedRecursiveContribution p recursive routed := by
  induction routed generalizing mixed with
  | nil =>
      change some [] = some mixed at hmixed
      have : mixed = [] := Option.some.inj hmixed.symm
      subst mixed
      simp only [factorProduct, routedRecursiveContribution, List.map_nil,
        List.prod_nil, one_mul]
  | cons z rest ih =>
      simp only [labelIntersections, List.mapM_cons] at hmixed
      cases hlabel : destinationLabel? recursive z.2.1 with
      | none => simp [hlabel] at hmixed
      | some a =>
          cases htail : labelIntersections p recursive rest with
          | none =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              simp [hlabel] at hmixed
          | some tail =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              have hout : mixed = (z.1 + p * a, z.2.2) :: tail := by
                simpa [hlabel] using hmixed.symm
              subst mixed
              change z.2.2 ^ (z.1 + p * a) * factorProduct tail = _
              rw [ih tail htail]
              simp only [factorProduct, List.map_cons, List.prod_cons,
                Option.getD_some, hlabel, routedRecursiveContribution]
              rw [pow_add]
              ring

omit [LawfulBEq F] in
private theorem labelIntersections_erase
    (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (mixed : List (ℕ × CPolynomial F))
    (hmixed : labelIntersections p recursive routed = some mixed) :
    mixed.map Prod.snd = routed.map fun z => z.2.2 := by
  induction routed generalizing mixed with
  | nil =>
      simp [labelIntersections] at hmixed
      subst mixed
      rfl
  | cons z rest ih =>
      simp only [labelIntersections, List.mapM_cons] at hmixed
      cases hlabel : destinationLabel? recursive z.2.1 with
      | none => simp [hlabel] at hmixed
      | some a =>
          cases htail : labelIntersections p recursive rest with
          | none =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              simp [hlabel] at hmixed
          | some tail =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              have hout : mixed = (z.1 + p * a, z.2.2) :: tail := by
                simpa [hlabel] using hmixed.symm
              subst mixed
              simp [ih tail (by simpa only [labelIntersections] using htail)]

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

private theorem routeTagged_label_positive
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) (hm : ∀ z ∈ pieces, z.2.monic)
    (hp : ∀ z ∈ pieces, 0 < z.1) :
    ∀ z ∈ routeTagged M D t pieces, 0 < z.1 := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hp a (List.mem_filter.mp ha).1
  | node h left right ihl ihr =>
    have hprune : ∀ z ∈ pruneTagged pieces, 0 < z.1 :=
      fun z hz => hp z (List.mem_filter.mp hz).1
    have hmprune : ∀ z ∈ pruneTagged pieces, z.2.monic :=
      fun z hz => hm z (List.mem_filter.mp hz).1
    rw [routeTagged, batchSplitTagged_eq M D _ _ hmprune]
    simp only [List.map_map, Function.comp_def]
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · apply ihl _ (fun a ha => ?_) (fun a ha => ?_) z hz
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdFactor_monic ((toPoly_eq_zero_iff b.2).not.mp
          ((monic_toPoly_iff b.2).mp (hmprune b hb)).ne_zero)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hprune b hb
    · apply ihr _ (fun a ha => ?_) (fun a ha => ?_) z hz
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact gcdComplement_monic (hmprune b hb)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hprune b hb

private theorem routeTagged_piece_nonunit
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (pieces : List (ℕ × CPolynomial F)) :
    ∀ z ∈ routeTagged M D t pieces, z.2.2 ≠ 1 := by
  induction t generalizing pieces with
  | leaf h =>
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    simpa only [bne_iff_ne] using (List.mem_filter.mp ha).2
  | node h left right ihl ihr =>
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ihl _ z hz
    · exact ihr _ z hz

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

private theorem refineRoot_routed_label_positive
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (strata : List (ℕ × CPolynomial F))
    (hm : ∀ z ∈ strata, z.2.monic) (hpositive : ∀ z ∈ strata, 0 < z.1) :
    ∀ z ∈ (refineRoot M D t strata).1, 0 < z.1 := by
  have hp : ∀ z ∈ pruneTagged strata, z.2.monic :=
    fun z hz => hm z (List.mem_filter.mp hz).1
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
  apply routeTagged_label_positive
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact gcdFactor_monic ((toPoly_eq_zero_iff a.2).not.mp
      ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero)
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact hpositive a (List.mem_filter.mp ha).1

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

private def routedAtProduct
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (q : CPolynomial F) : CPolynomial F :=
  ((routed.filter fun z => z.2.1 == q).map fun z => z.2.2).prod

private def recursiveIntersectionContribution (p : ℕ)
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (recursive : List (ℕ × CPolynomial F)) : CPolynomial F :=
  (recursive.map fun z => routedAtProduct routed z.2 ^ (p * z.1)).prod

private theorem recursiveOnly_factorProduct
    (p : ℕ) (M : MulContext F)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (only : List (ℕ × CPolynomial F))
    (hroutedMonic : ∀ z ∈ routed, z.2.2.monic)
    (honly : recursiveOnly p M recursive routed = some only) :
    factorProduct only * recursiveIntersectionContribution p routed recursive =
      (factorProduct recursive) ^ p := by
  induction recursive generalizing only with
  | nil =>
      change some [] = some only at honly
      have : only = [] := Option.some.inj honly.symm
      subst only
      simp only [factorProduct, recursiveIntersectionContribution, List.map_nil,
        List.prod_nil, one_mul, one_pow]
  | cons z rest ih =>
      simp only [recursiveOnly, List.mapM_cons] at honly
      let selected := (routed.filter fun t => t.2.1 == z.2).map fun t => t.2.2
      let selectedTagged := (routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2)
      have hselectedMonic : ∀ a ∈ selectedTagged, a.2.monic := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        exact hroutedMonic t (List.mem_filter.mp ht).1
      have hweighted : weightedProduct M selectedTagged = selected.prod := by
        rw [weightedProduct_eq M selectedTagged hselectedMonic]
        simp [selectedTagged, selected, List.map_map, Function.comp_def]
      cases hdivide : exactDivide z.2 (weightedProduct M selectedTagged) with
      | none =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = none := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          simp at honly
      | some d =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = some d := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          cases htail : recursiveOnly p M rest routed with
          | none =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              simp at honly
          | some tail =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              have hout : only = (p * z.1, d) :: tail := by simpa using honly.symm
              subst only
              have hexact := (exactDivide_eq_some_iff _ _ _).mp hdivide
              have hd : d * selected.prod = z.2 := by simpa [hweighted] using hexact.2
              have hpow : d ^ (p * z.1) * selected.prod ^ (p * z.1) =
                  z.2 ^ (p * z.1) := by rw [← mul_pow, hd]
              change d ^ (p * z.1) * factorProduct tail *
                  (selected.prod ^ (p * z.1) *
                    recursiveIntersectionContribution p routed rest) = _
              rw [show d ^ (p * z.1) * factorProduct tail *
                    (selected.prod ^ (p * z.1) *
                      recursiveIntersectionContribution p routed rest) =
                    (d ^ (p * z.1) * selected.prod ^ (p * z.1)) *
                      (factorProduct tail * recursiveIntersectionContribution p routed rest) by
                    ring,
                ih tail (by simpa only [recursiveOnly] using htail)]
              change _ = (z.2 ^ z.1 * factorProduct rest) ^ p
              rw [mul_pow]
              rw [hpow]
              congr 1
              rw [← pow_mul]
              congr 1
              exact Nat.mul_comm p z.1

private theorem recursiveOnly_supportProduct
    (p : ℕ) (M : MulContext F)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (only : List (ℕ × CPolynomial F))
    (hroutedMonic : ∀ z ∈ routed, z.2.2.monic)
    (honly : recursiveOnly p M recursive routed = some only) :
    (only.map Prod.snd).prod *
        (recursive.map fun z => routedAtProduct routed z.2).prod =
      (recursive.map Prod.snd).prod := by
  induction recursive generalizing only with
  | nil =>
      simp [recursiveOnly] at honly
      subst only
      simp
  | cons z rest ih =>
      simp only [recursiveOnly, List.mapM_cons] at honly
      let selected := (routed.filter fun t => t.2.1 == z.2).map fun t => t.2.2
      let selectedTagged := (routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2)
      have hselectedMonic : ∀ a ∈ selectedTagged, a.2.monic := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        exact hroutedMonic t (List.mem_filter.mp ht).1
      have hweighted : weightedProduct M selectedTagged = selected.prod := by
        rw [weightedProduct_eq M selectedTagged hselectedMonic]
        simp [selectedTagged, selected, List.map_map, Function.comp_def]
      cases hdivide : exactDivide z.2 (weightedProduct M selectedTagged) with
      | none =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = none := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          simp at honly
      | some d =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = some d := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          cases htail : recursiveOnly p M rest routed with
          | none =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              simp at honly
          | some tail =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              have hout : only = (p * z.1, d) :: tail := by simpa using honly.symm
              subst only
              have hexact := (exactDivide_eq_some_iff _ _ _).mp hdivide
              have hd : d * selected.prod = z.2 := by simpa [hweighted] using hexact.2
              simp only [List.map_cons, List.prod_cons]
              change d * (tail.map Prod.snd).prod *
                  (selected.prod * (rest.map fun z => routedAtProduct routed z.2).prod) =
                z.2 * (rest.map Prod.snd).prod
              rw [show d * (tail.map Prod.snd).prod *
                    (selected.prod * (rest.map fun z => routedAtProduct routed z.2).prod) =
                  (d * selected.prod) *
                    ((tail.map Prod.snd).prod *
                      (rest.map fun z => routedAtProduct routed z.2).prod) by ring,
                hd, ih tail (by simpa only [recursiveOnly] using htail)]

private theorem recursiveIntersectionContribution_cons_of_not_mem
    (p : ℕ) (z : ℕ × CPolynomial F × CPolynomial F)
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (recursive : List (ℕ × CPolynomial F))
    (hnotmem : z.2.1 ∉ recursive.map Prod.snd) :
    recursiveIntersectionContribution p (z :: routed) recursive =
      recursiveIntersectionContribution p routed recursive := by
  induction recursive with
  | nil => rfl
  | cons a rest ih =>
      have hne : z.2.1 ≠ a.2 := by
        intro heq
        apply hnotmem
        exact List.mem_map.mpr ⟨a, List.mem_cons_self, heq.symm⟩
      have hnotrest : z.2.1 ∉ rest.map Prod.snd := by
        intro hmem
        exact hnotmem (List.mem_cons_of_mem _ hmem)
      simp only [recursiveIntersectionContribution, List.map_cons, List.prod_cons]
      have hhead : routedAtProduct (z :: routed) a.2 = routedAtProduct routed a.2 := by
        simp [routedAtProduct, hne]
      rw [hhead]
      change _ * recursiveIntersectionContribution p (z :: routed) rest =
        _ * recursiveIntersectionContribution p routed rest
      rw [ih hnotrest]

private theorem recursiveIntersectionContribution_cons
    (p : ℕ) (z : ℕ × CPolynomial F × CPolynomial F)
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (recursive : List (ℕ × CPolynomial F)) (a : ℕ)
    (hnodup : (recursive.map Prod.snd).Nodup)
    (hmem : (a, z.2.1) ∈ recursive) :
    recursiveIntersectionContribution p (z :: routed) recursive =
      z.2.2 ^ (p * a) * recursiveIntersectionContribution p routed recursive := by
  induction recursive with
  | nil => simp at hmem
  | cons b rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        have hrest := recursiveIntersectionContribution_cons_of_not_mem
          p z routed rest hnodup.1
        simp only [recursiveIntersectionContribution, List.map_cons, List.prod_cons]
        change routedAtProduct (z :: routed) z.2.1 ^ (p * a) *
            recursiveIntersectionContribution p (z :: routed) rest = _
        rw [hrest]
        have hcurrent : routedAtProduct (z :: routed) z.2.1 =
            z.2.2 * routedAtProduct routed z.2.1 := by
          simp [routedAtProduct]
        rw [hcurrent, mul_pow]
        change _ = z.2.2 ^ (p * a) *
          (routedAtProduct routed z.2.1 ^ (p * a) *
            recursiveIntersectionContribution p routed rest)
        ring
      · have hne : z.2.1 ≠ b.2 := by
          intro heq
          apply hnodup.1
          rw [← heq]
          exact List.mem_map.mpr ⟨(a, z.2.1), htail, rfl⟩
        simp only [recursiveIntersectionContribution, List.map_cons, List.prod_cons]
        have hheadUnchanged : routedAtProduct (z :: routed) b.2 = routedAtProduct routed b.2 := by
          simp [routedAtProduct, hne]
        rw [hheadUnchanged]
        change _ * recursiveIntersectionContribution p (z :: routed) rest = _
        rw [ih hnodup.2 htail]
        change routedAtProduct routed b.2 ^ (p * b.1) *
            (z.2.2 ^ (p * a) * recursiveIntersectionContribution p routed rest) =
          z.2.2 ^ (p * a) * (routedAtProduct routed b.2 ^ (p * b.1) *
            recursiveIntersectionContribution p routed rest)
        ring

private theorem recursiveIntersectionContribution_eq_routed
    (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (hnodup : (recursive.map Prod.snd).Nodup)
    (hdest : ∀ z ∈ routed, ∃ a, (a, z.2.1) ∈ recursive) :
    recursiveIntersectionContribution p routed recursive =
      routedRecursiveContribution p recursive routed := by
  induction routed with
  | nil =>
      simp [recursiveIntersectionContribution, routedAtProduct,
        routedRecursiveContribution, factorProduct]
  | cons z rest ih =>
      obtain ⟨a, ha⟩ := hdest z (by simp)
      rw [recursiveIntersectionContribution_cons p z rest recursive a hnodup ha,
        ih (fun t ht => hdest t (by simp [ht]))]
      have hlabel := destinationLabel?_eq_of_mem recursive a z.2.1 hnodup ha
      simp [routedRecursiveContribution, factorProduct, hlabel]

private theorem routedAtProduct_partition
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (hnodup : (recursive.map Prod.snd).Nodup)
    (hdest : ∀ z ∈ routed, ∃ a, (a, z.2.1) ∈ recursive) :
    (recursive.map fun z => routedAtProduct routed z.2).prod =
      (routed.map fun z => z.2.2).prod := by
  let ones := recursive.map fun z => (1, z.2)
  have honesNodup : (ones.map Prod.snd).Nodup := by
    simpa [ones, List.map_map, Function.comp_def] using hnodup
  have honesDest : ∀ z ∈ routed, ∃ a, (a, z.2.1) ∈ ones := by
    intro z hz
    obtain ⟨a, ha⟩ := hdest z hz
    exact ⟨1, List.mem_map.mpr ⟨(a, z.2.1), ha, rfl⟩⟩
  have h := recursiveIntersectionContribution_eq_routed 1 ones routed honesNodup honesDest
  calc
    _ = recursiveIntersectionContribution 1 routed ones := by
      simp [recursiveIntersectionContribution, ones, List.map_map, Function.comp_def]
    _ = routedRecursiveContribution 1 ones routed := h
    _ = _ := by
      unfold routedRecursiveContribution factorProduct
      apply congrArg List.prod
      rw [List.map_map]
      apply List.map_congr_left
      intro z hz
      obtain ⟨a, ha⟩ := hdest z hz
      have hmem : (1, z.2.1) ∈ ones :=
        List.mem_map.mpr ⟨(a, z.2.1), ha, rfl⟩
      have hlabel := destinationLabel?_eq_of_mem ones 1 z.2.1 honesNodup hmem
      simp [hlabel]

private theorem cpoly_toPoly_dvd_prod_of_mem (a : CPolynomial F)
    (ps : List (CPolynomial F)) (ha : a ∈ ps) : a.toPoly ∣ ps.prod.toPoly := by
  obtain ⟨q, hq⟩ := List.dvd_prod ha
  exact ⟨q.toPoly, by rw [hq, toPoly_mul]⟩

private theorem toPoly_prod (ps : List (CPolynomial F)) :
    ps.prod.toPoly = (ps.map CPolynomial.toPoly).prod := by
  induction ps with
  | nil => simp [toPoly_one]
  | cons a rest ih => rw [List.prod_cons, toPoly_mul, List.map_cons, List.prod_cons, ih]

omit [BEq F] [LawfulBEq F] in
private theorem isCoprime_list_prod_left (ps : List (Polynomial F)) (q : Polynomial F)
    (hc : ∀ a ∈ ps, IsCoprime a q) : IsCoprime ps.prod q := by
  induction ps with
  | nil => exact isCoprime_one_left
  | cons a rest ih =>
      rw [List.prod_cons]
      exact (hc a (by simp)).mul_left (ih (fun b hb => hc b (by simp [hb])))

private theorem refineRoot_residueOnly_coprime
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (strata : List (ℕ × CPolynomial F))
    (hmonic : ∀ z ∈ strata, z.2.monic)
    (hsquarefree : ∀ z ∈ strata, Squarefree z.2.toPoly) :
    IsCoprime (((refineRoot M D t strata).2.map Prod.snd).prod).toPoly t.product.toPoly := by
  have hp : ∀ z ∈ pruneTagged strata, z.2.monic :=
    fun z hz => hmonic z (List.mem_filter.mp hz).1
  have heach : ∀ z ∈ (refineRoot M D t strata).2,
      IsCoprime z.2.toPoly t.product.toPoly := by
    simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
    intro z hz
    have hz' := List.mem_filter.mp hz
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hz'.1
    subst z
    have ha0 : a.2 ≠ 0 :=
      (toPoly_eq_zero_iff a.2).not.mp ((monic_toPoly_iff a.2).mp (hp a ha)).ne_zero
    exact gcdComplement_isCoprime_right ha0
      (hsquarefree a (List.mem_filter.mp ha).1)
  rw [toPoly_prod]
  apply isCoprime_list_prod_left
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
  exact heach z hz

private theorem cpoly_prod_monic (ps : List (CPolynomial F))
    (hm : ∀ q ∈ ps, q.monic) : ps.prod.monic := by
  rw [monic_toPoly_iff, toPoly_prod]
  induction ps with
  | nil => simp
  | cons q rest ih =>
      rw [List.map_cons, List.prod_cons]
      exact ((monic_toPoly_iff q).mp (hm q (by simp))).mul
        (ih (fun a ha => hm a (by simp [ha])))

private theorem refineRoot_residueOnly_positive_monic
    (M : MulContext F) (D : ModContext F) (t : BatchRemainder.Tree F)
    (strata : List (ℕ × CPolynomial F))
    (hpositive : ∀ z ∈ strata, 0 < z.1)
    (hmonic : ∀ z ∈ strata, z.2.monic) :
    ∀ z ∈ (refineRoot M D t strata).2, 0 < z.1 ∧ z.2.monic := by
  have hp : ∀ z ∈ pruneTagged strata, z.2.monic :=
    fun z hz => hmonic z (List.mem_filter.mp hz).1
  simp only [refineRoot, batchSplitTagged_eq M D _ _ hp, List.map_map, Function.comp_def]
  intro z hz
  have hz' := List.mem_filter.mp hz
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hz'.1
  subst z
  exact ⟨hpositive a (List.mem_filter.mp ha).1, gcdComplement_monic (hp a ha)⟩

omit [LawfulBEq F] in
private theorem labelIntersections_positive_monic
    (p : ℕ) (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (mixed : List (ℕ × CPolynomial F))
    (hpositive : ∀ z ∈ routed, 0 < z.1)
    (hmonic : ∀ z ∈ routed, z.2.2.monic)
    (hmixed : labelIntersections p recursive routed = some mixed) :
    ∀ z ∈ mixed, 0 < z.1 ∧ z.2.monic := by
  induction routed generalizing mixed with
  | nil =>
      simp [labelIntersections] at hmixed
      subst mixed
      simp
  | cons z rest ih =>
      simp only [labelIntersections, List.mapM_cons] at hmixed
      cases hlabel : destinationLabel? recursive z.2.1 with
      | none => simp [hlabel] at hmixed
      | some aa =>
          cases htail : labelIntersections p recursive rest with
          | none =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              simp [hlabel] at hmixed
          | some tail =>
              unfold labelIntersections at htail
              rw [htail] at hmixed
              have hout : mixed = (z.1 + p * aa, z.2.2) :: tail := by
                simpa [hlabel] using hmixed.symm
              subst mixed
              intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · exact ⟨Nat.lt_add_right _ (hpositive z (by simp)), hmonic z (by simp)⟩
              · exact ih tail (fun c hc => hpositive c (by simp [hc]))
                  (fun c hc => hmonic c (by simp [hc]))
                  (by simpa only [labelIntersections] using htail) b hb

private theorem recursiveOnly_positive_monic
    (p : ℕ) (hp : 0 < p) (M : MulContext F)
    (recursive : List (ℕ × CPolynomial F))
    (routed : List (ℕ × CPolynomial F × CPolynomial F))
    (only : List (ℕ × CPolynomial F))
    (hrecursive : ∀ z ∈ recursive, 0 < z.1 ∧ z.2.monic)
    (hroutedMonic : ∀ z ∈ routed, z.2.2.monic)
    (honly : recursiveOnly p M recursive routed = some only) :
    ∀ z ∈ only, 0 < z.1 ∧ z.2.monic := by
  induction recursive generalizing only with
  | nil =>
      simp [recursiveOnly] at honly
      subst only
      simp
  | cons z rest ih =>
      simp only [recursiveOnly, List.mapM_cons] at honly
      let selected := (routed.filter fun t => t.2.1 == z.2).map fun t => t.2.2
      let selectedTagged := (routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2)
      have hselectedMonic : ∀ a ∈ selectedTagged, a.2.monic := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        exact hroutedMonic t (List.mem_filter.mp ht).1
      have hweighted : weightedProduct M selectedTagged = selected.prod := by
        rw [weightedProduct_eq M selectedTagged hselectedMonic]
        simp [selectedTagged, selected, List.map_map, Function.comp_def]
      cases hdivide : exactDivide z.2 (weightedProduct M selectedTagged) with
      | none =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = none := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          simp at honly
      | some d =>
          have hdivide' : exactDivide z.2 (weightedProduct M
              ((routed.filter fun t => t.2.1 == z.2).map fun t => (1, t.2.2))) = some d := by
            simpa [selectedTagged] using hdivide
          rw [hdivide'] at honly
          cases htail : recursiveOnly p M rest routed with
          | none =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              simp at honly
          | some tail =>
              unfold recursiveOnly at htail
              rw [htail] at honly
              have hout : only = (p * z.1, d) :: tail := by simpa using honly.symm
              subst only
              have hexact := (exactDivide_eq_some_iff _ _ _).mp hdivide
              have hselectedProdMonic : selected.prod.monic := by
                apply cpoly_prod_monic
                intro q hq
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
                exact hroutedMonic t (List.mem_filter.mp ht).1
              have hdMonic : d.monic := by
                rw [monic_toPoly_iff]
                apply ((monic_toPoly_iff selected.prod).mp hselectedProdMonic).of_mul_monic_right
                rw [← toPoly_mul, show d * selected.prod = z.2 by
                  simpa [hweighted] using hexact.2]
                exact (monic_toPoly_iff z.2).mp (hrecursive z (by simp)).2
              intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · exact ⟨Nat.mul_pos hp (hrecursive z (by simp)).1, hdMonic⟩
              · exact ih tail (fun c hc => hrecursive c (by simp [hc]))
                  (by simpa only [recursiveOnly] using htail) b hb

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

/-- Successful refinement reconstructs the residue-weighted product times the `p`th power of
the recursively decomposed product, including every overlap label `r + p*a`. -/
theorem refineFactors_reconstruct
    (p : ℕ) (M : MulContext F) (D : ModContext F)
    (strata recursive factors : List (ℕ × CPolynomial F))
    (hstrataMonic : ∀ z ∈ strata, z.2.monic)
    (hrecursiveNodup : (recursive.map Prod.snd).Nodup)
    (hresult : refineFactors p M D strata recursive = some factors) :
    factorProduct factors = factorProduct strata * factorProduct recursive ^ p := by
  by_cases hrecursive : recursive = []
  · subst recursive
    change some (groupFactors strata) = some factors at hresult
    have : factors = groupFactors strata := Option.some.inj hresult.symm
    subst factors
    rw [factorProduct_groupFactors]
    simp [factorProduct]
  · have hnotempty : recursive.isEmpty ≠ true := by
      cases recursive with
      | nil => contradiction
      | cons z rest => simp
    unfold refineFactors at hresult
    rw [if_neg hnotempty] at hresult
    cases hbuild : BatchRemainder.build M (recursive.map Prod.snd) with
    | nil => simp [hbuild] at hresult
    | cons tree trees =>
      cases trees with
      | cons next rest => simp [hbuild] at hresult
      | nil =>
        rw [hbuild] at hresult
        let refined := refineRoot M D tree strata
        cases hmixed : labelIntersections p recursive refined.1 with
        | none => simp [refined, hmixed] at hresult
        | some mixed =>
          cases honly : recursiveOnly p M recursive refined.1 with
          | none => simp [refined, hmixed, honly] at hresult
          | some only =>
            have hout : factors = groupFactors (refined.2 ++ mixed ++ only) := by
              simpa [refined, hmixed, honly] using hresult.symm
            subst factors
            have hleaves : tree.leaves = recursive.map Prod.snd := by
              have h := BatchRemainder.buildForest_leaves M (recursive.map Prod.snd).length
                ((recursive.map Prod.snd).map BatchRemainder.Tree.leaf)
              rw [← BatchRemainder.build, hbuild] at h
              have heq : ((recursive.map Prod.snd).map BatchRemainder.Tree.leaf).flatMap
                  BatchRemainder.Tree.leaves = recursive.map Prod.snd := by
                induction recursive.map Prod.snd with
                | nil => rfl
                | cons q rest ih => simp [BatchRemainder.Tree.leaves, ih]
              simpa using h.trans heq
            have hdest : ∀ z ∈ refined.1, ∃ a, (a, z.2.1) ∈ recursive := by
              intro z hz
              have hleaf := routeTagged_leaf_mem M D tree _ z hz
              rw [hleaves] at hleaf
              obtain ⟨a, ha, heq⟩ := List.mem_map.mp hleaf
              rcases a with ⟨label, q⟩
              simp only at heq
              subst q
              exact ⟨label, ha⟩
            have hroutedMonic : ∀ z ∈ refined.1, z.2.2.monic :=
              refineRoot_routed_monic M D tree strata hstrataMonic
            have hmixedProduct := labelIntersections_factorProduct
              p recursive refined.1 mixed hmixed
            have honlyProduct := recursiveOnly_factorProduct
              p M recursive refined.1 only hroutedMonic honly
            have hpartition := recursiveIntersectionContribution_eq_routed
              p recursive refined.1 hrecursiveNodup hdest
            have hroot := refineRoot_factorProduct_exact M D tree strata hstrataMonic
            have hroot' : factorProduct (refined.1.map fun z => (z.1, z.2.2)) *
                factorProduct refined.2 = factorProduct strata := by
              simpa [refined] using hroot
            rw [factorProduct_groupFactors, factorProduct_append, factorProduct_append,
              hmixedProduct]
            rw [hpartition] at honlyProduct
            rw [show factorProduct refined.2 *
                  (factorProduct (refined.1.map fun z => (z.1, z.2.2)) *
                    routedRecursiveContribution p recursive refined.1) *
                    factorProduct only =
                (factorProduct (refined.1.map fun z => (z.1, z.2.2)) *
                  factorProduct refined.2) *
                  (factorProduct only *
                    routedRecursiveContribution p recursive refined.1) by ring,
              hroot', honlyProduct]

/-- Refinement preserves squarefreeness of the union support after splitting every overlap. -/
theorem refineFactors_support_squarefree
    (p : ℕ) (M : MulContext F) (D : ModContext F)
    (strata recursive factors : List (ℕ × CPolynomial F))
    (hstrataMonic : ∀ z ∈ strata, z.2.monic)
    (hstrataSquarefree : Squarefree ((strata.map Prod.snd).prod).toPoly)
    (hrecursiveMonic : ∀ z ∈ recursive, z.2.monic)
    (hrecursiveSquarefree : Squarefree ((recursive.map Prod.snd).prod).toPoly)
    (hrecursiveNodup : (recursive.map Prod.snd).Nodup)
    (hresult : refineFactors p M D strata recursive = some factors) :
    Squarefree ((factors.map Prod.snd).prod).toPoly := by
  by_cases hrecursive : recursive = []
  · subst recursive
    change some (groupFactors strata) = some factors at hresult
    have : factors = groupFactors strata := Option.some.inj hresult.symm
    subst factors
    rw [supportProduct_groupFactors]
    exact hstrataSquarefree
  · have hnotempty : recursive.isEmpty ≠ true := by
      cases recursive with
      | nil => contradiction
      | cons z rest => simp
    unfold refineFactors at hresult
    rw [if_neg hnotempty] at hresult
    cases hbuild : BatchRemainder.build M (recursive.map Prod.snd) with
    | nil => simp [hbuild] at hresult
    | cons tree trees =>
      cases trees with
      | cons next rest => simp [hbuild] at hresult
      | nil =>
        rw [hbuild] at hresult
        let refined := refineRoot M D tree strata
        cases hmixed : labelIntersections p recursive refined.1 with
        | none => simp [refined, hmixed] at hresult
        | some mixed =>
          cases honly : recursiveOnly p M recursive refined.1 with
          | none => simp [refined, hmixed, honly] at hresult
          | some only =>
            have hout : factors = groupFactors (refined.2 ++ mixed ++ only) := by
              simpa [refined, hmixed, honly] using hresult.symm
            subst factors
            have hleaves : tree.leaves = recursive.map Prod.snd := by
              have h := BatchRemainder.buildForest_leaves M (recursive.map Prod.snd).length
                ((recursive.map Prod.snd).map BatchRemainder.Tree.leaf)
              rw [← BatchRemainder.build, hbuild] at h
              have heq : ((recursive.map Prod.snd).map BatchRemainder.Tree.leaf).flatMap
                  BatchRemainder.Tree.leaves = recursive.map Prod.snd := by
                induction recursive.map Prod.snd with
                | nil => rfl
                | cons q rest ih => simp [BatchRemainder.Tree.leaves, ih]
              simpa using h.trans heq
            have hwell : tree.WellFormed := by
              have hw : ∀ t ∈ BatchRemainder.build M (recursive.map Prod.snd),
                  t.WellFormed := by
                apply BatchRemainder.buildForest_wellFormed
                intro t ht
                obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
                obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
                exact hrecursiveMonic z hz
              exact hw tree (by simp [hbuild])
            have htreeProduct : tree.product = (recursive.map Prod.snd).prod := by
              rw [tree_product_eq_prod tree hwell, hleaves]
            have hdest : ∀ z ∈ refined.1, ∃ a, (a, z.2.1) ∈ recursive := by
              intro z hz
              have hleaf := routeTagged_leaf_mem M D tree _ z hz
              rw [hleaves] at hleaf
              obtain ⟨a, ha, heq⟩ := List.mem_map.mp hleaf
              rcases a with ⟨label, q⟩
              simp only at heq
              subst q
              exact ⟨label, ha⟩
            have hroutedMonic : ∀ z ∈ refined.1, z.2.2.monic :=
              refineRoot_routed_monic M D tree strata hstrataMonic
            let R := (refined.1.map fun z : ℕ × CPolynomial F × CPolynomial F => z.2.2).prod
            let S := (refined.2.map Prod.snd).prod
            let L := (only.map Prod.snd).prod
            let Q := (recursive.map Prod.snd).prod
            have hRS : R * S = (strata.map Prod.snd).prod := by
              simpa [R, S, refined] using refineRoot_exact M D tree strata hstrataMonic
            have hLR : L * R = Q := by
              have hsupp := recursiveOnly_supportProduct
                p M recursive refined.1 only hroutedMonic honly
              rw [routedAtProduct_partition recursive refined.1 hrecursiveNodup hdest] at hsupp
              simpa [L, R, Q] using hsupp
            have hcSQ : IsCoprime S.toPoly Q.toPoly := by
              have hc := refineRoot_residueOnly_coprime M D tree strata hstrataMonic
                (fun z hz => hstrataSquarefree.squarefree_of_dvd
                  (cpoly_toPoly_dvd_prod_of_mem z.2 _
                    (List.mem_map.mpr ⟨z, hz, rfl⟩)))
              simpa [S, Q, refined, htreeProduct] using hc
            have hsRS : Squarefree (R.toPoly * S.toPoly) := by
              rw [← toPoly_mul, hRS]
              exact hstrataSquarefree
            have hsLR : Squarefree (L.toPoly * R.toPoly) := by
              rw [← toPoly_mul, hLR]
              exact hrecursiveSquarefree
            have hLdvdQ : L.toPoly ∣ Q.toPoly := by
              refine ⟨R.toPoly, ?_⟩
              rw [← toPoly_mul, hLR]
            have hcSL : IsCoprime S.toPoly L.toPoly :=
              hcSQ.of_isCoprime_of_dvd_right hLdvdQ
            have hcRL : IsCoprime R.toPoly L.toPoly :=
              (IsRelPrime.of_squarefree_mul hsLR).isCoprime.symm
            have hsSR : Squarefree (S.toPoly * R.toPoly) := by
              simpa [mul_comm] using hsRS
            have hsSRL : Squarefree ((S.toPoly * R.toPoly) * L.toPoly) :=
              squarefree_mul_iff.mpr
                ⟨(hcSL.mul_left hcRL).isRelPrime, hsSR, hsLR.of_mul_left⟩
            rw [supportProduct_groupFactors, List.map_append, List.prod_append,
              List.map_append, List.prod_append, labelIntersections_erase p recursive
                refined.1 mixed hmixed]
            simpa [R, S, L, toPoly_mul, mul_assoc] using hsSRL

/-- Refinement and grouping retain positive labels and monic nonunit factors. -/
theorem refineFactors_positive_monic
    (p : ℕ) (hp : 0 < p) (M : MulContext F) (D : ModContext F)
    (strata recursive factors : List (ℕ × CPolynomial F))
    (hstrata : ∀ z ∈ strata, 0 < z.1 ∧ z.2.monic)
    (hrecursive : ∀ z ∈ recursive, 0 < z.1 ∧ z.2.monic)
    (hresult : refineFactors p M D strata recursive = some factors) :
    ∀ z ∈ factors, 0 < z.1 ∧ z.2.monic ∧ z.2 ≠ 1 := by
  by_cases hrecursiveEmpty : recursive = []
  · subst recursive
    change some (groupFactors strata) = some factors at hresult
    have : factors = groupFactors strata := Option.some.inj hresult.symm
    subst factors
    exact groupFactors_positive_monic_nonunit strata hstrata
  · have hnotempty : recursive.isEmpty ≠ true := by
      cases recursive with
      | nil => contradiction
      | cons z rest => simp
    unfold refineFactors at hresult
    rw [if_neg hnotempty] at hresult
    cases hbuild : BatchRemainder.build M (recursive.map Prod.snd) with
    | nil => simp [hbuild] at hresult
    | cons tree trees =>
      cases trees with
      | cons next rest => simp [hbuild] at hresult
      | nil =>
        rw [hbuild] at hresult
        let refined := refineRoot M D tree strata
        cases hmixed : labelIntersections p recursive refined.1 with
        | none => simp [refined, hmixed] at hresult
        | some mixed =>
          cases honly : recursiveOnly p M recursive refined.1 with
          | none => simp [refined, hmixed, honly] at hresult
          | some only =>
            have hout : factors = groupFactors (refined.2 ++ mixed ++ only) := by
              simpa [refined, hmixed, honly] using hresult.symm
            subst factors
            have hroutedMonic : ∀ z ∈ refined.1, z.2.2.monic :=
              refineRoot_routed_monic M D tree strata (fun z hz => (hstrata z hz).2)
            have hroutedPositive : ∀ z ∈ refined.1, 0 < z.1 :=
              refineRoot_routed_label_positive M D tree strata
                (fun z hz => (hstrata z hz).2) (fun z hz => (hstrata z hz).1)
            have hresidue : ∀ z ∈ refined.2, 0 < z.1 ∧ z.2.monic :=
              refineRoot_residueOnly_positive_monic M D tree strata
                (fun z hz => (hstrata z hz).1) (fun z hz => (hstrata z hz).2)
            have hmixedShape : ∀ z ∈ mixed, 0 < z.1 ∧ z.2.monic :=
              labelIntersections_positive_monic p recursive refined.1 mixed
                hroutedPositive hroutedMonic hmixed
            have honlyShape : ∀ z ∈ only, 0 < z.1 ∧ z.2.monic :=
              recursiveOnly_positive_monic p hp M recursive refined.1 only
                hrecursive hroutedMonic honly
            apply groupFactors_positive_monic_nonunit
            intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · rcases List.mem_append.mp hz with hz | hz
              · exact hresidue z hz
              · exact hmixedShape z hz
            · exact honlyShape z hz

end CompPoly.CPolynomial.FullSquarefreeDecomposition.Driver
