/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.CotangentMixing
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.BalancedClasses
public import ArkLib.Data.Graph.GabberGalilConstruction.PowerChoice
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Cotangent classes from the original agreement hypothesis

A regular chart supplies the following intrinsic hypothesis: fewer than k agreeing cotangent
vectors lie in any proper subspace. This file begins deriving the selection inputs directly from
that statement. In particular, it proves that every independent partial selection of size below
the cotangent dimension has an agreeing label outside its span, including the odd leftover step.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open GabberGalil
open ReedSolomon.HiddenDerivative.SquareSystems

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Projective class of a vector in the quotient by `U`; vectors in `U` get the distinguished
`none` key. This keeps all agreeing labels, including quotient-zero labels, explicit. -/
noncomputable def quotientProjectiveKey (U : Submodule F V) (v : V) :
    Option (Projectivization F (V ⧸ U)) := by
  classical
  exact if h : U.mkQ v = 0 then none else some (Projectivization.mk F (U.mkQ v) h)

@[simp] theorem quotientProjectiveKey_eq_none_iff (U : Submodule F V) (v : V) :
    quotientProjectiveKey U v = none ↔ v ∈ U := by
  rw [quotientProjectiveKey]
  split_ifs with h
  · simpa [Submodule.mkQ_apply] using h
  · simp only [false_iff]
    intro hv
    apply h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv

/-- Membership in `U` plus the line through `v` forces the same nonzero quotient-projective
class. -/
theorem quotientProjectiveKey_eq_of_mem_sup {U : Submodule F V} {v w : V}
    (hv : v ∉ U) (hw : w ∉ U) (hmem : w ∈ U ⊔ F ∙ v) :
    quotientProjectiveKey U w = quotientProjectiveKey U v := by
  have hvQ : U.mkQ v ≠ 0 := by
    intro hz
    apply hv
    rw [← Submodule.Quotient.mk_eq_zero U]
    simpa [Submodule.mkQ_apply] using hz
  have hwQ : U.mkQ w ≠ 0 := by
    intro hz
    apply hw
    rw [← Submodule.Quotient.mk_eq_zero U]
    simpa [Submodule.mkQ_apply] using hz
  rw [quotientProjectiveKey, dif_neg hwQ, quotientProjectiveKey, dif_neg hvQ]
  congr 1
  rw [Projectivization.mk_eq_mk_iff']
  rw [Submodule.mem_sup] at hmem
  obtain ⟨u, hu, line, hline, rfl⟩ := hmem
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hline
  refine ⟨a, ?_⟩
  have huQ : U.mkQ u = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact hu
  simp only [map_add, map_smul, huQ, zero_add]

/-- Equal nonzero quotient-projective keys put the second vector in the span obtained by
adjoining the first vector to `U`. -/
theorem mem_sup_of_quotientProjectiveKey_eq {U : Submodule F V} {v w : V}
    (hv : v ∉ U) (hw : w ∉ U)
    (heq : quotientProjectiveKey U v = quotientProjectiveKey U w) :
    w ∈ U ⊔ F ∙ v := by
  have hvQ : U.mkQ v ≠ 0 := by
    intro hz
    apply hv
    rw [← Submodule.Quotient.mk_eq_zero U]
    simpa [Submodule.mkQ_apply] using hz
  have hwQ : U.mkQ w ≠ 0 := by
    intro hz
    apply hw
    rw [← Submodule.Quotient.mk_eq_zero U]
    simpa [Submodule.mkQ_apply] using hz
  rw [quotientProjectiveKey, dif_neg hvQ, quotientProjectiveKey, dif_neg hwQ] at heq
  have hprojective : Projectivization.mk F (U.mkQ w) hwQ =
      Projectivization.mk F (U.mkQ v) hvQ := by
    exact Option.some.inj heq.symm
  rw [Projectivization.mk_eq_mk_iff'] at hprojective
  obtain ⟨a, ha⟩ := hprojective
  rw [Submodule.mem_sup]
  refine ⟨w - a • v, ?_, a • v, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero U]
    change U.mkQ (w - a • v) = 0
    rw [map_sub, map_smul, ha, sub_self]
  · abel

/-- Different nonzero quotient-projective keys force the second vector to escape the span after
adjoining the first. -/
theorem not_mem_sup_of_quotientProjectiveKey_ne {U : Submodule F V} {v w : V}
    (hv : v ∉ U) (hw : w ∉ U)
    (hne : quotientProjectiveKey U v ≠ quotientProjectiveKey U w) :
    w ∉ U ⊔ F ∙ v := by
  intro hmem
  exact hne (quotientProjectiveKey_eq_of_mem_sup hv hw hmem).symm

/-- The agreeing labels whose cotangent vectors lie in a specified subspace. -/
noncomputable def agreeingInSubspace {n : ℕ} (agreeing : Finset (Fin n))
    (pool : Fin n → V) (U : Submodule F V) : Finset (Fin n) := by
  classical
  exact agreeing.filter fun i ↦ pool i ∈ U

/-- Every proper cotangent subspace contains fewer than k agreeing position differentials. -/
def ProperSubspaceAgreementBound {n : ℕ} (agreeing : Finset (Fin n))
    (pool : Fin n → V) (k : ℕ) : Prop :=
  ∀ U : Submodule F V, U < ⊤ →
    (agreeingInSubspace agreeing pool U).card < k

/-- An independent set smaller than the ambient dimension spans a proper subspace. -/
theorem span_lt_top_of_linearIndepOn_card_lt_finrank {n : ℕ}
    {pool : Fin n → V} {selected : Finset (Fin n)}
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hcard : selected.card < Module.finrank F V) :
    Submodule.span F (pool '' (selected : Set (Fin n))) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have himage : pool '' (selected : Set (Fin n)) =
      Set.range (fun i : {i // i ∈ (selected : Set (Fin n))} ↦ pool i) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
  have hfinrank : Module.finrank F
      (Submodule.span F (pool '' (selected : Set (Fin n)))) = selected.card := by
    rw [himage]
    simpa using finrank_span_eq_card hindependent
  rw [htop, finrank_top] at hfinrank
  omega

/-- The agreement bound produces an agreeing vector outside the span of every independent
partial selection below full rank. -/
theorem exists_agreeing_outside_span {n k : ℕ}
    (agreeing : Finset (Fin n)) (pool : Fin n → V)
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing pool k)
    (hk : k ≤ agreeing.card)
    (selected : Finset (Fin n))
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hcard : selected.card < Module.finrank F V) :
    ∃ i ∈ agreeing, pool i ∉ Submodule.span F (pool '' (selected : Set (Fin n))) := by
  let U := Submodule.span F (pool '' (selected : Set (Fin n)))
  have hproper : U < ⊤ :=
    span_lt_top_of_linearIndepOn_card_lt_finrank hindependent hcard
  have hsmall := hbound U hproper
  by_contra hno
  push Not at hno
  have hfilter : agreeingInSubspace agreeing pool U = agreeing := by
    classical
    ext i
    simp only [agreeingInSubspace, Finset.mem_filter]
    exact and_iff_left_of_imp (hno i)
  rw [hfilter] at hsmall
  omega

/-- The odd leftover after all pairs follows from the original agreement hypothesis. -/
theorem odd_escape_of_original_hypotheses {n k pairs : ℕ}
    (agreeing : Finset (Fin n)) (pool : Fin n → V)
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing pool k)
    (hk : k ≤ agreeing.card)
    (hdim : Module.finrank F V = 2 * pairs + 1) :
    ∀ selected : Finset (Fin n),
      LinearIndepOn F pool (selected : Set (Fin n)) → selected.card = 2 * pairs →
      ∃ i ∈ agreeing, pool i ∉ Submodule.span F (pool '' (selected : Set (Fin n))) := by
  intro selected hindependent hcard
  obtain ⟨i, hi, hout⟩ := exists_agreeing_outside_span agreeing pool hbound hk
    selected hindependent (by omega)
  exact ⟨i, hi, hout⟩

/-- Adjoining one vector to a subspace that is at least two dimensions below the ambient space
still gives a proper subspace. -/
theorem sup_span_singleton_lt_top_of_finrank_add_one_lt [FiniteDimensional F V]
    (U : Submodule F V) (v : V)
    (hdim : Module.finrank F U + 1 < Module.finrank F V) :
    U ⊔ F ∙ v < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  by_cases hv : v ∈ U
  · have hspan : F ∙ v ≤ U := Submodule.span_le.mpr fun x hx ↦ by
      rw [Set.mem_singleton_iff.mp hx]
      exact hv
    have : U = ⊤ := by simpa [sup_eq_left.mpr hspan] using htop
    rw [this, finrank_top] at hdim
    omega
  · have hfinrank := Submodule.finrank_sup_span_singleton hv
    rw [htop, finrank_top] at hfinrank
    omega

/-- A zero class together with one quotient-parallel class lies in a proper original subspace,
so the original agreement hypothesis bounds its number of agreeing labels by `k - 1`. -/
theorem agreement_class_bound [FiniteDimensional F V] {n k : ℕ}
    (agreeing : Finset (Fin n)) (pool : Fin n → V)
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing pool k)
    (U : Submodule F V) (v : V)
    (hdim : Module.finrank F U + 1 < Module.finrank F V) :
    (agreeingInSubspace agreeing pool (U ⊔ F ∙ v)).card < k := by
  exact hbound (U ⊔ F ∙ v)
    (sup_span_singleton_lt_top_of_finrank_add_one_lt U v hdim)

/-- At an independent partial selection with at least two ranks left, every quotient-parallel
class, including all quotient-zero agreeing labels, has size below `k`. -/
theorem selected_agreement_class_bound [FiniteDimensional F V] {n k : ℕ}
    (agreeing : Finset (Fin n)) (pool : Fin n → V)
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing pool k)
    (selected : Finset (Fin n))
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hremaining : selected.card + 1 < Module.finrank F V) (v : V) :
    (agreeingInSubspace agreeing pool
      (Submodule.span F (pool '' (selected : Set (Fin n))) ⊔ F ∙ v)).card < k := by
  have himage : pool '' (selected : Set (Fin n)) =
      Set.range (fun i : {i // i ∈ (selected : Set (Fin n))} ↦ pool i) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
  have hspanrank : Module.finrank F
      (Submodule.span F (pool '' (selected : Set (Fin n)))) = selected.card := by
    rw [show Submodule.span F (pool '' (selected : Set (Fin n))) =
      Submodule.span F (Set.range (fun i : {i // i ∈ (selected : Set (Fin n))} ↦ pool i))
      by rw [himage]]
    simpa using finrank_span_eq_card hindependent
  let U := Submodule.span F (pool '' (selected : Set (Fin n)))
  have hUrank : Module.finrank F U = selected.card := hspanrank
  apply agreement_class_bound agreeing pool hbound U v
  omega

/-- The original proper-subspace agreement bound yields the two large quotient-projective
classes needed by the graph argument. The integer `agreeing.card - k + 1` is the agreement
excess, and each output set has at least one third of that excess. -/
theorem exists_cotangent_separated_of_original_hypotheses [FiniteDimensional F V]
    {n k : ℕ} (agreeing : Finset (Fin n)) (pool : Fin n → V)
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing pool k)
    (hk : k ≤ agreeing.card) (selected : Finset (Fin n))
    (hindependent : LinearIndepOn F pool (selected : Set (Fin n)))
    (hremaining : selected.card + 1 < Module.finrank F V) :
    ∃ I J : Finset (Fin n),
      CotangentSeparated (F := F) pool selected I J ∧
      I ⊆ agreeing ∧ J ⊆ agreeing ∧
      agreeing.card - k + 1 ≤ 3 * I.card ∧
      agreeing.card - k + 1 ≤ 3 * J.card := by
  classical
  let U := Submodule.span F (pool '' (selected : Set (Fin n)))
  let zero := agreeingInSubspace agreeing pool U
  let active := agreeing.filter fun i ↦ pool i ∉ U
  let gap := agreeing.card - k + 1
  let key : Fin n → Option (Projectivization F (V ⧸ U)) :=
    fun i ↦ quotientProjectiveKey U (pool i)
  have hUproper : U < ⊤ :=
    span_lt_top_of_linearIndepOn_card_lt_finrank hindependent (by omega)
  have hzero : zero.card < k := hbound U hUproper
  have hpartition : zero.card + active.card = agreeing.card := by
    simpa only [zero, active, agreeingInSubspace] using
      Finset.card_filter_add_card_filter_not (s := agreeing) (fun i ↦ pool i ∈ U)
  have hgapPos : 0 < gap := by
    dsimp [gap]
    omega
  have hgapActive : gap ≤ active.card := by
    dsimp [gap]
    omega
  have hfiber : ∀ c, (active.filter fun i ↦ key i = c).card ≤ active.card - gap := by
    intro c
    let fiber := active.filter fun i ↦ key i = c
    by_cases hfiberEmpty : fiber = ∅
    · simp [fiber, hfiberEmpty]
    · obtain ⟨anchor, hanchor⟩ := Finset.nonempty_iff_ne_empty.mpr hfiberEmpty
      have hanchorActive : anchor ∈ active := (Finset.mem_filter.mp hanchor).1
      have hanchorOutside : pool anchor ∉ U := (Finset.mem_filter.mp hanchorActive).2
      have hdisjoint : Disjoint zero fiber := by
        rw [Finset.disjoint_left]
        intro i hizero hifiber
        have hiU : pool i ∈ U := by
          exact (Finset.mem_filter.mp hizero).2
        have hiOutside : pool i ∉ U := by
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hifiber).1).2
        exact hiOutside hiU
      have hunionSubset : zero ∪ fiber ⊆
          agreeingInSubspace agreeing pool (U ⊔ F ∙ pool anchor) := by
        intro i hi
        rw [Finset.mem_union] at hi
        apply Finset.mem_filter.mpr
        rcases hi with hizero | hifiber
        · exact ⟨(Finset.mem_filter.mp hizero).1,
            Submodule.mem_sup_left (Finset.mem_filter.mp hizero).2⟩
        · have hiActive : i ∈ active := (Finset.mem_filter.mp hifiber).1
          have hiAgreeing : i ∈ agreeing := (Finset.mem_filter.mp hiActive).1
          have hiOutside : pool i ∉ U := (Finset.mem_filter.mp hiActive).2
          have hiKey : key i = c := (Finset.mem_filter.mp hifiber).2
          have hanchorKey : key anchor = c := (Finset.mem_filter.mp hanchor).2
          exact ⟨hiAgreeing, mem_sup_of_quotientProjectiveKey_eq hanchorOutside hiOutside
            (by simpa [key] using hanchorKey.trans hiKey.symm)⟩
      have hclass := selected_agreement_class_bound agreeing pool hbound selected hindependent
        hremaining (pool anchor)
      have hunionCard : (zero ∪ fiber).card = zero.card + fiber.card :=
        Finset.card_union_of_disjoint hdisjoint
      have hsumLt : zero.card + fiber.card < k := by
        rw [← hunionCard]
        exact (Finset.card_le_card hunionSubset).trans_lt hclass
      change fiber.card ≤ active.card - gap
      apply Nat.le_sub_of_add_le
      dsimp [gap]
      omega
  obtain ⟨I, J, hIJ, hunion, hI, hJ, hkeys⟩ :=
    exists_balanced_fiber_sets active key gap hgapPos hgapActive hfiber
  have hIsub : I ⊆ active := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_left J hx
  have hJsub : J ⊆ active := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_right I hx
  refine ⟨I, J, ⟨hIJ, ?_⟩, ?_, ?_, hI, hJ⟩
  · intro i hi j hj
    have hiOutside : pool i ∉ U := (Finset.mem_filter.mp (hIsub hi)).2
    have hjOutside : pool j ∉ U := (Finset.mem_filter.mp (hJsub hj)).2
    have hkeyNe : quotientProjectiveKey U (pool i) ≠ quotientProjectiveKey U (pool j) := by
      simpa only [key] using hkeys i hi j hj
    refine ⟨hiOutside, ?_⟩
    have hjEscape := not_mem_sup_of_quotientProjectiveKey_ne hiOutside hjOutside hkeyNe
    simpa only [Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert,
      sup_comm] using hjEscape
  · intro i hi
    exact (Finset.mem_filter.mp (hIsub hi)).1
  · intro i hi
    exact (Finset.mem_filter.mp (hJsub hi)).1

/-- If enough agreeing coordinate functionals avoid every proper subspace, then the full
coordinate map is injective. This derives coverage for the direct-system route from the same
original agreement hypothesis used by the fixed-gap route. -/
theorem coordinateMap_injective_of_original_hypotheses [FiniteDimensional F V]
    {n k : ℕ} (agreeing : Finset (Fin n)) (map : V →ₗ[F] (Fin n → F))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional map) k)
    (hk : k ≤ agreeing.card) : Function.Injective map := by
  let U := Submodule.span F
    (coordinateFunctional map '' (agreeing : Set (Fin n)))
  have hUtop : U = ⊤ := by
    by_contra hne
    have hproper : U < ⊤ := lt_top_iff_ne_top.mpr hne
    have hsmall := hbound U hproper
    have hall : agreeingInSubspace agreeing (coordinateFunctional map) U = agreeing := by
      classical
      ext i
      simp only [agreeingInSubspace, Finset.mem_filter]
      constructor
      · exact fun hi ↦ hi.1
      · intro hi
        exact ⟨hi, Submodule.subset_span ⟨i, hi, rfl⟩⟩
    rw [hall] at hsmall
    omega
  intro x y hxy
  have hzero : map (x - y) = 0 := by
    simpa only [map_sub, sub_eq_zero] using hxy
  have hall (functional : Module.Dual F V) : functional (x - y) = 0 := by
    have hfunctional : functional ∈ U := by rw [hUtop]; trivial
    refine Submodule.span_induction (p := fun phi _ ↦ phi (x - y) = 0) ?_ ?_ ?_ ?_
      hfunctional
    · intro phi hphi
      obtain ⟨i, _hi, rfl⟩ := hphi
      exact congrFun hzero i
    · simp
    · intro phi psi _ _ hphi hpsi
      simp [hphi, hpsi]
    · intro scalar phi _ hphi
      simp [hphi]
  have hxyZero : x - y = 0 := by
    apply (Module.evalEquiv F V).injective
    ext functional
    simpa [Module.evalEquiv_apply, Module.Dual.eval_apply] using hall functional
  exact sub_eq_zero.mp hxyZero

/-- The coordinates indexed by the agreeing set already determine a tangent vector. -/
theorem agreeingCoordinateMap_injective_of_original_hypotheses [FiniteDimensional F V]
    {n k : ℕ} (agreeing : Finset (Fin n)) (map : V →ₗ[F] (Fin n → F))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional map) k)
    (hk : k ≤ agreeing.card) :
    Function.Injective
      (selectedCoordinateMap map (agreeing.orderEmbOfFin rfl)) := by
  let U := Submodule.span F
    (coordinateFunctional map '' (agreeing : Set (Fin n)))
  have hUtop : U = ⊤ := by
    by_contra hne
    have hproper : U < ⊤ := lt_top_iff_ne_top.mpr hne
    have hsmall := hbound U hproper
    have hall : agreeingInSubspace agreeing (coordinateFunctional map) U = agreeing := by
      classical
      ext i
      simp only [agreeingInSubspace, Finset.mem_filter]
      exact and_iff_left_of_imp fun hi ↦ Submodule.subset_span ⟨i, hi, rfl⟩
    rw [hall] at hsmall
    omega
  intro x y hxy
  have hzero : selectedCoordinateMap map (agreeing.orderEmbOfFin rfl) (x - y) = 0 := by
    simpa only [map_sub, sub_eq_zero] using hxy
  have hvanish (i : Fin n) (hi : i ∈ agreeing) : coordinateFunctional map i (x - y) = 0 := by
    have hirange : i ∈ Set.range (agreeing.orderEmbOfFin rfl) := by
      rwa [Finset.range_orderEmbOfFin]
    obtain ⟨j, rfl⟩ := hirange
    exact congrFun hzero j
  have hall (functional : Module.Dual F V) : functional (x - y) = 0 := by
    have hfunctional : functional ∈ U := by rw [hUtop]; trivial
    refine Submodule.span_induction (p := fun phi _ ↦ phi (x - y) = 0) ?_ ?_ ?_ ?_
      hfunctional
    · intro phi hphi
      obtain ⟨i, hi, rfl⟩ := hphi
      exact hvanish i hi
    · simp
    · intro phi psi _ _ hphi hpsi
      simp [hphi, hpsi]
    · intro scalar phi _ hphi
      simp [hphi]
  have hxyZero : x - y = 0 := by
    apply (Module.evalEquiv F V).injective
    ext functional
    simpa [Module.evalEquiv_apply, Module.Dual.eval_apply] using hall functional
  exact sub_eq_zero.mp hxyZero

/-- The exhaustive direct-system producer contains a nonsingular system under the original
agreement hypothesis; no caller-supplied tangent coverage premise remains. -/
theorem directSystems_contains_capture_of_original_hypotheses
    {W P : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [DecidableEq P] {n k r : ℕ} (hypersurface : P) (equations : Fin n → P)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        directSystems r hypersurface equations ∧
      selected ⊆ agreeing ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  let positions : Fin agreeing.card ↪ Fin n := (agreeing.orderEmbOfFin rfl).toEmbedding
  have htangent : Function.Injective
      ((selectedCoordinateMap pool positions).comp normal.ker.subtype) := by
    exact agreeingCoordinateMap_injective_of_original_hypotheses agreeing
      (pool.comp normal.ker.subtype) hbound hk
  obtain ⟨chosen, hchosen⟩ := exists_injective_normalSelectedMap normal
    (selectedCoordinateMap pool positions) hdim hnormal htangent
  let full := chosen.trans positions
  have hfull : Function.Injective (normalSelectedMap normal pool full) := hchosen
  let selected := Finset.univ.map full
  have hcard : selected.card = r := card_map_univ_embedding full
  refine ⟨selected, hcard, squareSystemRows_mem_enumerate _ _ _ _, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
    change positions (chosen j) ∈ agreeing
    change agreeing.orderEmbOfFin rfl (chosen j) ∈ agreeing
    have hjrange : agreeing.orderEmbOfFin rfl (chosen j) ∈
        Set.range (agreeing.orderEmbOfFin rfl) := ⟨chosen j, rfl⟩
    rwa [Finset.range_orderEmbOfFin] at hjrange
  · exact rowSubsetEmbedding_preserves_injective normal pool full hfull

/-- The all-subsets producer contains an actual common-zero system with injective supplied
differential, using only the equations' value and differential semantics at the wanted point. -/
theorem directSystems_contains_commonZero_capture_of_original_hypotheses
    {W P : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [DecidableEq P] {n k r : ℕ} (hypersurface : P) (equations : Fin n → P)
    (evaluate : P → F) (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hhypersurface : evaluate hypersurface = 0)
    (hagree : ∀ i ∈ agreeing, evaluate (equations i) = 0) :
    ∃ (selected : Finset (Fin n)) (hcard : selected.card = r),
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        directSystems r hypersurface equations ∧
      selected ⊆ agreeing ∧
      (∀ j, evaluate
        (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) j) = 0) ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  obtain ⟨selected, hcard, hsystem, hsubset, hinjective⟩ :=
    directSystems_contains_capture_of_original_hypotheses hypersurface equations normal pool
      hdim hnormal agreeing hbound hk
  exact ⟨selected, hcard, hsystem, hsubset,
    squareSystemRows_commonZero_of_subset hypersurface equations evaluate agreeing selected
      hcard hsubset hhypersurface hagree,
    hinjective⟩

/-- If the agreement excess has density at least `epsilonNumerator / epsilonDenominator`, then
the balanced threshold has padded density at least one twelfth as large. -/
theorem epsilonOverTwelve_le_balancedThreshold {n gap epsilonNumerator epsilonDenominator : ℕ}
    (hn : 0 < n)
    (hdensity : epsilonNumerator * n ≤ epsilonDenominator * gap) :
    epsilonNumerator * paddedSize n ≤
      12 * epsilonDenominator * thirdCeil gap := by
  calc
    epsilonNumerator * paddedSize n ≤ epsilonNumerator * (4 * n) :=
      Nat.mul_le_mul_left _ (paddedSize_le_four_mul hn)
    _ = 4 * (epsilonNumerator * n) := by ac_rfl
    _ ≤ 4 * (epsilonDenominator * gap) := Nat.mul_le_mul_left 4 hdensity
    _ ≤ 4 * (epsilonDenominator * (3 * thirdCeil gap)) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ (le_three_mul_thirdCeil gap))
    _ = 12 * epsilonDenominator * thirdCeil gap := by ac_rfl

/-- Conditional on the exact Gabber--Galil energy estimate, the executable powered selector
contains an even-rank nonsingular system directly from the original proper-subspace agreement
hypothesis. The only analytic side condition is the displayed normalized power inequality. -/
theorem fixedGapSelections_contains_even_capture_of_original_hypotheses
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n k pairs power : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n))
    (hnumeric : ((25 : ℝ) / 32) ^ power * (paddedSize n : ℝ) ^ 2 <
      (thirdCeil (agreeing.card - k + 1) : ℝ) ^ 2) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ∈ fixedGapSelections n hn (2 * pairs) power ∧
      selected ⊆ agreeing ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  let tangentPool := coordinateFunctional (pool.comp normal.ker.subtype)
  have hrange : LinearMap.range normal = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hnormal)
  have htangentDim : Module.finrank F normal.ker = 2 * pairs := by
    have hrankNullity := normal.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrankNullity
    omega
  have hdualDim : Module.finrank F (Module.Dual F normal.ker) = 2 * pairs := by
    simpa [Subspace.dual_finrank_eq] using htangentDim
  have hgapPos : 0 < agreeing.card - k + 1 := by omega
  have hmixing := connectsLargeSets_poweredEdges hn hGG (thirdCeil_pos hgapPos) hnumeric
  apply fixedGapSelections_contains_even_capture_of_mixing hn normal pool agreeing
    hdim hnormal hmixing
  intro selected hindependent hcard heven
  obtain ⟨q, hq⟩ := heven
  obtain ⟨I, J, hseparated, hIsub, hJsub, hI, hJ⟩ :=
    exists_cotangent_separated_of_original_hypotheses agreeing tangentPool hbound hk
      selected hindependent (by rw [hdualDim]; omega)
  exact ⟨I, J, hseparated, hIsub, hJsub, thirdCeil_le_of_le_three_mul hI,
    thirdCeil_le_of_le_three_mul hJ⟩

/-- The odd-rank version derives both every paired augmentation and the final leftover rank from
the original proper-subspace agreement hypothesis. -/
theorem fixedGapSelections_contains_odd_capture_of_original_hypotheses
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n k pairs power : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n))
    (hnumeric : ((25 : ℝ) / 32) ^ power * (paddedSize n : ℝ) ^ 2 <
      (thirdCeil (agreeing.card - k + 1) : ℝ) ^ 2) :
    ∃ selected, ∃ hcard : selected.card = 2 * pairs + 1,
      selected ∈ fixedGapSelections n hn (2 * pairs + 1) power ∧
      selected ⊆ agreeing ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  let tangentPool := coordinateFunctional (pool.comp normal.ker.subtype)
  have hrange : LinearMap.range normal = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hnormal)
  have htangentDim : Module.finrank F normal.ker = 2 * pairs + 1 := by
    have hrankNullity := normal.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrankNullity
    omega
  have hdualDim : Module.finrank F (Module.Dual F normal.ker) = 2 * pairs + 1 := by
    simpa [Subspace.dual_finrank_eq] using htangentDim
  have hgapPos : 0 < agreeing.card - k + 1 := by omega
  have hmixing := connectsLargeSets_poweredEdges hn hGG (thirdCeil_pos hgapPos) hnumeric
  apply fixedGapSelections_contains_odd_capture_of_mixing hn normal pool agreeing
    hdim hnormal hmixing
  · intro selected hindependent hcard heven
    obtain ⟨q, hq⟩ := heven
    obtain ⟨I, J, hseparated, hIsub, hJsub, hI, hJ⟩ :=
      exists_cotangent_separated_of_original_hypotheses agreeing tangentPool hbound hk
        selected hindependent (by rw [hdualDim]; omega)
    exact ⟨I, J, hseparated, hIsub, hJsub, thirdCeil_le_of_le_three_mul hI,
      thirdCeil_le_of_le_three_mul hJ⟩
  · intro selected hindependent hcard
    apply odd_escape_of_original_hypotheses agreeing tangentPool hbound hk hdualDim
      selected hindependent hcard

/-- Fully executable even-rank fixed-gap selection. Its finite search chooses the least power
satisfying mixing, so the exact energy estimate is the only spectral premise. -/
theorem fixedGapSelections_contains_even_capture_of_exactEnergy
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n k pairs : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n)) :
    let power := firstMixingPower (paddedSize n) (thirdCeil (agreeing.card - k + 1))
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ∈ fixedGapSelections n hn (2 * pairs) power ∧
      selected ⊆ agreeing ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  dsimp only
  apply fixedGapSelections_contains_even_capture_of_original_hypotheses hn normal pool
    hdim hnormal agreeing hbound hk hGG
  apply firstMixingPower_spec
  · exact lt_of_lt_of_le hn (le_paddedSize n)
  · exact thirdCeil_pos (by omega)

/-- Fully executable odd-rank fixed-gap selection, including the final unpaired rank. -/
theorem fixedGapSelections_contains_odd_capture_of_exactEnergy
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {n k pairs : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n)) :
    let power := firstMixingPower (paddedSize n) (thirdCeil (agreeing.card - k + 1))
    ∃ selected, ∃ hcard : selected.card = 2 * pairs + 1,
      selected ∈ fixedGapSelections n hn (2 * pairs + 1) power ∧
      selected ⊆ agreeing ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  dsimp only
  apply fixedGapSelections_contains_odd_capture_of_original_hypotheses hn normal pool
    hdim hnormal agreeing hbound hk hGG
  apply firstMixingPower_spec
  · exact lt_of_lt_of_le hn (le_paddedSize n)
  · exact thirdCeil_pos (by omega)

/-- The executable even-rank fixed-gap family contains a supplied common-zero system whose
supplied square differential is injective. -/
theorem fixedGapSystems_contains_even_commonZero_capture_of_exactEnergy
    {W P : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [DecidableEq P] {n k pairs : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (hypersurface : P) (equations : Fin n → P) (evaluate : P → F)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = 2 * pairs + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n))
    (hhypersurface : evaluate hypersurface = 0)
    (hagree : ∀ i ∈ agreeing, evaluate (equations i) = 0) :
    let power := firstMixingPower (paddedSize n) (thirdCeil (agreeing.card - k + 1))
    ∃ selected, ∃ hcard : selected.card = 2 * pairs,
      selected ⊆ agreeing ∧
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        fixedGapSystems hn power hypersurface equations ∧
      (∀ j, evaluate
        (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) j) = 0) ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  dsimp only
  obtain ⟨selected, hcard, hselected, hsubset, hinjective⟩ :=
    fixedGapSelections_contains_even_capture_of_exactEnergy hn normal pool hdim hnormal
      agreeing hbound hk hGG
  refine ⟨selected, hcard, hsubset, ?_, ?_, hinjective⟩
  · simpa using squareSystemRows_mem_fixedGapSystems hypersurface equations hselected
  · exact squareSystemRows_commonZero_of_subset hypersurface equations evaluate agreeing selected
      hcard hsubset hhypersurface hagree

/-- The odd-rank fixed-gap family has the same common-zero and differential guarantee, including
the final agreeing label appended after pair growth. -/
theorem fixedGapSystems_contains_odd_commonZero_capture_of_exactEnergy
    {W P : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [DecidableEq P] {n k pairs : ℕ} [NeZero (ceilSqrt n)] (hn : 0 < n)
    (hypersurface : P) (equations : Fin n → P) (evaluate : P → F)
    (normal : W →ₗ[F] F) (pool : W →ₗ[F] (Fin n → F))
    (hdim : Module.finrank F W = (2 * pairs + 1) + 1) (hnormal : normal ≠ 0)
    (agreeing : Finset (Fin n))
    (hbound : ProperSubspaceAgreementBound (F := F) agreeing
      (coordinateFunctional (pool.comp normal.ker.subtype)) k)
    (hk : k ≤ agreeing.card) (hGG : ExactEnergyEstimate (ceilSqrt n))
    (hhypersurface : evaluate hypersurface = 0)
    (hagree : ∀ i ∈ agreeing, evaluate (equations i) = 0) :
    let power := firstMixingPower (paddedSize n) (thirdCeil (agreeing.card - k + 1))
    ∃ selected, ∃ hcard : selected.card = 2 * pairs + 1,
      selected ⊆ agreeing ∧
      squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) ∈
        fixedGapSystems hn power hypersurface equations ∧
      (∀ j, evaluate
        (squareSystemRows hypersurface equations (rowSubsetEmbedding selected hcard) j) = 0) ∧
      Function.Injective
        (normalSelectedMap normal pool (rowSubsetEmbedding selected hcard)) := by
  dsimp only
  obtain ⟨selected, hcard, hselected, hsubset, hinjective⟩ :=
    fixedGapSelections_contains_odd_capture_of_exactEnergy hn normal pool hdim hnormal
      agreeing hbound hk hGG
  refine ⟨selected, hcard, hsubset, ?_, ?_, hinjective⟩
  · simpa using squareSystemRows_mem_fixedGapSystems hypersurface equations hselected
  · exact squareSystemRows_commonZero_of_subset hypersurface equations evaluate agreeing selected
      hcard hsubset hhypersurface hagree

end ReedSolomon.ListDecoding.HigherOrderProducer
