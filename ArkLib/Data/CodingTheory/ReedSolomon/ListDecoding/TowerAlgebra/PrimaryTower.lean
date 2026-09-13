/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.SplitZeroUnit
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.PrimarySplit

/-! # Geometric correctness of primary splitting for nonreduced towers -/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial Polynomial.JetHornerMachine
open ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Membership in the canonical weak-invariant splitter exposes its actual D5 terminal branch. -/
theorem mem_splitZeroUnitPrimary_iff
    {r : TowerRepresentation (F := F)} {residual : CPolynomial (CPolynomial F)}
    {width : ℕ} {hr : r.NonreducedWellFormed width} {output : TaggedTower (F := F)} :
    output ∈ splitZeroUnitPrimary r residual hr ↔
      ∃ terminal ∈ factorTower (splitStatePrimary r residual hr),
        makeTagged? r .zero terminal.modulus terminal.gcdPolynomial.toCPolynomial =
            some output ∨
          makeTagged? r .unit terminal.modulus
            (terminalQuotientPolynomial (splitStatePrimary r residual hr) terminal) =
              some output := by
  simp only [splitZeroUnitPrimary, List.mem_flatMap, terminalChildren, List.mem_filterMap,
    List.mem_cons]
  aesop

/-- Canonical reductions specialize to the ordinary remainder of the residual power. -/
theorem splitStatePrimary_divisor_specialize
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : r.modulus.toPoly.eval₂ phi u = 0) :
    (splitStatePrimary r residual hr).divisor.specialize phi u =
      (specializeFiberCPolynomial residual phi u) ^ r.fiber.natDegree %ₘ
        specializeFiberCPolynomial r.fiber phi u := by
  simp only [splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
    TowerRepresentation.reduceElement, TowerRepresentation.reduceBase]
  rw [specialize_reduceFiberCoefficients phi u hr.1 hu]
  simp only [specializeFiberCPolynomial]
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hr.2.2.2.1,
    Polynomial.map_modByMonic _ ((CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1),
    CPolynomial.toPoly_pow, Polynomial.map_pow]

/-- The powered divisor and residual have the same zero set on parent points. -/
theorem splitStatePrimary_divisor_eval_eq_zero_iff
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    {K : Type} [Field K] (phi : F →+* K) (u v : K) (hp : r.Point phi u v) :
    ((splitStatePrimary r residual hr).divisor.specialize phi u).eval v = 0 ↔
      TowerRepresentation.evalNested residual phi u v = 0 := by
  rw [splitStatePrimary_divisor_specialize r residual hr phi u hp.1]
  have hmod := Polynomial.eval₂_modByMonic_eq_self_of_root hp.2
    (p := (specializeFiberCPolynomial residual phi u) ^ r.fiber.natDegree)
  simp only [Polynomial.eval₂_id] at hmod
  rw [hmod]
  simp only [Polynomial.eval_pow, TowerRepresentation.evalNested,
    pow_eq_zero_iff hr.2.2.2.2.1.ne']

/-- A terminal complementary factor is nonzero and has exactly the nonagreeing parent points. -/
theorem primary_terminal_complement
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (terminal : TerminalGCDBranch (F := F))
    (ht : terminal ∈ factorTower (splitStatePrimary r residual hr))
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hu : terminal.modulus.toPoly.eval₂ phi u = 0) :
    let state := splitStatePrimary r residual hr
    let Q := (makeTerminalQuotientBranch state terminal).quotient.specialize phi u
    Q ≠ 0 ∧ (Q.eval v = 0 ↔
      (state.dividend.specialize phi u).eval v = 0 ∧
        (state.divisor.specialize phi u).eval v ≠ 0) := by
  classical
  dsimp only
  let state := splitStatePrimary r residual hr
  let H := state.dividend.specialize phi u
  let E := specializeFiberCPolynomial residual phi u
  let Q := (makeTerminalQuotientBranch state terminal).quotient.specialize phi u
  have hH : H = specializeFiberCPolynomial r.fiber phi u := by
    simp only [H, state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial]
  have hmonic : H.Monic := by
    rw [hH]
    exact ((CPolynomial.monic_toPoly_iff r.fiber).mp hr.2.2.2.1).map _
  have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
    (by simpa [state, splitStatePrimary] using hr.2.2.2.1) terminal ht phi u hu
  have hassoc := factorTower_terminal_fieldGCD_associated state phi u terminal ht hu
  have hparent := factorTower_root_sound state phi u terminal ht hu
  have hcop : IsCoprime Q E := by
    apply PrimarySplit.quotient_isCoprime_residual_of_common_divisors hmonic.ne_zero
      (b := r.fiber.natDegree) (D := terminal.gcdPolynomial.specialize phi u)
      (S := state.divisor.specialize phi u)
    · rw [hH]
      change (r.fiber.toPoly.map _).natDegree ≤ r.fiber.natDegree
      rw [((CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1).natDegree_map,
        ← CPolynomial.natDegree_toPoly]
    · intro p hpH hpE
      rw [hH] at hpH
      rw [splitStatePrimary_divisor_specialize r residual hr phi u hparent,
        Polynomial.modByMonic_eq_sub_mul_div]
      exact dvd_sub hpE (dvd_mul_of_dvd_left hpH _)
    · intro p hpH hpS
      exact hassoc.dvd_iff_dvd_right.mpr
        (@EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X]) _ _ _ hpH hpS)
    · exact hfactor
  have hQne : Q ≠ 0 := by
    intro hz
    apply hmonic.ne_zero
    simpa [Q, hz] using hfactor.symm
  refine ⟨hQne, ?_⟩
  constructor
  · intro hQroot
    have hHroot : H.eval v = 0 := by
      change (state.dividend.specialize phi u).eval v = 0
      rw [← hfactor, Polynomial.eval_mul, hQroot, mul_zero]
    refine ⟨hHroot, ?_⟩
    intro hSroot
    have hEroot := (splitStatePrimary_divisor_eval_eq_zero_iff r residual hr phi u v
      ⟨hparent, by simpa only [hH, TowerRepresentation.evalNested] using hHroot⟩).mp hSroot
    obtain ⟨a, b, hab⟩ := hcop
    have hc := congrArg (fun P : K[X] => P.eval v) hab
    change Q.eval v = 0 at hQroot
    change E.eval v = 0 at hEroot
    simp [hQroot, hEroot] at hc
  · rintro ⟨hHroot, hSnonzero⟩
    have hproduct : (terminal.gcdPolynomial.specialize phi u).eval v * Q.eval v = 0 := by
      rw [← Polynomial.eval_mul, hfactor, hHroot]
    apply (mul_eq_zero.mp hproduct).resolve_left
    intro hDroot
    have hdvd : terminal.gcdPolynomial.specialize phi u ∣ state.divisor.specialize phi u :=
      hassoc.dvd_iff_dvd_left.mpr
        (@EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X]) _ _)
    obtain ⟨p, hp⟩ := hdvd
    apply hSnonzero
    rw [hp, Polynomial.eval_mul, hDroot, zero_mul]

/-- Every returned child point is a parent point, and its tag exactly records whether the tested
element vanishes there. -/
theorem splitZeroUnitPrimary_point_sound
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnitPrimary r residual hr)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : output.tower.Point phi u v) :
    r.Point phi u v ∧
      (output.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnitPrimary_iff.mp houtput
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitStatePrimary r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hraw := (restrictTower_point_iff r terminal.modulus
      terminal.gcdPolynomial.toCPolynomial phi u v hinvariants.2.1).mp hpoint
    have hbase := factorTower_root_sound state phi u terminal hterminal hraw.1
    have hassociated := factorTower_terminal_fieldGCD_associated
      state phi u terminal hterminal hraw.1
    have hterminalRoot : (terminal.gcdPolynomial.specialize phi u).eval v = 0 := by
      change (specializeFiberCPolynomial terminal.gcdPolynomial.toCPolynomial phi u).eval v = 0
      exact hraw.2
    have hgcdRoot : (fieldGCD (state.dividend.specialize phi u)
        (state.divisor.specialize phi u)).eval v = 0 := by
      rcases hassociated with ⟨unit, hunit⟩
      have heval := congrArg (fun p : K[X] ↦ p.eval v) hunit
      simpa [Polynomial.eval_mul, hterminalRoot] using heval.symm
    have hgcdRoot' : (@EuclideanDomain.gcd K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)).eval v = 0 := by
      simpa [fieldGCD] using hgcdRoot
    have hHRoot : (state.dividend.specialize phi u).eval v = 0 := by
      obtain ⟨q, hq⟩ := @EuclideanDomain.gcd_dvd_left K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)
      rw [hq, Polynomial.eval_mul, hgcdRoot', zero_mul]
    have hSRoot : (state.divisor.specialize phi u).eval v = 0 := by
      obtain ⟨q, hq⟩ := @EuclideanDomain.gcd_dvd_right K[X] inferInstance
        (Classical.decEq K[X]) (state.dividend.specialize phi u)
          (state.divisor.specialize phi u)
      rw [hq, Polynomial.eval_mul, hgcdRoot', zero_mul]
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · simpa [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hHRoot
    · constructor
      · intro _
        apply (splitStatePrimary_divisor_eval_eq_zero_iff r residual hr phi u v
          ⟨hbase, ?_⟩).mp hSRoot
        simpa [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
          TowerRepresentation.evalNested] using hHRoot
      · intro _
        rfl
  · obtain ⟨_, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitStatePrimary r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hraw := (restrictTower_point_iff r terminal.modulus
      (terminalQuotientPolynomial state terminal) phi u v hinvariants.2.1).mp hpoint
    have hbase := factorTower_root_sound state phi u terminal hterminal hraw.1
    have hassociated := factorTower_terminal_fieldGCD_associated
      state phi u terminal hterminal hraw.1
    have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
      (by simpa [state, splitStatePrimary] using hr.2.2.2.1)
      terminal hterminal phi u hraw.1
    have hfiltered := primary_terminal_complement r residual hr terminal hterminal
      phi u v hraw.1
    have hquotientRoot :
        ((makeTerminalQuotientBranch state terminal).quotient.specialize phi u).eval v = 0 := by
      simpa [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hraw.2
    have hunitSemantics := hfiltered.2.mp hquotientRoot
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · simpa [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
        TowerRepresentation.evalNested] using hunitSemantics.1
    · constructor
      · intro htag
        cases htag
      · intro hresidual
        exfalso
        apply hunitSemantics.2
        apply (splitStatePrimary_divisor_eval_eq_zero_iff r residual hr phi u v ⟨hbase, ?_⟩).mpr
          hresidual
        simpa [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
          TowerRepresentation.evalNested] using hunitSemantics.1

/-- Every parent point reaches a returned child, and it reaches a zero-tagged child exactly when
the tested element vanishes.  This is the exhaustive direction of `SplitZeroUnit`. -/
theorem splitZeroUnitPrimary_point_complete
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    {K : Type} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : r.Point phi u v) :
    ∃ output ∈ splitZeroUnitPrimary r residual hr,
      output.tower.Point phi u v ∧
        (output.tag = .zero ↔ TowerRepresentation.evalNested residual phi u v = 0) := by
  let state := splitStatePrimary r residual hr
  obtain ⟨terminal, hterminal, hterminalRoot⟩ :=
    factorTower_root_complete state phi u hpoint.1
  have hinvariants := factorTower_terminal_invariants state terminal hterminal
  have hbasePos : 0 < terminal.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hinvariants.1) phi hterminalRoot
      (fun x hx ↦ phi.injective (hx.trans phi.map_zero.symm))
  have hdividendMonic : state.dividend.toCPolynomial.monic := by
    simpa [state, splitStatePrimary] using hr.2.2.2.1
  have hHRoot : (state.dividend.specialize phi u).eval v = 0 := by
    simpa [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial,
      TowerRepresentation.Point, TowerRepresentation.evalNested] using hpoint.2
  have hassociated := factorTower_terminal_fieldGCD_associated
    state phi u terminal hterminal hterminalRoot
  by_cases hresidual : TowerRepresentation.evalNested residual phi u v = 0
  · have hSRoot : (state.divisor.specialize phi u).eval v = 0 := by
      exact (splitStatePrimary_divisor_eval_eq_zero_iff r residual hr phi u v hpoint).mpr hresidual
    have hgcdRoot : (fieldGCD (state.dividend.specialize phi u)
        (state.divisor.specialize phi u)).eval v = 0 := by
      let : DecidableEq K[X] := Classical.decEq K[X]
      rw [fieldGCD, EuclideanDomain.gcd_eq_gcd_ab]
      simp [Polynomial.eval_add, Polynomial.eval_mul, hHRoot, hSRoot]
    have hterminalFiberRoot :
        (terminal.gcdPolynomial.specialize phi u).eval v = 0 := by
      rcases hassociated.symm with ⟨unit, hunit⟩
      have heval := congrArg (fun p : K[X] ↦ p.eval v) hunit
      simpa [Polynomial.eval_mul, hgcdRoot] using heval.symm
    have hrawPoint : (restrictTower r terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).Point phi u v :=
      (restrictTower_point_iff r terminal.modulus terminal.gcdPolynomial.toCPolynomial
        phi u v hinvariants.2.1).mpr ⟨hterminalRoot, by
          exact hterminalFiberRoot⟩
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (restrictTower r terminal.modulus terminal.gcdPolynomial.toCPolynomial).fiber.monic := by
      exact TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    have hdimension : (restrictTower r terminal.modulus
        terminal.gcdPolynomial.toCPolynomial).dimension ≠ 0 :=
      TowerRepresentation.dimension_ne_zero_of_point _ hinvariants.1 hchildMonic
        phi u v hrawPoint
    let output : TaggedTower (F := F) :=
      ⟨.zero, restrictTower r terminal.modulus terminal.gcdPolynomial.toCPolynomial⟩
    have hmade : makeTagged? r .zero terminal.modulus
        terminal.gcdPolynomial.toCPolynomial = some output :=
      makeTagged?_eq_some_iff.mpr ⟨hdimension, rfl⟩
    refine ⟨output, mem_splitZeroUnitPrimary_iff.mpr
      ⟨terminal, hterminal, Or.inl hmade⟩, hrawPoint, ?_⟩
    simp [output, hresidual]
  · have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
      hdividendMonic terminal hterminal phi u hterminalRoot
    have hfiltered := primary_terminal_complement r residual hr terminal hterminal
      phi u v hterminalRoot
    have hSNonzero : (state.divisor.specialize phi u).eval v ≠ 0 := by
      exact fun hz => hresidual
        ((splitStatePrimary_divisor_eval_eq_zero_iff r residual hr phi u v hpoint).mp hz)
    have hquotientRoot := hfiltered.2.mpr ⟨hHRoot, hSNonzero⟩
    have hrawPoint : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).Point phi u v :=
      (restrictTower_point_iff r terminal.modulus
        (terminalQuotientPolynomial state terminal) phi u v hinvariants.2.1).mpr
          ⟨hterminalRoot, by
            simpa [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
              TowerRepresentation.evalNested] using hquotientRoot⟩
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      have hspecializedZero :
          (makeTerminalQuotientBranch state terminal).quotient.specialize phi u = 0 := by
        rw [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
          hzero, specializeFiberCPolynomial, CPolynomial.toPoly_zero, Polynomial.map_zero]
      exact hfiltered.1 hspecializedZero
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).fiber.monic := by
      exact TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    have hdimension : (restrictTower r terminal.modulus
        (terminalQuotientPolynomial state terminal)).dimension ≠ 0 :=
      TowerRepresentation.dimension_ne_zero_of_point _ hinvariants.1 hchildMonic
        phi u v hrawPoint
    let output : TaggedTower (F := F) :=
      ⟨.unit, restrictTower r terminal.modulus (terminalQuotientPolynomial state terminal)⟩
    have hmade : makeTagged? r .unit terminal.modulus
        (terminalQuotientPolynomial state terminal) = some output :=
      makeTagged?_eq_some_iff.mpr ⟨hdimension, rfl⟩
    refine ⟨output, mem_splitZeroUnitPrimary_iff.mpr
      ⟨terminal, hterminal, Or.inr hmade⟩, hrawPoint, ?_⟩
    simp [output, hresidual]

/-- Restricting canonical coefficients requires no squarefreeness assumption on the fiber. -/
theorem restrictTower_nonreducedWellFormed
    (source : TowerRepresentation (F := F)) (modulus : CPolynomial F)
    (fiber : CPolynomial (CPolynomial F)) {width : ℕ}
    (hmodulusMonic : modulus.monic) (hmodulusFree : Squarefree modulus.toPoly)
    (hdimension : (restrictTower source modulus fiber).dimension ≠ 0)
    (hfiberMonic : (TowerRepresentation.reduceBase modulus fiber).monic)
    (hwidth : source.coefficients.length = width) :
    (restrictTower source modulus fiber).NonreducedWellFormed width := by
  have hbaseNe : modulus.natDegree ≠ 0 := by
    intro hz
    apply hdimension
    simp [TowerRepresentation.dimension, restrictTower, hz]
  have hfiberNe : (TowerRepresentation.reduceBase modulus fiber).natDegree ≠ 0 := by
    intro hz
    apply hdimension
    simp [TowerRepresentation.dimension, restrictTower, hz]
  refine ⟨hmodulusMonic, hmodulusFree, Nat.pos_of_ne_zero hbaseNe,
    hfiberMonic, Nat.pos_of_ne_zero hfiberNe,
    TowerRepresentation.baseReduced_reduceBase hmodulusMonic fiber, ?_, ?_⟩
  · simp [restrictTower, hwidth]
  · intro coefficient hc
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hc
    exact TowerRepresentation.elementReduced_reduceElement hmodulusMonic hfiberMonic
      (Nat.pos_of_ne_zero hfiberNe) original

/-- Every executable child retains the canonical tower invariants and the exact message width. -/
theorem splitZeroUnitPrimary_nonreducedWellFormed
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnitPrimary r residual hr) :
    output.tower.NonreducedWellFormed width := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnitPrimary_iff.mp houtput
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitStatePrimary r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      by_contra hnot
      have hzeroDegree : terminal.modulus.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzeroDegree]
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitStatePrimary] using hr.2.2.2.1
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (TowerRepresentation.reduceBase terminal.modulus
          terminal.gcdPolynomial.toCPolynomial).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    apply restrictTower_nonreducedWellFormed r terminal.modulus
      terminal.gcdPolynomial.toCPolynomial hinvariants.2.1 hinvariants.2.2
      hdimension hchildMonic
    exact hr.2.2.2.2.2.2.1
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitStatePrimary r residual hr
    change (restrictTower r terminal.modulus
      (terminalQuotientPolynomial state terminal)).dimension ≠ 0 at hdimension
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      by_contra hnot
      have hzeroDegree : terminal.modulus.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzeroDegree]
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitStatePrimary] using hr.2.2.2.1
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      apply hdimension
      simp [TowerRepresentation.dimension, restrictTower, hzero,
        TowerRepresentation.reduceBase,
        FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero terminal.modulus hinvariants.2.1,
        CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (TowerRepresentation.reduceBase terminal.modulus
        (terminalQuotientPolynomial state terminal)).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    apply restrictTower_nonreducedWellFormed r terminal.modulus
      (terminalQuotientPolynomial state terminal) hinvariants.2.1 hinvariants.2.2
      hdimension hchildMonic
    exact hr.2.2.2.2.2.2.1

/-- Restricting the stored coefficient family to any returned split component preserves its
specialization at every point of that component. -/
theorem splitZeroUnitPrimary_specialize
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width) (output : TaggedTower (F := F))
    (houtput : output ∈ splitZeroUnitPrimary r residual hr)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : output.tower.Point phi u v) :
    r.specialize phi u v = output.tower.specialize phi u v := by
  obtain ⟨terminal, hterminal, hzero | hunit⟩ := mem_splitZeroUnitPrimary_iff.mp houtput
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hzero
    let state := splitStatePrimary r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      have hne : terminal.modulus.natDegree ≠ 0 := by
        intro hzero
        apply hdimension
        simp [TowerRepresentation.dimension, restrictTower, hzero]
      exact Nat.pos_of_ne_zero hne
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitStatePrimary] using hr.2.2.2.1
    have hrawMonic := factorTower_terminal_gcd_monic
      state hdividendMonic terminal hterminal
    have hchildMonic :
        (TowerRepresentation.reduceBase terminal.modulus
          terminal.gcdPolynomial.toCPolynomial).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hrawMonic
    exact restrictTower_specialize r terminal.modulus terminal.gcdPolynomial.toCPolynomial
      phi u v hinvariants.2.1 hchildMonic hpoint
  · obtain ⟨hdimension, rfl⟩ := makeTagged?_eq_some_iff.mp hunit
    let state := splitStatePrimary r residual hr
    have hinvariants := factorTower_terminal_invariants state terminal hterminal
    have hbasePos : 0 < terminal.modulus.natDegree := by
      have hne : terminal.modulus.natDegree ≠ 0 := by
        intro hzero
        apply hdimension
        simp [TowerRepresentation.dimension, restrictTower, hzero]
      exact Nat.pos_of_ne_zero hne
    have hdividendMonic : state.dividend.toCPolynomial.monic := by
      simpa [state, splitStatePrimary] using hr.2.2.2.1
    change (restrictTower r terminal.modulus
      (terminalQuotientPolynomial state terminal)).dimension ≠ 0 at hdimension
    have hquotientNe : terminalQuotientPolynomial state terminal ≠ 0 := by
      intro hzero
      have hfiberZero : (restrictTower r terminal.modulus
          (terminalQuotientPolynomial state terminal)).fiber = 0 := by
        rw [restrictTower, hzero, TowerRepresentation.reduceBase]
        exact FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero
          terminal.modulus hinvariants.2.1
      apply hdimension
      rw [TowerRepresentation.dimension, hfiberZero]
      simp [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
    have hquotientMonic := terminalQuotientPolynomial_monic_of_ne_zero
      state hdividendMonic terminal hterminal hbasePos hquotientNe
    have hchildMonic : (TowerRepresentation.reduceBase terminal.modulus
        (terminalQuotientPolynomial state terminal)).monic :=
      TowerRepresentation.monic_reduceBase hinvariants.2.1 hbasePos hquotientMonic
    exact restrictTower_specialize r terminal.modulus
      (terminalQuotientPolynomial state terminal) phi u v
      hinvariants.2.1 hchildMonic hpoint

/-- The original residual is a unit modulo every retained terminal fiber quotient. -/
theorem primary_terminal_unit_coprime
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (terminal : TerminalGCDBranch (F := F))
    (ht : terminal ∈ factorTower (splitStatePrimary r residual hr))
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : terminal.modulus.toPoly.eval₂ phi u = 0) :
    IsCoprime
      ((makeTerminalQuotientBranch (splitStatePrimary r residual hr) terminal).quotient.specialize
        phi u)
      (specializeFiberCPolynomial residual phi u) := by
  classical
  let state := splitStatePrimary r residual hr
  let H := state.dividend.specialize phi u
  let E := specializeFiberCPolynomial residual phi u
  let Q := (makeTerminalQuotientBranch state terminal).quotient.specialize phi u
  have hH : H = specializeFiberCPolynomial r.fiber phi u := by
    simp only [H, state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial]
  have hmonic : H.Monic := by
    rw [hH]
    exact ((CPolynomial.monic_toPoly_iff r.fiber).mp hr.2.2.2.1).map _
  have hfactor := terminal_gcd_mul_terminalQuotient_specialize state
    (by simpa [state, splitStatePrimary] using hr.2.2.2.1) terminal ht phi u hu
  have hassoc := factorTower_terminal_fieldGCD_associated state phi u terminal ht hu
  have hparent := factorTower_root_sound state phi u terminal ht hu
  have hcop : IsCoprime Q E := by
    apply PrimarySplit.quotient_isCoprime_residual_of_common_divisors hmonic.ne_zero
      (b := r.fiber.natDegree) (D := terminal.gcdPolynomial.specialize phi u)
      (S := state.divisor.specialize phi u)
    · rw [hH]
      change (r.fiber.toPoly.map _).natDegree ≤ r.fiber.natDegree
      rw [((CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1).natDegree_map,
        ← CPolynomial.natDegree_toPoly]
    · intro p hpH hpE
      rw [hH] at hpH
      rw [splitStatePrimary_divisor_specialize r residual hr phi u hparent,
        Polynomial.modByMonic_eq_sub_mul_div]
      exact dvd_sub hpE (dvd_mul_of_dvd_left hpH _)
    · intro p hpH hpS
      exact hassoc.dvd_iff_dvd_right.mpr
        (@EuclideanDomain.dvd_gcd K[X] inferInstance (Classical.decEq K[X]) _ _ _ hpH hpS)
    · exact hfactor
  exact hcop

/-- The terminal agreeing factor divides the unreduced residual power. -/
theorem primary_terminal_gcd_dvd_power
    (r : TowerRepresentation (F := F)) (residual : CPolynomial (CPolynomial F))
    {width : ℕ} (hr : r.NonreducedWellFormed width)
    (terminal : TerminalGCDBranch (F := F))
    (ht : terminal ∈ factorTower (splitStatePrimary r residual hr))
    {K : Type} [Field K] (phi : F →+* K) (u : K)
    (hu : terminal.modulus.toPoly.eval₂ phi u = 0) :
    terminal.gcdPolynomial.specialize phi u ∣
      (specializeFiberCPolynomial residual phi u) ^ r.fiber.natDegree := by
  let state := splitStatePrimary r residual hr
  have hassoc := factorTower_terminal_fieldGCD_associated state phi u terminal ht hu
  have hparent := factorTower_root_sound state phi u terminal ht hu
  have hdH := hassoc.dvd_iff_dvd_left.mpr
    (@EuclideanDomain.gcd_dvd_left K[X] inferInstance (Classical.decEq K[X]) _ _)
  have hdS := hassoc.dvd_iff_dvd_left.mpr
    (@EuclideanDomain.gcd_dvd_right K[X] inferInstance (Classical.decEq K[X]) _ _)
  rw [splitStatePrimary_divisor_specialize r residual hr phi u hparent] at hdS
  simp only [state, splitStatePrimary, FiberPolynomial.specialize_ofCPolynomial] at hdH
  rw [← Polynomial.modByMonic_add_div
    ((specializeFiberCPolynomial residual phi u) ^ r.fiber.natDegree)
    (specializeFiberCPolynomial r.fiber phi u)]
  exact dvd_add hdS (dvd_mul_of_dvd_left hdH _)

end ReedSolomon.ListDecoding.TowerAlgebra
