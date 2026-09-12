/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Assembly
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ComponentDescent

/-!
# Concrete component and norm preparation

This module joins the first two executable stages of the first-order producer.  Starting from a
Taylor chart and received word, it constructs the stored bivariate residuals, runs the actual
all-fiber component descent, and computes the determinant norm product for every returned
component.  The resulting blocks are output artifacts; callers do not supply them.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPolynomial
open ReedSolomon.HiddenDerivative.FastTaylor
open Polynomial.FunctionFieldAlgorithms

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- One actual descended component together with its computed nonuniversal norm rows and their
product. -/
structure ComputedBlock (E : Type) [Field E] [BEq E] [LawfulBEq E] where
  component : ComponentDescent.Block E
  norms : List (CPolynomial E)
  normProduct : CPolynomial E

/-- Compute the norm payload for a block returned by component descent. -/
def computeBlock (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) : ComputedBlock E :=
  { component := block
    norms := blockNorms block.modulus agreements block.universal
    normProduct := blockNormProduct block.modulus agreements block.universal }

@[simp] theorem computeBlock_component (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).component = block := rfl

@[simp] theorem computeBlock_norms (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).norms =
      blockNorms block.modulus agreements block.universal := rfl

@[simp] theorem computeBlock_normProduct (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).normProduct =
      (computeBlock agreements block).norms.prod := rfl

/-- The complete concrete output before multiplicity decomposition. -/
structure Prepared (E : Type) [Field E] [BEq E] [LawfulBEq E] (k : ℕ) where
  chartPolynomials : ChartPolynomials.Data E k
  agreements : List (CPolynomial (CPolynomial E))
  descent : ComponentDescent.Output E
  blocks : List (ComputedBlock E)

/-- Execute chart conversion, all-fiber component descent, and all determinant norms. -/
def prepare {k : ℕ} (chart : ChartData E 1 k) (received : List (E × E)) : Prepared E k :=
  let data := ChartPolynomials.ofChart chart
  let agreements := received.map fun row => ChartPolynomials.agreement chart row.1 row.2
  let descent := ComponentDescent.run data.equation agreements
  { chartPolynomials := data
    agreements := agreements
    descent := descent
    blocks := descent.blocks.map (computeBlock agreements) }

@[simp] theorem prepare_chartPolynomials {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).chartPolynomials = ChartPolynomials.ofChart chart := rfl

@[simp] theorem prepare_agreements {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).agreements =
      received.map fun row => ChartPolynomials.agreement chart row.1 row.2 := rfl

@[simp] theorem prepare_descent {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).descent =
      ComponentDescent.run (ChartPolynomials.ofChart chart).equation
        (received.map fun row => ChartPolynomials.agreement chart row.1 row.2) := rfl

@[simp] theorem prepare_blocks {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).blocks =
      (prepare chart received).descent.blocks.map
        (computeBlock (prepare chart received).agreements) := rfl

/-- Every prepared block comes from the actual component scan with its norms recomputed from the
actual residual list. -/
theorem mem_prepare_blocks_iff {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (out : ComputedBlock E) :
    out ∈ (prepare chart received).blocks ↔
      ∃ block ∈ (prepare chart received).descent.blocks,
        computeBlock (prepare chart received).agreements block = out := by
  simp only [prepare_blocks, List.mem_map]

/-- Monicity of the converted chart equation propagates through the actual descent to every
prepared block. -/
theorem preparedBlock_monic [DecidableEq E] {k b L : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (hnormal : chart.NormalForms b L)
    (out : ComputedBlock E) (hout : out ∈ (prepare chart received).blocks) :
    out.component.modulus.monic := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  exact ComponentDescent.run_monic
    (ChartPolynomials.ofChart chart).equation
    (prepare chart received).agreements
    (ChartPolynomials.equation_monic_of_normalForms chart hnormal)
    block (by simpa using hblock)

/-- Prepared universal labels are valid received-word positions. -/
theorem preparedBlock_labels_lt {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (out : ComputedBlock E)
    (hout : out ∈ (prepare chart received).blocks) (i : ℕ)
    (hi : i ∈ out.component.universal) : i < received.length := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  have h := ComponentDescent.run_labels_lt
    (ChartPolynomials.ofChart chart).equation
    (prepare chart received).agreements block (by simpa using hblock) i hi
  simpa using h

end ReedSolomon.ListDecoding.FirstOrderNormProducer
