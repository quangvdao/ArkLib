/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ComponentDescent

/-! Execution tests for global component descent at meeting and ramified fibers. -/

namespace ComponentDescentTests

open CompPoly CPolynomial
open Polynomial.FunctionFieldAlgorithms.ComponentDescent

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def x : CBivariate (ZMod 5) := CPolynomial.C CPolynomial.X
private def y : CBivariate (ZMod 5) := CPolynomial.X

/-- Exercise a nonconstant coefficient during function-field Euclid, retain both global
components, and check their meeting fiber instead of deleting it. -/
def execute : IO Unit := do
  let left := y - x
  let right := y + x
  let meeting := left * right
  let residual := x * left
  let out := run meeting [residual]
  unless out.blocks.length == 2 do
    throw (IO.userError "component scan failed to retain both generic components")
  unless (out.blocks.map Block.modulus).prod == meeting do
    throw (IO.userError "component scan lost its exact global product")
  unless out.blocks.all fun b => b.modulus.monic do
    throw (IO.userError "component scan returned a nonmonic component")
  unless out.blocks.all fun b => CBivariate.evalEval 0 0 b.modulus == 0 do
    throw (IO.userError "the meeting fiber was removed from a returned component")
  unless (out.blocks.map Block.universal).any fun labels => 0 ∈ labels do
    throw (IO.userError "the actual residual did not label its global component")
  let ramified := y ^ 2 - x
  let ramifiedOut := run ramified [y]
  unless ramifiedOut.blocks.length == 1 do
    throw (IO.userError "a generically coprime residual split the ramified chart")
  unless (ramifiedOut.blocks.map Block.modulus).prod == ramified do
    throw (IO.userError "ramified chart product changed")
  unless ramifiedOut.blocks.all fun b => CBivariate.evalEval 0 0 b.modulus == 0 do
    throw (IO.userError "ramified special fiber was excluded")

#print axioms valueGlobal_monicGlobalGcd_associated
#print axioms monicGlobalGcd_mul_divByMonic
#print axioms divByMonic_generic_isCoprime
#print axioms run_product
#print axioms run_monic
#print axioms run_squarefree
#print axioms run_generic_squarefree
#print axioms run_labels_lt
#print axioms run_labels_nodup
#print axioms run_universal_dvd
#print axioms run_genericClassified
#print axioms run_allFiber_coverage

end ComponentDescentTests
