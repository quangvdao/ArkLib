/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract

/-! # Acceptance checks for the computed Taylor chart contract -/

open ReedSolomon.HiddenDerivative.FastTaylor

#check eval₂_initialEquation
#check eval₂_initialSeparant
#check local_initial_root_of_component_dvd
#check local_highest_partial_unit_of_inverseAt
#check nonlinearNewton_exists_of_component
#check construct?_success_of_component
#check construct?_cleared_global
#check construct?_agreement_at_regular

#print axioms construct?_success_of_component
#print axioms construct?_cleared_global
#print axioms construct?_agreement_at_regular
