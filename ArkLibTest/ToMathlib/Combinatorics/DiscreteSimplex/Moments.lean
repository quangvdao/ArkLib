/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Moments
import Mathlib.Tactic.FinCases

/-! # Boundary regression tests -/

noncomputable section

namespace DiscreteSimplex

open scoped BigOperators

/-- With budget three, marking the second unit in `(2,1)` leaves `(0,1,1)` at budget two.
This distinguishes the residual and appended coordinates and the removed marked unit. -/
example :
    (simplexCoordinateSplitEquiv (S := 2) (0 : Fin 2)
      ⟨⟨![2, 1], by norm_num [Fin.sum_univ_succ]⟩, ⟨1, by decide⟩⟩).1 = ![0, 1, 1] := by
  funext j
  fin_cases j <;> rfl

end DiscreteSimplex
