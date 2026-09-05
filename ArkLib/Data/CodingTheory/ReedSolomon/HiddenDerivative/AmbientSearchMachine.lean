/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

/-!
# Descending integer ambient search

The runtime receives integer parameters and materialized received points. It counts those
points, then tries every ambient degree from n-1 down to max(k-1,d+1), stopping at the first
actual interpolation success. Each failed attempt is charged in full. The constant control
charge covers the natural-number tests, arithmetic, branch and output allocation; underlying
interpolation costs are retained verbatim. No real parameter or witness enters execution.
-/

namespace ReedSolomon.HiddenDerivative.AmbientSearchMachine

/-- A successful search records its actual ambient degree and sparse interpolant. -/
structure Output (F : Type*) where
  degree : ℕ
  interpolant : NonzeroInterpolationMachine.Output F
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Visit at most `count` descending candidates, including all work on failed attempts. -/
def search (d m A : ℕ) (received : List (F × F)) : ℕ → ℕ → Option (Output F) × ℕ
  | 0, _ => (none, 32)
  | count + 1, D =>
      let attempt := NonzeroInterpolationMachine.run D d m A received
      match attempt.1 with
      | some out => (some ⟨D, out⟩, 32 + attempt.2)
      | none =>
          let rest := search d m A received count (D - 1)
          (rest.1, 32 + attempt.2 + rest.2)

/-- Count the input and search the closed interval max(k-1,d+1),...,n-1 in reverse order. -/
def run (k d m A : ℕ) (received : List (F × F)) : Option (Output F) × ℕ :=
  let counted := ReceivedInterpolationMatrixMachine.countCells received
  let lower := max (k - 1) (d + 1)
  let result := search d m A received (counted.1 - lower) (counted.1 - 1)
  (result.1, 32 + counted.2 + result.2)

end ReedSolomon.HiddenDerivative.AmbientSearchMachine
