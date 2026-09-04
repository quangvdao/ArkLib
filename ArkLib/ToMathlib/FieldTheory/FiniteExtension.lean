/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.Finite.Extension

/-!
# Sufficiently large extensions of finite fields

Mathlib provides `FiniteField.Extension k p n`, a chosen degree-`n` extension of a finite field
`k` of characteristic `p`. This file chooses an explicit positive degree whose extension has more
than a prescribed number of elements. The construction changes cardinality but preserves
characteristic; this distinction matters in characteristic-sensitive root-counting arguments.
-/

namespace FiniteField

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A positive extension degree for which the resulting finite field has cardinality strictly
larger than `bound`. -/
def extensionDegreeAbove (bound : ℕ) : ℕ :=
  (Nat.log (Nat.card k) bound).succ

instance (bound : ℕ) : NeZero (extensionDegreeAbove k bound) :=
  ⟨Nat.succ_ne_zero _⟩

/-- The chosen finite extension of `k` with more than `bound` elements. -/
abbrev ExtensionAbove (bound : ℕ) : Type :=
  Extension k p (extensionDegreeAbove k bound)

omit [Field k] [Finite k] in
theorem extensionDegreeAbove_pos (bound : ℕ) : 0 < extensionDegreeAbove k bound := by
  simp [extensionDegreeAbove]

/-- Exact cardinality of the chosen sufficiently large extension. -/
theorem natCard_extensionAbove (bound : ℕ) :
    Nat.card (ExtensionAbove k p bound) = Nat.card k ^ extensionDegreeAbove k bound := by
  exact natCard_extension k p (extensionDegreeAbove k bound)

/-- The chosen extension has strictly more elements than the requested bound. -/
theorem lt_natCard_extensionAbove (bound : ℕ) :
    bound < Nat.card (ExtensionAbove k p bound) := by
  rw [natCard_extensionAbove]
  exact Nat.lt_pow_succ_log_self Finite.one_lt_card bound

/-- Exact degree of the chosen sufficiently large extension. -/
theorem finrank_extensionAbove (bound : ℕ) :
    Module.finrank k (ExtensionAbove k p bound) = extensionDegreeAbove k bound := by
  exact finrank_extension k p (extensionDegreeAbove k bound)

/-- Passing to the chosen extension preserves the base field's characteristic. -/
theorem charP_extensionAbove (bound : ℕ) : CharP (ExtensionAbove k p bound) p := by
  exact charP_of_injective_algebraMap (algebraMap k (ExtensionAbove k p bound)).injective p

/-! ### Boundary canaries -/

/-- The strict size guarantee remains meaningful when the requested bound is zero. -/
example : 0 < Nat.card (ExtensionAbove (ZMod 2) 2 0) := by
  exact lt_natCard_extensionAbove (ZMod 2) 2 0

/-- Enlarging a field never changes characteristic: a large characteristic-two extension still
has characteristic two. -/
example : CharP (ExtensionAbove (ZMod 2) 2 8) 2 := by
  exact charP_extensionAbove (ZMod 2) 2 8

end

end FiniteField
