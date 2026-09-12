/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Source specification for the general Rojas producer

The producer in this directory follows J. Maurice Rojas, *Solving Degenerate
Sparse Polynomial Systems Faster*, Journal of Symbolic Computation 28 (1999),
155--186, arXiv:math/9809071v2.

The primary geometric statement is Main Theorem 4 together with Definitions
1--3.  For supports `E = (E₁, ..., Eₙ)`, auxiliary support
`A = Δ ∩ ℤⁿ = {0,e₁,...,eₙ}`, and a system `FStar` having finitely many roots in
the associated toric variety, it defines

`H(u;s) = Res_(E,A)(F - s FStar, u₀ + Σᵢ uᵢ xᵢ)`.

The coefficient of the lowest power of `s` occurring in `H` is `Pert_A`.
Main Theorem 4 says that `Pert_A` is nonzero and homogeneous of degree the
mixed volume, contains the linear factor belonging to every isolated root,
and splits into geometric linear factors.  Main Theorem 1, Steps 0--5 in
Section 5.1, specializes `Pert_A`, squarefree-reduces the shifted eliminants,
and uses their first subresultants to recover the coordinate polynomials.
Its final clause obtains affine, rather than only torus, coverage by replacing
every `Eᵢ` by `{0} ∪ Eᵢ`.  This clause is what retains roots on coordinate
hyperplanes even when another component is positive-dimensional.

For dense total-degree bounds `dᵢ`, Section 3.4 fixes the deterministic
perturbing system

`FStar = (x₁^d₁, ..., xₙ^dₙ)`.

It has one projective root at the origin, with multiplicity `∏ᵢ dᵢ`, and no
search or generic coefficient is needed.  The same section identifies the
resultant construction with Macaulay's dense resultant matrix.  In the sparse
setting, Main Theorem 3 instead constructs `FStar` from an irreducible fill
`Dᵢ ⊆ Eᵢ`, characterized by `MV(D) = MV(E)` and minimality under deletion.
The executable checkpoint uses the dense specialization required by the
decoder systems while retaining the actual sparse supports as computed data.
Its stored determinant is presently only the Macaulay resultant multiple;
removal of the classical extraneous factor and the geometric factor theorem
remain explicit proof obligations.

The dense quotient convention is fixed more precisely by J. F. Canny,
*Generalized Characteristic Polynomials*, UCB/CSD-88-440 (1988), Section 2,
equations (1)--(5).  Canny uses the same critical degree and assigns a row to
the smallest index whose paired power divides its monomial.  The extraneous
factor is the principal minor on row and column monomials that are not reduced,
meaning that at least two paired powers divide them.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.Source

/-- Stable identifier for the primary theorem implemented by the producer. -/
def primaryTheorem : String :=
  "Rojas99, Main Theorems 1 and 4; dense matrix construction in Section 3.4"

end ArkLib.Rojas.Producer.Source
