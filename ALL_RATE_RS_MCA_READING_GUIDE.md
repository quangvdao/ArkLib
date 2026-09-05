# Reading the formal mutual correlated agreement theorem

This guide is for readers of the paper who do not know Lean. It explains the public
statements, not the internal geometric proof. The relevant paper passage is
**Mutual correlated agreement up to capacity**, followed by **Mutual agreement for
affine families** in Dao, Kominers, Thaler, and Zheng, *Reed–Solomon List Decoding
and Mutual Correlated Agreement up to Capacity* (draft).

## Start with the mathematical statement

Fix a positive capacity gap δ. There are constants N, d, and C > 0, depending only
on δ. Put E(n) = C n^(d+1). For every sufficiently long Reed–Solomon code in
characteristic zero or characteristic at least n, and every received line f + zg,
there is one set of at most E(n) exceptional challenges.

Outside that set, every degree-<k polynomial P agreeing with f + zg on at least
k + δn positions has the form P = F₀ + zG₀. Both constituent polynomials have
degree < k. The full agreement set of P is exactly the set where F₀ agrees with f
and G₀ agrees with g simultaneously.

Read the actual declarations here:

- [Line theorem: `exists_allRate_correlatedAgreement`](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/AllRateCorrelatedAgreement.lean).
- [Affine witnesses and probability corollary](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/AllRateAffineAgreement.lean).

## Paper-to-Lean correspondence

| Paper | Lean | Meaning |
|---|---|---|
| For every positive gap δ | `(δ : ℝ) (hδ : 0 < δ)` | δ is real and positive. |
| Constants depending only on δ | `∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧ …` | These constants are chosen before every code parameter. |
| E(n) = n raised to a gap-dependent constant | `let E := fun n : ℕ ↦ C * (n : ℝ) ^ (d + 1)` | An explicit polynomial upper bound, not informal asymptotic notation. |
| Length and message dimension | `N ≤ n`, `0 < k`, `k ≤ n` | All rates are allowed. |
| Agreement threshold | `(k : ℝ) + δ * n ≤ A` | A is an integer; this is equivalent to A ≥ k + ceil(δn). |
| Distinct evaluation points | `α : Fin n ↪ F` | `Fin n` is the set of n positions; the arrow means an injective map. |
| Polynomials over F | `P : F[X]` | An ordinary univariate polynomial. |
| Degree less than k | `P.degree < k` | Includes the zero polynomial. Lean assigns it degree minus infinity. |
| Exceptional set | `exceptional : Finset F` | A finite set of challenges, even if F is infinite. |
| Cardinality bound | `(exceptional.card : ℝ) ≤ E n` | The number of exceptional challenges, compared as a real number. |
| Every nonexceptional challenge | `∀ z ∉ exceptional` | For every z, assuming z is not exceptional. |
| Polynomial decomposition | `P = F₀ + z • G₀` | `•` multiplies every coefficient of G₀ by z. |
| Equality of full agreement sets | `S z P = T F₀ G₀` | Equality, not containment or equality of cardinalities. |

`ℕ` means natural numbers; `ℝ` means real numbers. `∃` means “there exist,” `∀`
means “for every,” `∧` means “and,” and `→` means “assuming the preceding condition.”
A `let` names an expression; it does not add a hypothesis. Expressions such as
`(n : ℝ)` view the same integer n as a real number.

## Inspect the two agreement sets

The local names S and T only abbreviate existing definitions. Those definitions
are [visible in the source](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/HalfGapCorrelatedAgreement.lean):

```lean
Finset.univ.filter fun i ↦ P.eval (α i) = received i
```

This says: take every position, then retain exactly the positions satisfying the
displayed equality. For S, `received i` is `f i + z * g i`. The common set uses

```lean
Finset.univ.filter fun i ↦ F₀.eval (α i) = f i ∧ G₀.eval (α i) = g i
```

There is no hidden selection of a convenient subset in either definition.

## Read the quantifiers in order

1. Choose δ.
2. Obtain N, d, and C, before knowing the rate, field, or received words.
3. Supply n, k, A, the field, evaluation points, and the received words f and g.
4. Obtain one exceptional set.
5. Choose any z outside it and any qualifying P.
6. Obtain the constituent polynomials F₀ and G₀.

Moving step 4 after step 5 would weaken the theorem substantially. The Lean
statement does not do that. The constituent witnesses may depend on z and P;
the exceptional set cannot.

## Affine families and probabilities

The affine witness statement presents the received family as a constant word a
plus a sum of scalar multiples of direction words u. The parameter t has s
coordinates, where s ≥ 1. The reconstructed polynomial is F₀ plus the corresponding sum of
t_j G_j. Its full agreement set is exactly where all constituent equations hold.

For a finite field of size q, the line bad-challenge probability is at most E(n)/q.
The affine bad-parameter probability is at most E(n)/(q−1), independently of s.
The exceptional affine set has at most E(n)q^s/(q−1) elements: division by the
sample-space size q^s gives that probability bound.

The separate probability corollary uses ArkLib's `mcaError`: the worst-case
probability, over received families, that some sufficiently large position set
admits the combined word but not all constituent words as restricted codewords.
Despite its historical name, the underlying `IsMCA` predicate describes this
**bad event**. `ENNReal.ofReal` embeds the nonnegative real bound into the
extended nonnegative reals used by the probability library.

For consumers requiring one shared choice of N, d, C across the witness and probability
bounds, `exists_allRate_affineAgreement_and_mcaError` exposes them together. The two
shorter statements are consequences of that joint theorem.

## Differences from the paper, explicitly

- The qualitative Lean theorem allows every δ > 0, not only δ < 1. Impossible
  thresholds have no qualifying P, so they make the conclusion vacuous.
- It does not require A ≤ n for the same reason. In the intended nonvacuous
  regime it covers exactly the paper's integer agreement thresholds.
- Its characteristic assumption is zero or **at least n**, including the prime
  field q = n. This is slightly broader than the paper's main displayed >n guard.
- `Field F` supplies field laws. `DecidableEq F` supplies equality decisions used
  to represent finite agreement sets; classical logic can supply this instance.
- The line theorem need not assume F finite. Probability statements do.
- The d in the qualitative statement is an exponent parameter. The prescribed
  derivative-order construction is exposed separately in `PrescribedLineMCA`.
- This statement does not claim the paper's sharp prefactor or low-order refinements.

## What the formal check establishes

Lean checks that the proof proves this exact statement from its definitions.
The endpoint axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`, Lean's standard classical foundations; no `sorry` is used in their
proof dependencies. Other parts of ArkLib still contain unrelated admissions.

This does not replace the human task of checking that the statement represents
the intended mathematics. The correspondence table, explicit agreement definitions,
and quantifier tour make that task inspectable. Nor is this a running-time theorem.

From a configured checkout, reproduce the repository checks with
`./scripts/validate.sh --axioms`. Consult
[the strengthening tracker](ALL_RATE_RS_STRENGTHENINGS.md) for the exact validated
checkpoint and remaining quantitative work.
