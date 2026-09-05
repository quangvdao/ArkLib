# Strengthening lane: verified endpoint and remaining MCA frontier

This is a handoff record, not an additional theorem. Only declarations in the
certified commits have passed the repository gates. Scratch under
`.lake/strengthening-wip` is preserved separately and is not a proof dependency.

## Completed list endpoint

Commit `0646f443` proves the manuscript list bound for arbitrary fields with
characteristic zero or characteristic at least the block length. For
`0 < delta < 1/4`, `d = ceil(exp(6.76/delta))`,
`m = ceil(100*d^2*H_(d-1))`, `n >= 8m`, and
`A = k + ceil(delta*n) <= n`, the complete degree-`<k` close-polynomial list is
finite and has cardinality at most `4*m^2*(4*m/delta)^d*n^d`.
There is no field-cardinality factor.

Public declarations in namespace `ReedSolomon.AllRateListDecoding`:

- `prescribed_geometric_finite_list_bound` bounds any finite agreeing family.
- `prescribed_geometric_close_list_bound` proves finiteness and bounds actual
  `Set.ncard` of the entire close-polynomial set.
- `prescribed_geometric_lambda_bound` bounds canonical `Code.Lambda` at radius
  `1-k/n-delta`, with `Nat.ceil` only for the natural/ENat output bound.

The proof uses actual principal-cut purity and affine Bezout, retained minimal
prime covers, finite high-cut families, agreement double counting, explicit
rational Taylor numerators, and an explicit algebraic-closure embedding.
`TaylorAllSolutions` handles positive characteristic; `TaylorCharZeroSolutions`
uses a separate direct induction. Neither assumes a root-count or geometric
law structure. The central decoder-output bridge was independently audited:
it attaches this bound to the same existing physical output and work witness.

## Completed correlated-agreement components

The half-gap branch already proves the full common-agreement set statement and
actual line/affine MCA bounds with exceptional budget `2*n`, in every
characteristic. The symbolic band certificate is actual and primitive, stays
nonzero at every challenge over every extension, has total jet degree at most
`2*m-1`, and coefficient challenge degree below `338*(2*m-1)`.

The intermediate selected-column certificate uses `b1 <= 16` and
`b0+b1 <= 119`. Its actual rank bound is `28152*n`, its selected dimension is at
least `30464*n + 1156*k`, and its primitive coefficient height is at most 1449.
Its stronger interface exposes support total jet degree at most 119 and the
same cap at every extension-field challenge specialization. The selected
construction removes the earlier upper-window premise. Its prescribed wrapper
currently uses `k >= 3`, `n > 0`, and `4*k+n <= 4*A`.

## Still unproved: manuscript small/intermediate MCA transfer

The list bound does not imply the requested MCA endpoint. In particular, the
existing general list-to-MCA conversion changes the radius and squares the list
size, so it does not discharge this manuscript target.

The remaining argument is `core/correlated-agreement.tex`, the symbolic-transfer
and joint-envelope lemmas. Required concrete constructions are:

1. Retain the challenge variable in the rational Taylor chart and prove its
   second degree bound. For a stage of jet degree `v` and challenge height
   `zeta`, the later numerator has challenge degree at most `(2h-1)*zeta`.
   A common representation has challenge degree at most `1+2K*zeta` and jet
   degree at most `b = 1+2K*(nu-1)`.
2. Construct actual rational image closures and prove the mixed-degree image
   bound. Sum actual separant stages to obtain a joint envelope of dimension at
   most `d+1` and degree at most
   `Delta = nu*b^d*(zeta*b + (d+1)*nu*(1+2K*zeta))`.
   A nonzero terminal coefficient bounds the exceptional challenge set by zeta.
3. Prove the generic fiber statement for this actual joint closure: dimension
   at most d and degree at most `nu^2*b^d`. It is a generic-fiber claim, not a
   claim about every specialization. The existing point-list theorem does not
   establish it, nor does it justify commuting closure with specialization.
4. Extend agreement incidence to exclude the actual common-agreement graph
   lines. The fixed-k Vandermonde/graph-line recognition and exact accidental
   agreement removal are already proved in `GraphLineAgreement`. Count the
   retained lines using the generic fiber, and off-line points using the joint
   envelope. Ordinary pointwise k-cut uniqueness is insufficient here: k cuts
   in the joint challenge/message space leave a graph line, not a point.
5. Assemble the exact exceptional set and full equality of agreement sets, then
   the actual mutual line/affine predicates. For `k <= L <= A`, the target is
   `zeta + lambda1^(d+1)*Delta + n*lambda2^d*nu^2*b^d`, where
   `lambda1=(n-L+1)/(A-L+1)` and `lambda2=(n-k+1)/(L-k+1)`.
   Substituting `L=k+floor((A-k)/2)` must yield the stated small/intermediate
   constants, including the intermediate low-k cases.

Do not replace these constructions with assumed degree laws, a generic fiber
premise, or a weaker radius/error budget and call the MCA goal complete.

## Validation and handoff discipline

The eleventh checkpoint passed full default validation, 858 umbrella imports,
23,020 declarations across 859 modules in the axiom sweep, 312 preexisting
sorry-tainted declarations, zero nonstandard axioms, and no new taint. The source
trust inventory is unchanged. No baseline was updated and no resource override
was introduced. Subsequent checkpoint receipts belong in
`ALL_RATE_RS_STRENGTHENINGS_PROGRESS.md`.

The private lane must not publish or edit the central worktree. Central remains
the sole publication owner. New implementation stops at 09:21:04 UTC on
2026-09-05; handoff and preservation are due by 09:36 UTC, final stop by 09:51:04.
