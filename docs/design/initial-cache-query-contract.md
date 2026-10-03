# Further SHOULD 3: errors from queries outside a fixed initial cache

This is the lowest-priority already-authorized extension after the empty-cache MUST theorem.
It does not replace or weaken that theorem. Work only within the remaining second-night budget.

## Model and definitions

Use the existing actual `OracleComp.randomOracleLoggedRun oa initialCache`: replies already
in the fixed supplied cache are reused, and each previously uncached hash key receives a fresh
uniform reply independent of prior private samples and other freshly sampled cells. Private
uniform samples remain fresh and unlogged. The theorem is conditional on this interpreter
model; it makes no claim about an external oracle whose unseen answers were correlated with
the initial cache through information not represented in the cache.

Define `newQueryKeys initialCache log` as distinct logged hash keys t with `initialCache t = none`.
Define `newQueryCharge initialCache error log` as their finite sum of nonnegative extended-real
errors, and `expectedNewQueryCharge oa initialCache error` as its expectation in the actual
joint cached run. Keep original outputs, ordered log, final cache, and failure values intact.
The initial cache may contain arbitrary valid replies; the hash input domain D need not be finite.

## Exact target

For D with decidable equality, dependent finite inhabited uniformly sampleable replies R(t),
finite interleaved computation oa, output event E, complete-table predicate bad(t,g), fixed
initialCache c, and error e(t), prove

    Pr[z <- randomOracleLoggedRun oa c : E(z.output)]
      <= expectedNewQueryCharge oa c e.

Require the explicit same-run trace implication: for every complete fallback table g and every
supported `fixedTableLoggedRun oa g c` result z, E(z.output) implies there is a key t in
`newQueryKeys c z.log` such that `bad(t, completeTable c g)`. The completed table respects every
initially cached answer.

Require the explicit own-cell bound for every initially uncached key t and every g:

    Pr[u <- uniform R(t) : bad(t, completeTable c (update g t u))] <= e(t).

Cached keys incur zero *new* charge. Consequently the trace hypothesis must identify an error
at a newly sampled key. This does not bound a bad output caused solely by a bad initial cached
answer: such applications need a separate initial-bad event or charge, left open here. Do not
hide that restriction in a definition or silently assert a general warm-cache security theorem.

Prove the arbitrary-domain theorem using a finite-support bridge and actual joint measures,
without sampling an infinite table. A finite-domain lemma may precede it. If helper visibility
or generalization is necessary in existing expected-query modules, preserve their old public
statements and do not duplicate the entire proof unnecessarily. Show that at empty initial
cache the new charge agrees with the existing expected distinct-query charge, and that the
new theorem covers the same empty-cache contract.

## Delivery

One coherent VCVio PR, ideally 500-1500 changed lines, with general difficult probability and
restriction theorems. No examples-as-deliverable, no admissions or trust shortcuts, no lint
exemptions. Target checks then canonical validation including environment lint, tests and axiom
regression. A fresh blind reader receives the frozen exported theorem before this contract.
Root owns final integration and publication. If a hidden independence issue prevents the exact
statement, report it and preserve the strongest checked result; do not weaken it without root review.
