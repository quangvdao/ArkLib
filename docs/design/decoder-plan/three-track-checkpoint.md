# Three-track producer and Taylor collection

This collection combines three independently published checkpoints over accepted core
`700a44b7473c41d0c98e311b37bad474d7ea7a0c`:

| Owner | Exact source checkpoint | Completed contract |
| --- | --- | --- |
| Personal 1 | `6d4c45aff0fda14bc9e992538ec8ded6d57cc531` | Generic actual-run normalization correctness: no arithmetic failure, zero/constant semantics, original graph equivalence, divisibility, X/Y bounds and obstruction/fiber facts |
| Personal 3 | `fe907e828739188bbc01fd89cb410f51dd7f0f63` | Supplied polynomial-basis inverse Frobenius, odd/binary quadratic centers, prefixes and center-dispatch success conditions |
| Personal 4 | `a158e13a6558109eb5cf43826bd96efb7259527f` | One-chart Taylor construction success and global regular-locus agreement; conditional supplied-field zeroth-order adapter |

Personal 4 already includes the earlier Personal 3 fields, direct Jacobian and univariate Rojas
slices. Their shared files are included once. The three returned histories are preserved by
collection merges; no source theorem is weakened to combine them.

## What the new combination establishes

The generic normalizer's conditional inverse law can now be instantiated by the concrete
supplied-field gcd-based inverse. A compiled consumer test normalizes a fourth power over F4
with a coefficient outside its prime subfield; identity inversion cannot pass this case.
All newly supplied runtime suites are registered centrally, and the umbrella is regenerated.

The one-chart constructor computes its projection, sample and quotient inverse, lifts the
actual nonlinear equation, reconstructs global numerators and proves its regular-locus agreement
contract. This is not all-chart coverage. The supplied center dispatcher constructs a prefix
when the requested count is at most q squared; the application must derive that capacity bound
from its interpolation/obstruction parameters.

## Subsequent zeroth-order composition

Personal 4 has now implemented the public supplied-field decoder described in
[the public zeroth-order checkpoint](public-zeroth-checkpoint.md). It constructs the interpolant,
normalizes it, derives center capacity, dispatches through the supplied-field center producer,
and performs ordinary recovery. This supersedes the first item in the historical list below.

## Historical open list at collection time

- The dedicated arbitrary-field decoder had to execute normalization and center construction,
  map into either quadratic branch, discharge conversion/coverage hypotheses and prove final
  q >= n success/exactness. A nonempty full binary-extension recovery test remains required.
- Positive-order construction still needs all-chart coverage, complete first-order norm
  candidates, general toric isolated-root construction, both higher-order selections and final
  public composition. Existing valid local-chart or univariate hypotheses are not global coverage.
- The original q-only extension search is separate from the now-complete supplied-field input
  path. Supplied-field correctness does not close general extension construction.

Paper zeroth-order specification: `b1be8b89069542faacac40a7e92068857b43e97a`.
Positive-order scope retains the previously adopted prime-field algorithm and its assumptions.
No bit-cost model is claimed; the actual prescribed algorithms and their guards still matter.

## Acceptance and coordination

The coordinator checks source identity, exact interfaces, runtime registrations and independent
reviews, then runs the full combined `validate.sh --axioms` before publication. Worker gates do
not replace that final check. Exact integrated SHA, tested tree and validation evidence are
recorded in the launch-kit collection handoff. Dependency pins and the axiom baseline are unchanged.

The task board assigns the next substantial deliverables. Main agents and all subagents use
GPT-5.6 Sol with high reasoning. Publish useful verified intermediate checkpoints, while keeping
larger remaining proof obligations explicit and continuing toward the assigned milestone.
