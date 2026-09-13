# Public zeroth decoder and positive-order backend collection

This collection preserves the following exact published checkpoints over core
`b626a599817381cfb84155f8b74d9cf6ff0c18a4`.

| Source | Exact checkpoint | Established scope |
| --- | --- | --- |
| Personal 1 | `b26284081fa4d45fd400c0ff00081fc468988e2c` | Actual full decomposition, component norm/descent, candidate coverage under chart premises, emitted modulus degree bounds |
| Personal 4 zeroth | `ebd6cefb822870955b192759618dab8c4a745dc7` | Public supplied-field `run?` and `run?_exists_exact` under `Valid` |
| Personal 4 positive | `6fe32a979590e6e31863192fff1b66b4bcfe575b` | Fixed-order stage/chart assembly and conditional top-active coverage |
| Personal 3 preparation | `d8c8b5478625a54a0eb6753d47a99d702a8727d4` | Stored inverse-Frobenius preparation reused by the certificate callback |
| Personal 3 extensions | `b9d6b3b1d2795dc4933042ec4c215e4aac33399c` | Executed general extension search, proved success, quotient field and prefix |
| Personal 3 Rojas | `de0aba60a3a8268199cf84b28e8ea182b0354dac` | Executable Macaulay matrices, checked quotient and degree/refinement infrastructure |
| Personal 3 selection | `0ec81eae456f731cc5a7bc1d7b4c550bee0b7a63` | Executable fixed-gap independent selection conditional on `ExactEnergyEstimate` |

The zeroth-order input accepts a supplied polynomial-basis field. The public theorem contains
parameter, interpolation-dimension and cardinality conditions, not a normalization result,
center, inverse callback or final coverage oracle. Compiled public base, odd-quadratic and
binary-quadratic paths return nonempty outputs. Ordinary recovery retains no `k ≤ p` guard.
See [the dedicated public contract](public-zeroth-checkpoint.md).

The first-order backend computes component descent, norms, labelled squarefree decomposition,
retained support and tower materialization. Its completeness theorem still requires the chart's
normal forms, generic squarefreeness, universal-position count bound and equation degree below the
characteristic. Its literal denominator-power equality is stronger than the constructor's actual
normal-form contract: the reduced denominator agrees with that power on the chart, not generally
as a polynomial. Personal 1 must repair this consumer premise to quotient/evaluation equality or
regular-point nonvanishing. The returned conditional theorem is sound but not yet directly usable
with general constructor outputs. It does not itself prove global chart coverage.

The positive chart scan currently drops stages whose active jet is below the fixed top jet.
`ComponentProducer.CoversTopActiveSolutions` accurately names that boundary. A concrete component
producer, varying-order adapter and semantic separant-chain/fuel bridge remain necessary.
See [the fixed-order contract](positive-coverage-checkpoint.md).

## Remaining work and ownership

Personal 1 resumes on concrete regular-component construction and the chart contracts required
by its first-order backend. Personal 4 owns varying-order coverage, the semantic separant-chain
bridge, final candidate recovery and public positive-order dispatch. Their next exact handoffs
freeze separate files and consumer signatures before parallel implementation.

Personal 3 is already continuing G08. Its ongoing worktree and report are not modified by this
collection. The exact published matrix checkpoint above is the integration dependency until a
new reviewed producer is returned. Remaining G08 obligations are multivariate-resultant semantics,
Macaulay quotient identification and Rojas deformation/isolated-root coverage.

G09 has a second integration gap in addition to its analytic premise: the final selection theorem
retains cardinality and independence but drops `selected ⊆ agreeing`. The agreeing-set membership
must be carried through classes, powered edges, rank growth and odd completion before a downstream
root producer can infer that the selected equations vanish. Do not describe the published G09
result as complete wanted-point capture conditional only on energy.

Personal 1 owns the next agreeing-membership repair and a separate new-module proof lane for the
actual eight-map Gabber–Galil energy estimate. This transfer leaves Personal 3's active G08 work
untouched. Executable powering and mixing consequences do not prove the analytic estimate; the
uniform composite-modulus case remains part of that obligation.

All main agents and subagents use GPT-5.6 Sol High. Assign sustained programs with verified
intermediate publications; do not stop after a conditional wrapper. Preserve the paper pin
`b1be8b89069542faacac40a7e92068857b43e97a` and existing positive-order characteristic scope.

## Collection checks

The coordinator regenerates the production umbrella, registers returned runtime entrypoints,
checks immutable source identity and reviews the cross-team contracts. Publication requires the
full combined cache-disabled `validate.sh --axioms` gate with unchanged pins and taint baseline.
The launch-kit collection report records the exact published commit, tested tree and retained log.
Worker validation alone does not establish combined acceptance.
