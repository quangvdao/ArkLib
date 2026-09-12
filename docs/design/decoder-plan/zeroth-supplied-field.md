# Supplied-field zeroth-order decoder and positive-order Taylor

This plan records the user-adopted split for implementers and integration reviewers.
The accepted core is `700a44b7473c41d0c98e311b37bad474d7ea7a0c`; it was merged into the
preserved Personal 4 continuation rather than used as a reset.
The revised zeroth-order specification is paper commit
`b1be8b89069542faacac40a7e92068857b43e97a`, particularly
`appendices/decoder-separable.tex` and `core/decoding.tex`.
The positive-order work preserves its original Taylor specification and checkpoints.

## Dedicated entrypoint

`PublicDecoder.run?` is the implemented application entrypoint. Its input supplies the existing
polynomial-basis field presentation,
primality and irreducibility promises, a positive modulus degree, distinct evaluation
points, `q >= n`, and valid decoding parameters. It does not construct `F_q` from `q`.
Reuse existing executable field dictionaries and embeddings at accepted peer commits.
Do not invent a second global field packet while those interfaces are unsettled.

For `k = 1`, count received-value frequencies. For larger supported `k`, execute the
interpolant construction, Personal 1's saturated radical/separable normalization and
obstruction, Personal 3's sufficient center prefix and quadratic extension when needed,
one ordinary quotient Newton lift, then arbitrary-base-field agreement recovery.
The public theorem must prove exact membership for that executed list, including
termination, producer success and completeness. A supplied good center, desired
factorization, or final coverage proof cannot replace the corresponding producer.

The ordinary Newton path has no `k <= p` restriction. Large binary extension inputs,
including `n > p` and `k > p`, reach this path. Coordinate prefixes range over the
supplied field, not just its prime subfield. Binary quadratic centers use trace-one
Artin–Schreier polynomials; odd centers use nonsquares in the actual supplied field.
The separate `d < p` fiber preprocessing and prime-only large norm routines keep
their original restrictions. No bit-complexity formalization is part of this task.

## Producer ownership and adoption

| Owner | Required checked producer | Adoption state |
| --- | --- | --- |
| Personal 1 | Saturated Radical/SeparablePart; global graph retention, degree bounds; obstruction | Full generic capstone `6d4c45aff0fda14bc9e992538ec8ded6d57cc531` collected; instantiate its explicit coefficient inverse law |
| Personal 3 | Supplied-field inverse Frobenius; coordinate prefixes; both quadratic branches | Complete supplied-field producers `fe907e828739188bbc01fd89cb410f51dd7f0f63` collected, including inverse Frobenius and binary/odd centers |
| Personal 4 | Ordinary Newton/recovery adapters and exact executed composition | `PublicDecoder.run?` composes actual interpolation, certified normalization, all supplied-center branches and ordinary recovery; `run?_exists_exact` proves unconditional success and exactness under `Valid` |

Adopt only reviewed immutable commits. Record each SHA with a compiled producer and
consumer client at the same integration head. Current worker source and historical
published soundness slices do not imply completion of the revised producers.

## Completed application composition

`PublicDecoder.run?` builds the actual interpolant and certified normalization result. Its branches
handle impossible zero/failure outcomes, constant regular parts, supplied-field center dispatch,
ordinary lifting and exact recovery. `normalized_capacity` derives the required obstruction bound
from the interpolation witness and normalization degree bounds. `run?_exists_exact` proves that
every `Valid` input returns a list satisfying `ExactOutput`; callers supply no normalization,
center, inverse, candidate or coverage callback. The `k = 1` frequency branch remains first, and
the large ordinary branch has no differential `k <= p` guard.

The compiled runtime covers all preliminary branches and nonempty F4 recovery with `n > p` and
`k > p`. F8 and F9 near-capacity calls also recover nonempty outputs. These end-to-end public
fixtures currently select base centers. The lower `SuppliedTransport` suite executes both actual
odd and binary quadratic branches, including F4 to F16. A public interpolation/normalization
fixture selecting each quadratic branch remains an acceptance-test obligation; it is not a gap in
the generic exactness proof.

## Positive-order chart: separate acceptance

The positive-order dispatcher remains prime-field specific. The checked differential
APIs require the coefficient field's actual characteristic, not an unrelated numeric
bound. Worker 2 repaired `fundamental?` and `nonlinearNewton?` to require
`CharP E p`. The exact reviewed solver checkpoint is `ff8b3aab2e9dd770816eadbf857baa1d77710b2d`.
Its full private gate and native characteristic/second-order tests passed. The one-chart
integration was independently accepted and passed the full combined gate at published
checkpoint `0c54212998b62ee34214493fab5995a43906f8d1`.
Raw arithmetic helpers remain conditional on the hypotheses of their correctness lemmas.

The actual constructor executes projection, weighted monic reduction, sample search,
local quotient inversion, nonlinear lifting, clearing and recovery. Nonlinear precision,
initial-jet invariants, literal numerator provenance from actual solver output, and
bounded recovered degrees compile. Public returned-chart geometry, normal-form and
input-to-success contracts compile. The global contract identifies the actual cleared
numerators and denominator after arbitrary coefficient-field embeddings and proves the
regular-locus agreement identity. Stored solution
precision is `k`; the positive-order residual precision is `k-r`. All-chart tangent/coverage
production and global dispatch remain later obligations.

Use “candidate cover” for one-way inclusion of wanted messages. It can include
extraneous Taylor truncations and extension points. Final recovery and agreement
filtering establish exactness. Do not add an artificial Lean wrapper for terminology.
Point-independent direct chart systems may be constructed before solving; a helper
requiring the unknown point and checking its separant cannot replace that producer.

## Acceptance tests and publication

Exercise supplied extensions with `n > p`; binary ordinary lifting with `k > p`;
degree-one and theta-zero presentations; `p`- and `p²`-multiplicities; mixed inseparable
factors; both quadratic center branches; prefixes crossing the base field; `k = 1`;
and final agreement rejection. These are required cases, not current pass claims.

Run focused producer/consumer tests and the combined
`LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true ./scripts/validate.sh --axioms` gate
in the isolated integration worktree. Require fresh independent review of the exact
integrated diff before publication. Report zeroth-order completion and positive-order
chart progress separately, preserving the accepted admission baseline.
