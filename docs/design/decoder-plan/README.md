# Complete the paper decoder

This is the current coordination hub for the Reed–Solomon paper decoder on
`quang/rs-capacity-and-correlated-agreement` in `quangvdao/ArkLib`.
It replaces the completed A–E worker assignments and earlier decoder sprint notes.

The original foundation source baseline is
[`3c67cb3fa669985b2add6c5d080a3060c4728789`](https://github.com/quangvdao/ArkLib/commit/3c67cb3fa669985b2add6c5d080a3060c4728789).
The preceding accepted integration base is
[`b626a599817381cfb84155f8b74d9cf6ff0c18a4`](https://github.com/quangvdao/ArkLib/commit/b626a599817381cfb84155f8b74d9cf6ff0c18a4).
The [new backend/public collection](backend-public-checkpoint.md) records subsequent exact sources.
The dedicated zeroth decoder is complete. The full positive-order symbolic decoder is not:
`HiddenDerivativeDecoder.symbolicDecode` still returns `symbolicBackendUnavailable`.

Read the [verified status](status.md), then the [shared contracts](contracts.md),
[workstream assignments](workstreams.md), and [launch and acceptance workflow](workflow.md).
The contracts describe required semantics. The first stored chart payload is implemented, and
the [varying-order checkpoint](varying-order-checkpoint.md) now provides semantic traversal,
canonical fuel and dependent dispatch. Concrete component production remains open. See also
[the Taylor checkpoint](taylor-checkpoint.md).

## Target and scope

Implement and prove correctness of the paper's eight procedures:
`ExactHiddenDerivativeDecode`, `RecoverAgreement`, `FirstOrderNormCandidates`,
`PairedCandidates` in both selection modes, `FastRegularTaylorFamily`, `SplitZeroUnit`,
`PreprocessFiber`, and the dedicated `ZerothOrderDecode`.

The final theorem concerns the actual executable program and the existing `ExactOutput` predicate.
Valid input/options, with a supplied explaining equation or a valid support certificate, must
produce the complete duplicate-free agreement list. A theorem about successful runs alone is
insufficient. Constructor coverage and solver correctness must be proved for concrete producers.

Termination, algebraic invariants, and correspondence with the named algorithms are in scope.
Arithmetic, bit, RAM, and native running-time bounds are not. This exclusion does not authorize
replacing Newton doubling, the norm decomposition, paired selection, or Rojas with another program.
MCA/proof-system development and paper edits are outside these worker assignments.

The paper-side specification is `docs/decoder-formalization-plan-2026-09-11.md` and the Taylor
construction is `appendices/decoder-taylor.tex` in `quangvdao/rs-capacity-and-correlated-agreement`.
At launch the coordinator supplies an immutable paper revision or accessible excerpts. Report
inaccessible sources; do not invent paper details. The ArkLib plan records implementation status,
while the paper defines the mathematical target.

## Adopted zeroth-order specification

The revised zeroth-order paper pin is `b1be8b89069542faacac40a7e92068857b43e97a`.
See [the split delivery plan](zeroth-supplied-field.md). This is a new supplied-field
composition obligation, separate from the positive-order chart milestone below.
The latter retains prime-field dispatch and characteristic-certified differential guards.
It accepts supplied polynomial-basis F_q with q >= n,
without a characteristic or extension-degree bound. Constructing a field from q alone is not
required. Positive-order algorithms retain their prime-field scope. Large binary extensions
must use the dedicated ordinary path, not the old small-characteristic fallback argument.

## Current task board

Personal 4 coordinates integration and owns G03–G05 and G10. Personal 1 owns G01/G02/G06.
Personal 3 owns G07–G09. All three teams have resumed under the revised zeroth-order
specification. Personal 2 is unavailable. New worker checkpoints require separate collection
review and validation before becoming integration dependencies.
The [Personal 1 checkpoint](personal-1-checkpoint.md) records the earlier seven slices.
The [normalization checkpoint](normalization-checkpoint.md) records the earlier executable slice.
The [three-track collection](three-track-checkpoint.md) adds full generic normalization
correctness, supplied-field arithmetic/centers and the completed one-chart Taylor contract.
The [public zeroth-order checkpoint](public-zeroth-checkpoint.md) records their executed
composition. The [fixed-order Taylor coverage checkpoint](positive-coverage-checkpoint.md)
records the next positive-order assembly boundary. The [Personal 3 checkpoint](personal-3-checkpoint.md) records the six collected slices and their
remaining obligations. Personal 4 remains the sole core integration owner.

| ID | Work | State | First action |
| --- | --- | --- | --- |
| I0 | Shared Lean interface freeze | Personal 4; fixed-order coverage and candidate APIs available | Freeze P1 component/constructor bridge and varying-order consumer signatures |
| G01 | Function-field algebra and normalization | Generic normalization and first-order descent complete | Support concrete regular-component construction |
| G02 | Full squarefree decomposition | Personal 1 backend collected; actual supplied-field success proved | Consume from concrete component/first-order integration |
| G03 | Taylor geometry | P4 stage/order assembly complete; P1 owns concrete components | Produce regular components and sufficient centers from original inputs |
| G04 | Taylor local algebra and lifting | One-chart lifting/success complete | Preserve characteristic guards through varying-order dispatch |
| G05 | Taylor reconstruction | Semantic traversal and canonical fuel complete; global coverage conditional | Connect concrete components to varying-order solution coverage |
| G06 | First-order norms | Concrete backend collected under chart premises | Discharge constructor premises and compose final recovery |
| G07 | Explicit fields | Prepared supplied inverse and general extensions complete | Consume published constructors |
| G08 | Rojas producer | Personal 3 actively continuing foundations | Resultant semantics, quotient identification and isolated-root factor theorem |
| G09 | Higher-order selection | Conditional independence selection; P1 takes remaining proof lane | Preserve agreeing labels, prove exact energy bound, then compose G08 |
| G10 | Supplied-field zeroth-order decoder | Public actual-run exactness complete | Preserve base/odd/binary public regression coverage |
| I1 | Integration and independent review | Personal 4 | Collect exact producers and prove public positive-order exactness |

At each launch record the lead, exact branch/base, owned files, first deliverable and acceptance
check here or in the corresponding group section. Record explicit dependency commit SHAs as they land.
Do not substitute a moving branch name for an agreed interface revision.

## Next substantial delivery wave

The [backend/public collection](backend-public-checkpoint.md) records this wave's sources.
The next targets are intentionally larger than individual helper lemmas:

- Personal 1: construct actual regular components and close constructor-to-first-order chart
  premises, giving Personal 4 a usable producer. In a separate lane, repair G09 agreeing-label
  capture and prove the exact graph energy estimate.
- Personal 3: continue the already active G08 resultant and Rojas foundations. Do not restart
  or duplicate that work. General extensions and prepared inverse Frobenius are completed.
- Personal 4: cover varying active orders and semantic separant chains, then close the public
  first-order decoder and compose higher-order producers as their exact contracts become available.

The remaining G09 energy estimate is a distinct analytic obligation. Current selection also
needs its agreeing-label invariant exposed before common-zero capture can be composed.

Publish independently reviewed and fully validated checkpoints along the way. A checkpoint
records progress; it does not close a larger target whose completeness obligations remain.
All leads and subagents use GPT-5.6 Sol High. Preserve disjoint source/build ownership and
use a nonauthor reviewer for substantial mathematical and integration changes.

## Parallel organization

The ten groups support a proposed team of roughly 20–30 authors and reviewers once interfaces
stabilize. This is a staffing proposal, not a measured optimum or a tool-concurrency promise.
Split a group only when another worker has an independent deliverable and separate file ownership.
Each group needs compilation capacity; uncompiled patches otherwise accumulate at integration.

Use the completed algebra, fields and zeroth decoder as frozen dependencies. Split concrete
component construction from varying-order coverage and final recovery. G08 foundations and the
G09 analytic estimate can advance independently of first-order public completion.

| Consumer milestone | Required groups and already available components |
| --- | --- |
| Dedicated zeroth-order exact decoder | G10 + ordinary normalization from G01 + G07; reuse quotient Newton and recovery |
| Closed first-order exact decoder | G03–G05 Taylor + G01/G02/G06 norm pipeline + G07; reuse tower preprocessing/materialization/recovery |
| General-order all-subsets exact decoder | Taylor + G07 fields + G08 Rojas + G09 direct-system capture; reuse common recovery |
| Complete paper decoder | Both higher-order selections, global separant/center loop, supplied-equation and certified-support success, public theorem and algorithm correspondence |

Rojas production and the expander spectral certificate need early feasibility checkpoints.
More integration workers cannot remove those mathematical dependencies.

## Coordination ownership

The coordinator owns shared contracts, top-level dispatch and correctness, public reader maps,
umbrella generation, runtime-suite registration, dependency pins, and this task board.
Groups own the source areas in [workstreams](workstreams.md); existing source owners remain read-only
until an explicit transfer. An independent reviewer checks statements and algorithm correspondence.

Completion has separate stages: proposed, assigned, implemented, locally verified, integrated,
and accepted. Only the last stage closes a work package. See [workflow](workflow.md).

## Superseded records

Completed A–E assignments and their patch provenance remain in
[the foundation checkpoint's history](https://github.com/quangvdao/ArkLib/tree/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/decoder-workers).
Earlier [algebraic-machine planning](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/rs-algebraic-machine-plan.md),
[bit-cost planning](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/docs/design/rs-bit-cost-backend.md),
and [continuation logs](https://github.com/quangvdao/ArkLib/blob/3c67cb3fa669985b2add6c5d080a3060c4728789/PROGRESS.md)
are historical evidence, not active instructions. Their source implementations remain available.
A commit-pinned historical URL is immutable; current coordination lives only in this directory.
