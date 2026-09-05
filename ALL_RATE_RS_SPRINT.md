# Four-hour decoder and strengthening sprint

**Closed within the gate.** All proof implementation stopped by 09:18 UTC. All worker tasks and
strengthening descendants are stopped. Final central code validation completed at 09:21 UTC;
the remaining closing actions were documentation, commit/push and remote verification.
The original full bit-complexity theorem and general small/intermediate-gap MCA remain unproved.

## Hard stop

The user authorized this local-only four-hour sprint on September 5, 2026.
It supersedes earlier instructions to continue indefinitely until the theorem is complete.

| Event | UTC, September 5 | Phoenix |
|---|---|---|
| Start | 05:51:04 | September 4, 22:51:04 |
| Frontier and risk checkpoint | 08:51:04 | September 5, 01:51:04 |
| Stop new proof/implementation; consolidate | 09:21:04 | September 5, 02:21:04 |
| All worker handoffs and stops | 09:36:00 | September 5, 02:36:00 |
| Final push, report, and stop | **09:51:04** | **September 5, 02:51:04** |

These limits apply to the central orchestrator, all decoder lanes, the strengthening
coordinator, and every strengthening subagent. No agent may extend its own deadline.
After the cutoff, only bounded preservation, validation and handoff operations are allowed;
do not start another mathematical objective. Confirm every descendant has stopped.

## Outcomes and acceptance

- **Primary:** finish the original, pre-strengthening Theorem 1.1, with literal executable
  exact output, both field regimes, constants and gap-only dependence, and proved cost for
  that same program in an explicitly stated model. A primitive ledger alone is not its bit bound.
- **Must:** preserve the strongest coherent, validated result on the single central branch;
  record exact validation and an independent audit, unfinished proof obligations, and useful
  non-integrated work. Stop at the deadline even if the primary theorem remains incomplete.
- **Should:** close the remaining outer parameter/branch/list/cost joins while completing
  coordinate lowering and concrete bit-RAM representation/compilation prerequisites.
- **Stretch:** finish unconditional field-independent list and mutual correlated-agreement
  results along the shortest substantive dependency path. If the original theorem closes,
  transfer the decoder workers immediately to non-overlapping strengthening assignments.

The deadline fallback completes this sprint, not an unfinished mathematical theorem. Do not
label a weaker theorem, conditional backend, or assumed geometry interface as the original result.

## Ownership and resource policy

Central task `01a06c48-8980-76a2-b439-9872f827bfcd` owns integration, the original decoder,
this record and [the main tracker](ALL_RATE_RS_FORMALIZATION.md).
The three decoder lane IDs and exclusive claims are maintained there. Lane A independently
audits the new outer decoder, which it did not author, before continuing bit-code work.

Strengthening task `01a07013-4475-7522-ace6-e5dab07fad0a` owns
[the strengthening plan](ALL_RATE_RS_STRENGTHENINGS.md), its progress log, and up to three
Sol/high subagents. It propagates and enforces the same deadline, reserves independent audit
capacity, and reports major findings and integration-ready commits. It does not redirect the
three decoder workers or edit their files. All results return to the same central branch.

Execution is on this Mac only: 16 logical CPUs, 64 GiB RAM, approximately 479 GiB free disk
at the opening check. Use normal, coordinated concurrency: isolated targeted builds may overlap;
coordinate expensive full gates. Shared dependency sources/artifacts remain read-only. Preserve
user changes and agent worktrees. Do not spawn another coordinator or recursive agent tree.

## Baseline and validation

Central checkout: `/Users/quangdao/Documents/Lean/ArkLib-all-rate-rs-capacity`.
Integration branch: `quang/all-rate-rs-capacity-formalization`.
Push remote: `fork`, `https://github.com/quangvdao/ArkLib.git`.

Opening committed baseline: `77ad3e8b12f5c0537f99aaba1d10511edd5e4e4f`; in-progress
outer-decoder and agent changes were retained and subsequently validated in `41002c81`.
Upstream `origin/main` was fetched at start and resolved to
`a527b514e029ecf9da40d66b5531a0707c686edc`. It is not an ancestor of the current research branch.
Do not silently replace the requested research integration target with an unrelated upstream
migration. No upstream merge, PR, announcement, force-push, worktree deletion or dependency
upgrade is part of this sprint.

Every central checkpoint requires `./scripts/validate.sh --axioms`, source/import inventory,
diff checks and statement review. Stage new modules before generating `ArkLib.lean`.
No new admissions, nonstandard axioms, native trust or resource/linter suppressions are allowed.
Keep the repository's existing debt distinct from this proof's dependency cone. Final acceptance
also requires an independent statement/execution audit and verification of the pushed remote SHA.

At the deadline, report the exact proved frontier, final SHA, validation and audit findings,
remaining gaps, retained work and stopped-agent status. The stronger claims require their own
unconditional proofs; their smaller output bound does not automatically improve decoder time.

## Integration checkpoint, 06:48 UTC

- `300ea830` proves `capacity_decoder_exact_output_and_primitive_work` for the actual
  integer-input decoder. Its same-run primitive bound is not yet the full bit-time theorem.
- `0f28ac0d` adds the independently reviewed kernel-height, half-gap correlated-agreement,
  and universal Taylor-support results. Both checkpoints passed full validation and were pushed.
- Current integration adds actual binary addition/comparison/subtraction, a fixed-tape
  prefix-block writer with exact traces and memory frame properties, shared-list heap
  representation and writer execution, and coordinate residual recovery/indexed updates.
  The second strengthening checkpoint adds actual line/affine MCA bounds, fixed symbolic
  interpolation margin, filtered Hilbert principal cuts, and denominator algebra.
- A owns retained-operand binary field arithmetic; B owns cell-payload materialization and
  the same-memory fixed-tape cell writer; C owns the coordinate direct-coefficient controller
  and subsequent lift loop. Central owns the block-reader controller and integration.
  The strengthening coordinator owns rational Taylor charts, symbolic-line interpolation,
  and concrete geometric counting. These claims do not overlap.
- Remaining original-theorem joins include complete coordinate lowering, concrete heap
  allocation/read and scalar operations, whole-driver representation/width invariants,
  input/output materialization, and a same-program bit-time bound. No conditional backend
  or primitive ledger is being substituted for that final theorem.

## Read/write and coordinate checkpoint, 06:58 UTC

`cbe45968` passed the full canonical gate and was pushed. Its source admission count is
unchanged (183 repository-wide), and its axiom sweep found no new taint. The next checkpoint
connects actual cell-payload construction to bit writes on one fixed eleven-tape bank, adds
modular negation and an actual subtraction-borrow flag, and executes both direct-coefficient
recoveries and the intervening coordinate update. Central independently read all those changes.

Central's block reader now has exact access/reset/output-reversal traces, an unchanged-memory
theorem, per-position observations, and read-after-store correctness. Lane B independently
audited it and ran non-palindromic/nonzero-offset/dirty-memory/short-fuel canaries; its only finding
was a corrected long source line. A further fixed fourteen-tape controller physically separates
the live tag, head and tail. Its exact count includes the parser handoff, tag test, head scan and
reversal. Malformed payload rejection preserves all tapes. Kernel checks include an actual
cell-write followed by its actual read and parse, with exact final-step boundaries.

Input length tapes are explicit materialized inputs, not free length computation. General
allocation, whole-driver instruction lowering, retained-state width bounds and serialization
still need composition before a full decoder bit-time theorem can be asserted.

## Scalar, allocation and symbolic-certificate checkpoint, 07:23 UTC

`5d87acd7` passed full validation and was pushed: it contains the actual rational Taylor charts,
their cleared equations and cuts, extension-field symbolic local ranks, and the coordinate
regular-lifting loop. Source admissions and axiom taint did not increase.

The next audited integration adds these concrete joins:

- Literal retained-modulus addition and repeated-addition multiplication on fixed bit tapes.
  Multiplication uses an actual binary countdown; its cost is polynomial in the modulus value.
- Actual fixed-width pointer advancement followed by payload construction and a cell write,
  on one twelve-tape bank and one RAM. The overflow branch preserves the original memory.
- Physical width-marker construction and scalar padding. Worker B independently audited all
  three main-authored modules and additional kernel canaries, with no findings. Fixed-width
  modular addition composes the actual adder and padding child with a tape-preserving handoff.
- Coordinate candidate preparation and residual acceptance, with literal arithmetic children
  and same-execution primitive ledgers. These are not yet bit-lowered decoder instructions.
- The unconditional prescribed symbolic-band certificate: no rank or coefficient-height
  hypothesis remains. The interpolant has challenge degree below `338(2m - 1)`, total jet degree
  at most `2m - 1`, and remains nonzero and sound over every extension field. Actual standard
  monomial quotient bases, retained prime-cut covers and zero-dimensional point counts support
  the remaining geometric proof; they do not yet prove the final field-independent list bound.

Ownership now: A inversion and core field instructions; B reduced-scalar allocation and heap
instruction joins; C coordinate shift, candidate/root enumeration and whole coordinate decoder;
central fixed-width arithmetic adapters, integration and whole-driver backend composition.
The strengthening coordinator retains geometry and the stronger endpoints. The original full
bit-time theorem remains open, and all four-hour stop times above remain unchanged.

## Inverse and coordinate enumeration checkpoint, 07:35 UTC

`8a619227` is pushed after full validation: 25,726 declarations in 905 modules, no new axiom
taint, 183 source admissions unchanged, and zero explicit axioms or native trust. Worker B
independently accepted the fixed-width modular-add adapter and the subsequent multiplication
adapter, including extra modulus-one and padded-zero canaries. The multiplication adapter
executes its own normalization, so fixed-width callers do not owe a free canonicalization.

The next integration includes actual prime-field inverse search with retained modulus and
input, scalar-to-heap allocation, coordinate center translation, full lift/filter/translation
acceptance, and ordered initial-jet enumeration. Coordinate center/stage enumeration and
canonical guards still need their own lowerings; the original bit-time theorem is not closed.
The strengthening checkpoint constructs the unique Hilbert polynomial of each actual affine
quotient, proves the principal-cut degree/coefficient inequalities and relative height one,
and bounds zero-dimensional points by the actual quotient dimension. Absolute component-degree
purity and the refined degree sum remain necessary before the stronger list theorem is proved.

## Shared-memory evaluation and coordinate stages, 08:13 UTC

`ac761d3f` is pushed and passed full validation: 26,433 declarations in 926 modules,
312 pre-existing tainted declarations and no new taint or nonstandard axioms. Source admissions
remain 183. The next integration contains physical fixed-width inverse and negation adapters,
retained-modulus equality, a prepared reader and nil-aware uncons, and an actual shared-memory
Horner loop. The loop charges its pointer/index clearing, tail-pointer movement, multiplication,
addition and final nil scan. Its initial accumulator is explicit; lane B is implementing the
physical zero initialization before claiming a closed evaluation entry.

Coordinate normalization, differentiation, highest-variable selection, separant-chain generation,
center and stage enumeration now execute their actual base arithmetic children. Their same-run
refinements retain ordering, duplicates, complete stage contexts and failure tags. Lane A owns
the disjoint canonical-guard/candidate/acceptance/output branch; lane C owns the prepared and
separate-sample outer decoder. Their field-level ledgers are not bit-cost theorems.

Central's allocation-capacity invariant derives the actual allocator's no-overflow premise from
an explicit remaining budget and decreases that budget on the same successful RAM execution.
It deliberately does not assume or claim the missing whole-decoder lifetime-allocation bound.
The strengthening team has additionally proved invariance of Hilbert-polynomial degree under
radicals, concrete localization filtration comparisons and finite-prime separator inequalities.
Its absolute component-purity/refined-degree endpoint is still separate.

The original full bit-time theorem remains open: closed driver lowering, global representation
and width/lifetime invariants, physical input/output and the final same-program cost composition
are not supplied by merely collecting these component results. The hard deadlines are unchanged.

## Complete coordinate outer and affine degree checkpoint, 08:41 UTC

`9e551abe` passed the full canonical gate and is pushed: 27,858 declarations in 975 modules,
312 pre-existing tainted declarations, zero new taint/nonstandard axioms, and 183 unchanged source
admissions. The next checkpoint contains the full prepared/separate-sample coordinate pipeline,
canonical filtering and collection, actual three-alphabet materialization, and executed
interpolation/setup composition. Its fixed fuel uses only initial integer parameters. Exact
output and the work bound refer to the same actual program; they still do not assert bit time.

Physical Horner evaluation now constructs its own zero accumulator. Main's word-copy controller
and allocation budget, padded inverse and padded negation passed independent worker-B audits.
Main's alphabet materializer passed worker-A audit. The literal register ADD passed worker-C
audit, including all alias partitions and observations of the entire fixed 28-tape bank. MUL
likewise copies both operands before overwriting a possibly aliased destination and explicitly
clears retained temporaries. Main read both implementations and their actual source-step joins.

The strengthening integration now proves the unconditional refined principal-cut degree sum.
Degree is factorial times the leading coefficient of the actual coordinate quotient's Hilbert
polynomial. Noether normalization and finite-extension growth prove purity; no purity or degree
law is postulated. Finite principal-open and terminal point-count lemmas are also proved. The
finite agreement-incidence/list/MCA endpoint remains a separate assembly obligation.

Ownership: A audits the coordinate core and outer composition; B completes register-level NEG/INV;
C supplies same-run coordinate numerical bounds; central closes the integer dispatch and integrates.
The strengthening coordinator retains geometry/list/MCA and its three bounded descendants. The
09:21 proof stop, 09:36 worker stop and 09:51 final hard stop remain in force.

## Three-hour risk checkpoint, 08:51 UTC

`188a9820` is pushed after full validation: 29,312 declarations in 1,034 modules,
312 pre-existing tainted declarations, no new taint/nonstandard axioms, and 183 source admissions
unchanged. `CoordinateCapacityMachine.run_exact` now proves all-rate exact execution on the
same integer coordinate decoder, including exceptional blocks and both field regimes. The
central `Capacity.lean` primitive-work theorem is being switched to this implementation without
adding another public theorem or changing its mathematical output/list-size clauses. Independent
audits accepted the core, parameter branches and integer dispatch, and all four physical
ADD/MUL/NEG/INV register instructions. Durable independent full-bank replays are integrated.

The full bit-time theorem is **not expected to close in the remaining proof window**. Local
tape-update shape alone does not force finite-control/head-only branching. A separate finite
head-program interpreter and exact word-copy refinement are being proved to expose that
adequacy obligation. Whole-decoder instruction compilation, bounded lifetime allocation and
representation widths, integer/fuel arithmetic and physical input/output remain outstanding.
Standalone arithmetic instructions do not discharge those obligations by themselves.

The strengthening team has certified the actual regular-solution field-independent bound
`ν * (n * (1 + 2K(ν - 1)) / (A - k + 1))^r`, via the explicit algebraic-closure embedding,
actual chart geometry and cardinality preservation. The singular/order-restriction join is
its immediate priority. General small/intermediate-gap MCA and its image/envelope/generic-fiber
argument remain unproved and are unlikely to finish in this sprint. No conditional geometry
interface or regular-only result is being presented as the final all-solution theorem.

The deadline fallback remains preservation of verified progress, not mathematical completion.
All workers acknowledged the unchanged cutoffs. Central owns register initialization and final
integration; A owns finite-head adequacy; B owns remaining load/output/dispatcher instructions;
C independently audits new instructions and initialization. No overlapping implementation claims.

## Coordinate capstone and independent instruction audits, 09:03 UTC

`19e7505b` is pushed after full validation: 29,775 declarations in 1,048 modules,
312 pre-existing tainted declarations, zero new taint/nonstandard axioms, and 183 unchanged
source admissions. `Capacity.lean` now names the actual coordinate decoder in its existing
primitive-work theorem. Lane A independently audited that public statement and the executed
core, all-rate dispatch and budget branches. No output or mathematical clause was weakened.

Physical initialization constructs all eight zero registers and both false flag bits in exactly
`19 * width + 40` transitions from blank register storage. Lane C independently replayed every
one of the 28 physical tapes, dirty destination handoffs, all five load selectors and the actual
flag pop/push boundary. It found no correctness issue and rejected deliberate restoration,
uncharged-clearing and selector mutations. These are component audits, not a full bit-RAM claim.

The next integration contains a complete 24-state, six-tape finite-head literal controller and
physical pair/Boolean output instructions. The strengthening coordinator has closed the singular
recursion and assembled the prescribed field-independent list bound in both characteristic zero
and characteristic at least the block length. That checkpoint is undergoing its full gate.
Central is connecting this geometric bound to the existing decoder's identical physical output;
the primitive-work bound will remain unchanged. No faster decoder or general MCA theorem is claimed.

## Field-independent list assembly and physical dispatch, 09:13 UTC

Strengthening checkpoint `0646f443` passed its private full gate and is integrated for central
validation. It proves the entire degree-`<k` agreement list finite with bound
`4m² (4m/δ)^d n^d`, including both regular and singular differential solutions, in characteristic
zero or characteristic at least `n`. The canonical codeword-list function satisfies the same
bound rounded upward to a natural. The order, multiplicity and `8m` threshold are prescribed;
there is no assumed degree law, separant-count interface or regular-only restriction at this endpoint.

Central's `GeometricOutputBounds.coordinate_run_list_bound` passes its targeted build and states
that the identical coordinate decoder output satisfies this field-independent bound. The original
observed primitive work, including the larger-field saving, is unchanged. No runtime operation
or alternative output is introduced. Its equality-instance conversion is confined to the proof
of exactness; the executed prime-field decoder retains its concrete equality implementation.

Finite-head literal construction and static injective tape placement preserve all fuel prefixes.
The unified scalar dispatcher has a bounded instruction cursor, physically exact initialization,
all eight literal child kinds and tape-preserving returns, including adoption of updated equality
flags. Generic whole-program scalar correctness/cost and finite-head adequacy of that dispatcher
are still separate. Lane C independently audited literal/pair/Boolean components, adding full-bank
kernel replays and rejecting seven injected implementation faults. It is now auditing the dispatcher
and placement; lane A independently audits the geometric output bridge.

## Final implementation handoffs, 09:19 UTC

`792288c4` is pushed after full central validation: 30,218 declarations in 1,064 modules,
312 pre-existing tainted declarations, zero new taint/nonstandard axioms, 183 source admissions
unchanged. The exact strengthened-output bridge also passed a separate strict rebuild and audit
against 361 frozen local dependency hashes. Its public statements retain the actual decoder,
both primitive-work regimes, original output and exact threshold semantics.

All new proof work finished before the 09:21 cutoff. Final integration consists of:

- B's `a23020c9`: actual dispatcher-to-child-to-return traces for all eight instruction kinds.
  Scalar cases include observed execution, decoded updates, fixed widths, reduced residues and
  both charged control steps. Whole-program induction, total bound and head-only adequacy remain.
- C's `0f391ed1`: seven permanent kernel replays for complete ADD/EQUAL programs, equality-to-Boolean
  flag adoption, empty code and rejected child halting. Concrete tests do not replace the generic proof.
- Strengthening `98c075b5`: the selected order-one certificate with no upper-rate premise,
  coefficient challenge degree at most 1449 and total jet degree at most 119. Nonzero specialization
  and the close-polynomial differential identity hold at every extension-field challenge.
- Updated bit-backend and strengthening handoffs, distinguishing certified components from the
  unfinished global compiler and joint-envelope/generic-fiber MCA argument.

Central independently read and audited the final 194-line B composition against the previously
audited children. Every scalar return adds exactly two transitions; pair/Boolean halt after their
actual output child, and LOAD/EQUAL retain the correct input/register/flag projections. No missing
whole-program theorem is hidden in these statements. The selected certificate had a separate
exact-source mathematical audit in its lane and was fully read again before central integration.

### Resume only with a new authorization

| Track | Next proof obligation | Existing entry point |
|---|---|---|
| Scalar program | Compose initialization and the eight instruction cases into generic literal-program correctness and a uniform total bound; then prove finite-head adequacy | `QuadraticArithmeticBitProgramExecution.lean`, `FiniteHeadProgramPlacement.lean` |
| Decoder compiler | Lower the remaining coordinate-controller clauses, natural/fuel administration and representations to the concrete backend | `CoordinateCapacityExecution.lean`, `docs/design/rs-bit-cost-backend.md` |
| Global resource bound | Derive initial word widths and cumulative allocation, preserve them across the whole run, account for external input/output, and join the same-program bit-cost bound | `HeapAllocationBudget.lean`, shared-list backend, decoder primitive budgets |
| General MCA | Actual mixed-degree rational image/joint envelope, generic fiber, graph-line-excluded incidence, exceptional-set equality and low-dimension cases | `ALL_RATE_RS_STRENGTHENINGS_FRONTIER.md` |

The first three rows are needed for full original algorithmic Theorem 1.1. The last row is a
separate strengthening. The field-independent list theorem and its reuse of the existing decoder
are proved already. No reliable small epoch estimate is asserted for the unfinished compiler.

## Final validation and stopped roster

Final full-code gate: `./scripts/validate.sh --axioms` passed. The umbrella imports 1,066
modules; the sweep checked 30,267 declarations across 1,067 modules. It found 312 pre-existing
sorry-tainted declarations, **zero new taint and zero nonstandard-axiom taint**. Source inventory
remained at 183 admissions, with zero explicit axioms and zero native-trust constructs. The final
test-only increment adds seven kernel examples. No trust baseline or resource limit was relaxed.
Existing repository debt is not evidence of an admission in the newly audited theorem cones.

Reproducible local receipts are `/tmp/rs-final-sprint-validation.log` and
`/tmp/rs-final-sprint-source-trust.json`; the source and validation scripts are on the branch.
Independent final audits cover the exact coordinate public capstone, strengthened same-output
bridge, register instructions/initialization, finite-head literals/placement and scalar dispatcher.
Auditors rebuilt frozen source slices with trust zero and checked endpoint axiom dependencies.
Their mutation probes rejected stale flags, source restoration errors, uncharged clears, wrong
selectors/head routing, fabricated returns and nonadvancing cursors. Permanent kernel regression
modules preserve representative complete executions and exceptional cases.

| Worker task | Final private checkpoint | Stop confirmation |
|---|---|---|
| A: `01a06e56-bed2-72f2-9bba-78de078e8a81` | `4e9896df` | Completed; app status idle |
| B: `01a06e56-c0dc-7ea0-90fd-499425b394f9` | `a23020c9` | Completed; app status idle |
| C: `01a06e56-c2e1-7101-8774-21db0a570b2d` | `0f391ed1` | Completed; app status idle |
| Strengthening: `01a07013-4475-7522-ace6-e5dab07fad0a` | `98c075b5` | Completed; app status idle |

The strengthening coordinator confirmed all three descendants completed before 09:18 UTC:
`geometry_audit` (Copernicus), `half_gap` (Plato), and `kernel_height` (Sartre). The three older
central audit subagents were already completed. There is no running proof lane. Future work
requires a new user authorization; the longstanding full-theorem objective has **not** been
marked achieved merely because this bounded sprint ended.

Private worktrees and frozen audit scratch were preserved without destructive cleanup. The
strengthening lane additionally archived 85 unvetted scratch files locally; its archive hash and
location are in the strengthening progress log. Those files are not certified source or proof
dependencies. No upstream PR, announcement, remote compute or dependency upgrade was performed.
