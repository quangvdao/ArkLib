# Four-hour decoder and strengthening sprint

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
