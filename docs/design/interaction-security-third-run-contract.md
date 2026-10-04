# Proposed 5½-hour contract: connect native restoration to existing Fiat–Shamir security

**Status:** authorized and launched October 4, 2026, at 05:07:49 UTC (01:07:49 America/New_York).
**Budget:** 5 hours 30 minutes. Deadline 10:37:49 UTC (06:37:49 America/New_York).
Checkpoint 09:15:19 UTC; new-work freeze 09:37:49 UTC.
This replaces the earlier six-hour draft. The theorem statements below are targets, not completed proofs.

## Outcome and reuse baseline

Deliver a native single-salt, full-prefix Fiat–Shamir security theorem derived from native
round-by-round knowledge certificates, with an expected distinct-query bound for verification
that actually stops on rejection. Prove the relationship to the existing canonical FS results;
do not independently recreate their conditional SR-to-FS theorem.

Reviewed native source: ArkLib integration `e3a1793a45a461b42ab7b8845d6c3c8120ba0e75`,
VCVio `6bf6c91b66dfa159342c355a4b81d65b55cb54a4`, Lean 4.34.0.
Existing FS source to reuse, with original attribution:

- [#469](https://github.com/Verified-zkEVM/ArkLib/pull/469),
  `036d6f561f6e33cc02d0712095c09ebfc3f1ffb1`: salted constructions, codecs and Section 5 machinery.
- [#848](https://github.com/Verified-zkEVM/ArkLib/pull/848),
  `1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb`: canonical single-salt soundness/knowledge transport
  and conditional duplex results. Its baseline is Lean 4.33.1 with VCVio `eb22883264cd2fd513df4ee7db1bc5a86ec789c7`.

The [overlap audit](fiat-shamir-open-pr-overlap.md) distinguishes proved reductions from deferred
Section 5 obligations. Refresh exact PR heads at launch. Pin the chosen snapshots in the run record.
Import or port only the necessary reviewed mathematics onto a compatible dependency baseline;
do not undertake an unrelated toolchain migration or modify the authors' PR branches.

The current same-cache adversary-to-completion bind is already proved. Reproving it alone is
not an outcome. The concrete DSFS Key Lemma is not proved by the existing conditional theorems.

## Scope fixed for this run

- A fixed finite schedule of message/challenge rounds, finite message carriers, and a common
  finite nonempty uniform challenge carrier. Zero-round cases use zero total/max error.
- Pure guards on the reconstructed prefix/current message, before that round's hash query.
  Rejection stops execution. Guards may not query the current/future challenge cell.
- A single global salt in the proof, represented in the restoration input as `(statement, salt)`;
  restoration per-round salt is `PUnit`. Unsalted FS is the global `PUnit` specialization.
- Typed full-prefix challenge keys are the MUST interface. An external encoded domain with
  off-image queries is SHOULD S2, explicitly demoted from the earlier draft to focus the shorter
  run on the native/legacy bridge. Do not advertise concrete byte-string or XOF security from MUST.
- Core native stopped security retains arbitrary decidable input/salt domains. The exact legacy
  eager-table comparison is restricted to its finite compatible fragment; do not impose that
  restriction on the native owner theorem or posit a uniform finite sampler for an infinite table.
- Arbitrary finite malicious oracle computations, adaptive statement/proof selection, interleaved
  private randomness, repeated/out-of-order queries, and returned failure.
- Full message proofs and accept/reject endpoints, with a generic input witness relation. This
  is not succinct oracle elimination. If a client retains an input oracle, the result remains
  relative to that oracle until a separate realization theorem is supplied.
- Named extraction with explicit access and terminal seed. No PPT/runtime, deterministic
  prover-trace-only, zero-knowledge or universal relation-to-relation claim.

These describe one theorem family, not a permanent limit on the interaction framework.

## MUST 1: actual stopped restoration security

Define guarded completion using the existing native runner and restoration keys. A malicious
proof supplies a complete message sequence; no default message is invented on rejected paths.
Let `Jstop(A)` be the actual joint run of adversary A and stopped verification from empty cache.
Let `D(Jstop)` be its distinct queried keys and let `epsilon(key)` be its round's fixed local error.

From an all-authored-prefix knowledge certificate, prover preservation, the input relation law,
and an explicit terminal seed whose validity follows from acceptance, prove

    Pr[accepted and not Rin(x, Ext(x, proof, H))]
      <= E[sum (t in D(Jstop)), epsilon(t)].

`Ext` must be the named backward extractor applied to that exact terminal seed. An existential
terminal witness, or assuming the desired input relation, is not an adequate replacement.

Required proof obligations:

1. Native verification and the stopped program have the same returned result, ordered challenge
   log and final cache, under the declared instrumentation and key map.
2. For every fixed table and every supported privately randomized run, accepted invalid extraction
   yields a bad key in this same run's log. Derive the witness from the certificate and execution;
   do not leave the advertised protocol theorem conditional on this final trace implication.
3. Prove own-cell invariance for reconstructed pre-challenge states/guard outcomes. Preserve the
   all-prefix local bounds, including prefixes not reached by any chosen honest execution.
4. Let DA be the adversary's distinct key set, and Istop the rounds actually queried by verification.
   Prove the actual resource estimate

       E[charge(Jstop)]
         <= max_i epsilon_i * E[|DA|] + E[sum (i in Istop), epsilon_i]
         <= max_i epsilon_i * E[|DA|] + sum_i epsilon_i.

Returned failure retains previous costs. Cached/repeated calls may make the inequality strict.
A comparison with padded completion may erase irrelevant suffix effects only for the specified
acceptance observation; it must not identify post-rejection caches/logs or substitute padded costs.

Acceptance: a general exported theorem and a native Sumcheck corollary using it, with no new
admissions. Sumcheck's Unit witness remains ordinary soundness; it is not substantive extraction.
The generic theorem must retain non-Unit input witness types.

## MUST 2: supply the existing FS theorem's premise and prove native compilation

Reuse #848's single-salt construction, induced-adversary reduction, transcript reconstruction,
extractor transport and budget-family discipline where they apply. Generalize/port narrowly when
native semantics require it, preserving authorship and a declaration-by-declaration correspondence.

### A. Prove the common-fragment correspondence

Fix the alternating fixed-round fragment shared by legacy ProtocolSpec and native Interaction.
For this bridge, ambient source observations are absent or use an explicitly matched stateless
deterministic handler. Arbitrary mutable ambient effects are outside this common fragment.
Construct the public-message presentation, and prove transport of statement/proof/salt, transcript,
knowledge state, extractor, terminal seed and query resources. The native restoration presentation
currently uses `oracleWith` nodes; public message histories require an explicit bridge. A Unit
oracle interface is not a substitute for public visibility.

On the finite compatible fragment, prove the observation/extractor laws connecting lazy native
execution to the legacy eager-table game. Derive the legacy SR soundness/knowledge premise from
native local certificates, instead of accepting SR security as a new unexplained assumption.
Where rejection differs, compare the named accepted failure event, not the full final state.

### B. Obtain the native compiled theorem

Implement the native single-salt verifier with actual prefix-key generation, native checks and
stopping. Construct its induced restoration adversary. Prove exact native compiled/stopped-game
correspondence and charge transport from their program definitions.

Apply MUST 1 and the reused/generalized canonical FS-to-SR transport to obtain

    Pr[native FS accepts (x, salt, proof) and not Rin(x, Ext(x, salt, proof, H))]
      <= E[sum (distinct typed challenge keys in the actual joint run), epsilon(key)]
      <= max_i epsilon_i * E[|DA|] + sum_i epsilon_i.

Under an actual adversary query cap Q, derive `Q * max_i epsilon_i + sum_i epsilon_i`;
uniform errors yield `(Q + k) * epsilon`. Include the ordinary false-statement corollary.
Choose the extractor once before the budget index. Define its terminal seed and prove acceptance
validates that seed; preserve all access assumptions and source-observation interpretations.

Acceptance: both the exact finite-fragment connection to the existing FS result and the native
lazy/stopped theorem. A paper comparison, an assumed game equality, a theorem alias, or importing
#848 while leaving its SR premise unproved does not satisfy this target. A narrow attributable
port is acceptable only with the named correspondence and genuine native operational extension.

A compiled Sumcheck client must exercise the actual verifier and generic theorem; state retained
input-oracle access explicitly. No full legacy layer retirement is part of this run.

## SHOULD, in priority order

### S1: honest single-salt execution and completeness

Reuse the existing honest construction. Define its native counterpart with independent fresh salt
sampling and private prover randomness. For an honest prover without challenge-RO access, prove
accepted-output distribution correspondence with the interactive source and transfer completeness.
Preserve private continuations. Extra RO access requires a proved freshness/noninterference law.
This is new proof work: the open stack's basic/single-salt completeness remains deferred.

### S2: external encoded-query security

Generalize the typed-key theorem to a computable codec into D. Prove both
`decode(encode k) = some k` and `decode d = some k -> encode k = d`, hence injectivity.
Allow arbitrary off-image adversarial queries. Simulate them with lazily sampled, memoized private
coins, preserving repeated replies, adaptive choices and the full mapped cache. Prove actual
log/charge transport and the same security inequality, charging each distinct encoded key once.
No concrete byte format is required. A codec structure without its adversary reduction is incomplete.

## HOPE: connect native local certificates to conditional duplex security

On the explicitly matched finite fragment, instantiate the existing Section 6 theorem with the
SR premise supplied by MUST 2. State an attributable corollary of shape

    native local knowledge certificate + concrete KeyLemmaSecurityWitness
      => DSFS security with epsilon_SR + etaStarTotal.

Use the exact existing constants, codec-bias terms and query substitutions. Preserve its randomized,
two-log extractor interface and one-extractor-before-budgets quantifier order. The concrete witness
remains a named hypothesis. This would connect the two developments, not prove the missing Key Lemma.
Do not publish a vacuous wrapper whose new native SR premise was not actually discharged.

Online Merkle exchanges move out of this run's deliverables. Their replay reduction is worthwhile,
but starting it would compete with finishing the actual FS integration and completeness proofs.

## Still-open decisions and research boundaries

- Effectful rejection, variable-depth/dependent schedules, and challenge-distribution transport.
- Functional query solving/tail control versus full-message and tree extraction capabilities.
- General relation/output-oracle compilation and backend-specific guarantees.
- Extractor runtime, ancestor replay, and stricter deterministic/prover-trace-only access.
- General correlated auxiliary information, initial cached bad events, and multi-session salts.
- Concrete serialization/XOF suites, decoding bias, and protocol/session separation.
- Hash-chain FS and the concrete duplex hybrid/abort/Key Lemma proofs. Several old main-snapshot
  statement defects are repaired in #469; consult the overlap audit rather than treating those
  historical findings as the current PR status.
- Online Merkle checks, interleaved commitments, and their exact query accounting.

The textbook pipeline remains required coverage. Connecting the native theory to existing single-salt
FS is the selected next increment; it does not settle or replace the other compiler branches.

## Team, schedule and delivery

Root orchestrates, integrates, and strictly reviews. Two Sol High workers own distinct lanes;
one independent reviewer uses `review-lean-formalization`, including fresh blind read-back for new
main statements. Private worktrees/build outputs; serialized shared dependency writes; no fan-out.

- 0:00–0:30: refresh snapshots, audit exact public statements, freeze the common fragment,
  guard/seed/key interfaces, extractor access and the reusable legacy declarations.
- 0:30–3:15: worker A owns stopped restoration; worker B owns the legacy/native and FS transport
  bridges. Root handles integration, compatibility and the concrete client. Review incrementally.
- 3:15–4:15: complete MUST integration; use available capacity for S1, then S2, then HOPE.
- 4:07:30: 75% checkpoint with proved frontier, failed goals and any extension recommendation.
- 4:30: freeze new theorem families. Reserve the final hour for full validation, independent
  review, conflict resolution, pushes and handoff.
- 5:30: deadline. No automatic extension and no automatic claim of mathematical completion.

PR order: (1) stopped restoration theory; (2) native/legacy single-salt bridge and compiled security,
stacked only where required; (3) completeness or encoded-query security if independently complete.
A compatibility-only slice is separate only when independently useful. Prefer 500–1500 changed
lines per substantial PR; smaller complete results are fine. Preserve attribution when porting.
Do not fold the entire DSFS stack or a toolchain upgrade into an implementation PR.

On launch, work authorization covers local branches, commits, pushes, substantial PRs and necessary
updates to this run's owned PRs. No main merges, edits to other authors' PR branches, destructive
cleanup, infrastructure changes, or messages to others. Record latest fetched main and retained
integration/dependency heads; validate the actual selected versions, not an imagined newer API.

No new admissions, axioms, linter bypasses, weaker hidden quantifiers or duplicate-framework shortcuts.
Run repository-required validation and axiom checks for new proof claims; audit the complete
base-to-head diff and actual public statements before publication. Expected-cost/core statements
must remain independent of legacy admitted completeness and the unproved duplex witness.

If MUST fails, preserve the strongest checked result, exact blocker/counterexample, remaining
obligations and review evidence. Keep useful partial work clearly labeled. A padded bound or an
assumed semantic bridge is partial progress, not completed MUST. Do not substitute cleanup for the
technical target. At the deadline consolidate, push and hand off; report each MUST/SHOULD/HOPE honestly.
