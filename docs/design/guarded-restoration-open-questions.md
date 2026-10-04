# Early rejection and state restoration: the next design questions

Status: research note from the second interaction-security run, October 3, 2026.
These are candidate obligations and unresolved choices, not an implemented generic adapter.
The audience is a cryptographer deciding the next formalization contract.

The Sumcheck application now provides a concrete route from fixed-round restoration to
native early rejection. A general adapter needs to say which execution's state and costs
it preserves. Equality of accepted outputs alone does not settle that question.

## What the current proofs establish

The restoration owner uses a fixed list of `Round`s. Each round fixes its message type,
oracle interface, and finite nonempty uniformly sampled challenge type. Restoration keys
contain the input, message prefix, and salt prefix. They omit earlier challenges; the
extractor reconstructs those challenges from the same table at strict ancestor keys.
The `keyExtractor_update` theorem proves that changing the target cell leaves its
pre-challenge extractor unchanged.

The Sumcheck certificate retains a proposition saying that all preceding sum checks passed.
Its state predicate conjoins this proposition with truth of the current polynomial claim.
A failed check makes every later predicate false, even though the fixed-round path continues.
The local degree-over-field-size bound is proved at every authored prefix, including these
invalid prefixes. The witness type is `Unit`, so this is ordinary soundness.

`paddedStatement` evaluates the selected full transcript and returns `none` at its first
failed sum check. `replay_execute_eq` identifies its output with the actual aborting native
Sumcheck execution under the selected messages and completed field coins. On success, the
closed output retains the original polynomial-oracle behavior. This theorem compares
returned outputs; it does not identify final caches or logs after rejected executions.

The randomized restoration experiment completes the selected full transcript in the same
random oracle as the adversary. Its security theorem charges that joint execution. The
Sumcheck application obtains its native output by replaying the completed path. It does
not already describe an arbitrary online prover supplying its next message after each
verifier challenge.

Source anchors:

- [Fixed-round presentation and own-cell invariance](../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean)
- [Actual randomized execution and costs](../../ArkLib/Interaction/Oracle/Security/StateRestorationRandomized.lean)
- [Sumcheck certificate and all-prefix local bounds](../../ArkLib/ProofSystem/Sumcheck/Interaction/StateRestorationCertificate.lean)
- [Padded evaluation and native replay equality](../../ArkLib/ProofSystem/Sumcheck/Interaction/StateRestorationEvaluation.lean)
- [Sumcheck restoration probability bound](../../ArkLib/ProofSystem/Sumcheck/Interaction/StateRestorationSoundness.lean)

## A narrow reusable adapter worth investigating

One possible next theorem family keeps the existing fixed message and challenge alphabets.
Add an explicit rejection test before a round's challenge, and retain a flag recording
whether rejection has occurred. This is a proposed restricted fragment, not the selected
interface for every future protocol.

The obligations would be:

1. **Prefix agreement.** The padded and native executions perform the same effects until
   the first rejection, using the same replies and cache. State exactly which effects
   compute the rejection test and which public branch announces rejection.
2. **Accepted output correspondence.** On a surviving path, the native terminal output,
   closed oracle behavior, and any terminal witness interface agree with the padded ones.
   On a rejected path, native acceptance is false.
3. **Persistent rejection.** The padded certificate's predicate remains false after
   rejection. This removes false-to-true transitions in the padded suffix. For knowledge
   soundness, the witness carriers and backward maps still need actual definitions and
   preservation proofs; a Boolean flag alone does not supply them.
4. **All-prefix local bounds.** Prove the local challenge bound on every authored prefix
   of the padded presentation, not only prefixes reached by a particular honest execution.
5. **Query accounting.** Separate the common prefix, native work, and padding work. Prove
   the bound for the chosen operational game, with the cost of every executed query.
6. **Own-cell invariance.** Reconstructing a target key's pre-challenge state and rejection
   status must not inspect that key's reply. A test that reads the target cell before
   declaring it a challenge breaks the existing causality proof obligation.

The current Sumcheck proofs establish output correspondence, persistent false certificate
states after rejection, and all-prefix local bounds. The randomized owner supplies the
joint execution's query accounting and own-cell invariance. The Sumcheck output replay
theorem does not separately establish native/padded prefix effect agreement. These results
are evidence that this fragment is useful, not a proof that every guard or oracle interface
can be handled by the same adapter.

## Decisions that remain open

| Question | Plausible choices | Why it changes the theorem |
| --- | --- | --- |
| What is the primary security experiment? | Complete the selected transcript and replay native verification; or stop actual completion at rejection. | Rejected executions can have different random-oracle logs and caches. An expected-cost statement must name the execution being charged. |
| What does the correspondence preserve? | Acceptance/output probabilities; common-prefix state; or a specified continuation interface. | A theorem about returned outputs does not justify resuming a later phase from an independently reconstructed cache. |
| Which rejection tests are supported? | Pure tests on the reconstructed prefix; or tests with explicit oracle effects. | Effectful tests need handlers, resource bounds, and proof that target-cell resampling does not change the pre-challenge test. |
| How are rejected paths extended? | An already supplied full transcript; explicit default messages; or a separately proved extension procedure. | `Round.Message` is finite but is not assumed inhabited. A generic default message is unavailable in the existing interface. |
| Which challenge distributions are supported? | Fixed finite uniform carriers; or a proved distribution transport per branch. | Uniform sampling of `Option F` is not the native law that rejects deterministically or samples a uniform element of `F`. |
| Which knowledge predicates survive the adapter? | A false predicate after rejection on specified carriers; or a more structured terminal witness interface. | Ordinary truth with a `Unit` witness does not settle reconstruction of substantive witnesses. |
| What counts as an implementation cost? | Current semantic table reconstruction; or an explicit machine that queries strict ancestors. | The present theorem does not provide a PPT extractor or automatically charge executable ancestor replay. |

These questions should stay separate. Choosing a restricted pure-guard fragment does not
commit the library to that fragment as the universal protocol representation.

## Candidate quantitative statements, not yet proved generically

For a chosen padded execution `J_pad`, the existing restoration theorem already suggests
the target shape

    Pr[native bad accepted output under the proved correspondence]
      <= E[sum of round errors over distinct keys queried by J_pad].

If native completion stops early, call the corresponding execution `J_stop`. Replacing
the right-hand side by its `J_stop` counterpart requires an additional argument. Erasing
post-rejection work preserves the acceptance observation when the relevant suffix is
lossless and irrelevant to that observation. It does not preserve the final cache, and
it does not by itself give equality of the two query charges.

One possible sufficient route is to prove a pointwise coupling bound

    charge(J_pad) <= charge(J_stop) + charge(padding suffix),

then bound the padding suffix explicitly. Another route might prove the probability bound
directly for stopped completion. Which gives the useful theorem depends on the intended
consumer; neither route is adopted by this note.

Likewise, a later phase can use a fixed initial cache only under the actual interpreter's
fresh sampling semantics and the new-key trace and own-cell hypotheses. A fixed-cache
theorem cannot silently discharge a conditioning argument for an adaptively produced
cache, or account for a bad answer already present there. Those application obligations
remain separate from the guarded adapter.

## Suggested next contract boundary

Before implementation, choose one real consumer beyond the existing Sumcheck replay and
write its literal native and restoration games. Freeze the required observation, phase
handoff, rejection timing, and cost expression. Then ask for a generic theorem covering
that consumer and Sumcheck with the same owner interface.

Keep arbitrary dependent challenge carriers, online message generation, general oracle
lowering, machine/PPT extraction, and substantive witness applications as separately
specified extensions. The current results provide useful components for these questions;
they do not select their final interfaces.

Related records: [second-run contract](interaction-security-next-night-contract.md),
[second-run results](interaction-security-second-night-results.md), and
[literature map](../kb/audits/interaction-literature-map.md).
