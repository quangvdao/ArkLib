# Further SHOULD 2: causal adaptive terminal query programs

The principal Merkle transfer and its clean ideal-game repair have passed independent review.
This lane starts after those semantic gates, while root validates the clean publication base. This is the already-authorized Further SHOULD 2 of the second-night contract,
not a move to online interleaved openings or a general dependent-protocol compiler.

## Proposed precise increment

Replace the fixed list of commitment slots/selectors at the terminal batch with a finite
causal query program. A program either returns an acceptance bit, or requests a batch selector
at a specified public commitment slot/configuration and continues as a function of that
request's ordered answers. Later requests may depend on earlier answers. Every requested
slot refers to a completed commitment checkpoint; there are no new commitments in this phase.
Use plain names such as `QueryProgram`, `checkTranscript`, `idealDecision`, and `realAcceptance`.

The malicious terminal strategy supplies the complete opening transcript. The real native
verifier still verifies EVERY submitted opening unconditionally before final acceptance,
then checks that the ordered request/answer sequence is exactly a path of the causal program,
with no missing or extra entries, and uses its final decision. Public root lookup and slot,
configuration, selector, and answer-length checks must be explicit. No private checkpoint/log
is exposed to the verifier. This is terminal-batch verification of a causal decision program;
it is not an online protocol requesting new openings between verifier moves.

The ideal decision evaluates the same causal program by looking up the requested leaves in
the immutable checkpoint-extracted vectors, with the existing total fallback. Its next request
must depend on these extracted answers, not on the malicious opening list. It should not need
honest opening-verification queries. If the ideal runner retains an irrelevant malicious
terminal phase for coupling, prove its Boolean marginal can erase that phase when appropriate;
never claim equality of final caches/logs after erasing queries.

Prove by induction on the program/transcript that, on an accepting well-formed real transcript
with no checkpoint extraction disagreement, real answers and ideal answers determine the same
next request and final acceptance. This path-agreement theorem is a central deliverable; it
must not be an assumption or a certificate supplied by callers.

Prove actual native execution and owner-game coupling for this new verifier, reusing existing
source handlers and all-opening verification where possible. Then prove

    Pr[real accepts] <= Pr[ideal program accepts] +
      multiCheckpointROMErrorNumerator(N,C,H,Q) / card(Y),

with the SAME owning VCVio resource assumptions: total adversarial commitment/opening prefix
queries <= Q, honest opening verification <= H, per-checkpoint node budget P, rounds*P<=N,
and rounds<=C. Do not assume the final desired probability transfer or native execution bridge.
Expose eta transfer for an independently bounded ideal program. Fixed query plans should have
a clearly identified specialization if easy; do not refactor existing accepted APIs merely to
force the new representation everywhere.

## Acceptance / stop conditions

- General finite causal programs; examples alone do not count.
- Prove path agreement and actual native/owner/clean-ideal marginals, then exact probability bound.
- No new admissions, lint exemptions, weakened resource assumptions, or hidden promise predicates.
- One coherent PR, aim 500-1500 changed lines; preserve accepted baseline PR unchanged when possible.
- New main statement gets a fresh blind readback only AFTER it is frozen, then contract comparison.
- Target build, full validation/axiom audit, exact dependency pin and independent review.
- If a reusable native verifier parameterization is needed, explain its semantic boundary before
  implementing it. If the task reveals an unresolved compiler design choice, preserve the
  strongest checked theorem and report the unresolved choice instead of fixing it by fiat.

## Statement freeze for the implementation lane

`QueryProgram config rounds Y depth` has two constructors: `done accepted` at any depth,
and `request site next` at depth `d+1`, where `next : List Y → QueryProgram config rounds Y d`.
The depth is a uniform upper bound and early termination is allowed. Responses are selected
leaf values in canonical order; the real transcript checker validates their exact shape
before choosing the continuation. A fixed public program suffices for this milestone.

`checkTranscript` consumes exactly one opening per request and requires an empty remaining
list at `done`. It checks the public slot, configuration, selectors, and answer length.
`idealDecision` runs the same program using only public roots and commitment-time extracted
values. The actual verifier checks every supplied Merkle proof before calling the transcript
checker. The principal new mathematical obligation is recursive path agreement: on an
accepting transcript outside checkpoint disagreement, each real answer equals the corresponding
ideal answer, so the next request and final decision agree.

Implementation ownership is the new `MerkleAdaptiveTerminal.lean` module and its generated
root import. Existing `MerkleTerminalBatch` interfaces are preserved. Reuse its native protocol,
malicious prover, owner adversary image, coupling, and clean suffix-erasure laws; prove the new
native verifier's source equality. The probability headline uses the unchanged owning VCVio
numerator and resource premises. Erasing the malicious terminal phase from the ideal Boolean
marginal is permitted because this new ideal decision does not inspect that phase's output;
this does not assert equality of final caches or logs.
