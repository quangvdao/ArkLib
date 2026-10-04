# Third interaction-security run: checked progress

Run: October 4, 2026, 05:07:49–10:37:49 UTC. Status: **in progress**.
The [authorized contract](interaction-security-third-run-contract.md) remains the acceptance target.
A proved support lemma or conditional assembly is not completion of its principal target.

## Published slices

- [#1274](https://github.com/Verified-zkEVM/ArkLib/pull/1274): stopped-restoration knowledge security,
  distinct-adversary/actual-verifier cost bounds, query-cap corollary, and Sumcheck specialization.
  Head `ac424bacac5314cf802158c1a281c486720debcf`, base #1269 at
  `afe42b588a9ba302f5cbcaa35a7027cd6c20d7b7`; 1303 additions, 3 deletions.
  Full validation with axiom regression passed: 938 modules, 18,402 declarations, no new taint.
- [#1275](https://github.com/Verified-zkEVM/ArkLib/pull/1275): attributable port of #848's
  transcript reconstruction, query logging and routing lemmas. Head `c8489f70a`, base main at
  `7717f73cd09e5a6b8952ff00bdfccc158330bcac`; 779 additions, 18 deletions.
  Full validation with axiom regression passed: 924 modules, 18,033 declarations, no new taint.
  The VCVio pin needs the existing Ajtai binding API names updated; no mathematical change.

- [#1276](https://github.com/Verified-zkEVM/ArkLib/pull/1276): canonical coin-bearing
  single-salt knowledge-security transport, stacked on #1275. Head `6b8a3d0dc`; 825 additions.
  Full validation: 926 modules, 18,067 declarations, no new taint. Its SR premise remains explicit.
- [#1277](https://github.com/Verified-zkEVM/ArkLib/pull/1277): actual native single-salt
  knowledge security and compiled Sumcheck soundness, stacked on #1274. Head `2433b391b`;
  1,310 additions across nine files, including 97 executor equations reused from #1261.
  Full isolated validation: 945 modules, 18,510 declarations, no new taint.
  Ordinary review approved; independent code-only read-back recorded the exact statement.

- [#1278](https://github.com/Verified-zkEVM/ArkLib/pull/1278): transcript/key/table
  correspondence and finite lazy/eager restoration, 1,105 additions. Head `bd10a2d47`,
  based on the explicit dependency join of #1276 and #1277. Full isolated validation:
  955 modules, 18,690 declarations, no new taint.
- [#1279](https://github.com/Verified-zkEVM/ArkLib/pull/1279): actual legacy execution,
  game unrolling, query accounting, canonical SR bound, and single-salt knowledge-security
  family from native certificates. Head `e87bc6f75`, stacked on #1278; 1,453 additions.
  Full isolated validation: 964 modules, 18,761 declarations, no new taint. Ordinary and
  code-only reviews agree on the stated finite/empty-source/pure-observer fragment.

## Verified frontier and remaining obligations

The stopped theorem derives a bad queried key from an all-prefix local certificate. Its endpoint
uses an explicit terminal seed and the named backward extractor. Independent review caught an
unnecessary terminal-witness equivalence: the implementation now requires only a forward seed map
and acceptance implying terminal validity. The input witness remains generic. The total seed map
on rejected paths remains a known restriction, to revisit if a concrete client needs partial seeds.

The native public executor is now proved equal to stopped completion as an open oracle
program. `singleSalt_knowledge_soundness` derives accepted extraction failure bounds from native
certificates, with no execution correspondence premise. The final acceptance filter preserves
ordered logs, caches, and charges. Expected adversary/verifier costs and actual query-cap bounds
are proved. Compiled Sumcheck exercises the actual terminal claim check and exports the sharp,
expected-round, and `(Q + n) * fieldError` soundness bounds. Its source realization remains
explicit and its Unit witness expresses ordinary soundness.

The finite legacy bridge now proves the actual arbitrary-prover execution and canonical
`coinKSExperimentProb` bound. Typed message/transcript/key/table equivalences preserve the
completed path, and a fixed-table cache projection preserves the value experiment with private
coins. The legacy initializer is explicitly the pushforward of the uniform native table sampler.
The proof compares accepted failure events; it does not identify stopped and full-completion caches.

`singleSalt_knowledgeSoundness_of_nativeCertificate` now derives the canonical single-salt
knowledge theorem from native preserving/local-bound and input/output laws. It chooses one
backward/delegating extractor before all structural hash-query budgets and yields
`Q * max(round errors) + sum(round errors)`. No supplied state-restoration security hypothesis
or assumed game equality remains. The common fragment uses finite statements, a finite global
salt carried in the statement, empty ambient source, and a pure path observer. It retains a total
terminal seed and the canonical two-log extractor interface; it does not establish extraction time
or a deterministic prover-trace-only interface.

**MUST 1 is complete. MUST 2 now has both native and canonical security theorems; its final
matched-check accepted-event bridge remains in progress.** Independent review approved both
theorems as stated but requires this explicit connection before closing the whole target. The
canonical verifier completes the full transcript; the native verifier stops on failed guards.
The pending proof compares accepted failure events under matched guards and terminal checks,
not post-rejection cache/log equality. Root integration `c8d7d6884` passes
full validation: 969 modules, 19,198 declarations, 285 baseline sorry-tainted declarations,
no new taint or nonstandard axioms. Independent code-only read-back records the actual final
quantifier order and experiment.

SHOULD S1 has a fully validated honest accepted-output equality and completeness transfer for
salt-oblivious strategies. Independent review requested a salt-aware strategy interface and an
explicit connection from the recursive interactive interpreter to native `executeStrategies`;
these repairs are in progress before S1 is counted complete. S2 has a checked operational reduction for arbitrary adaptive encoded-domain clients: image
queries use the native oracle and off-image replies are privately sampled and memoized. Its
returned value, full external query log, and reconstructed external cache match the actual external
random oracle. Native log/charge transport and the certificate security assembly remain in progress.
This is a preserved partial result, not completion of S2.
HOPE remains unimplemented. No main branch was merged or another author's branch edited.

## Review record

- [Stopped ordinary fidelity ledger](reviews/stopped-fidelity-third-run.md).
- [Revised code-only read-back](reviews/stopped-blind-third-run.md).
- [Canonical port ordinary review](reviews/canonical-fs-port-third-run.md).
- [Canonical code-only read-back](reviews/canonical-fs-blind-third-run.md).
- [Native FS ordinary review](reviews/native-fs-third-run.md).
- [Native FS code-only read-back](reviews/native-fs-blind-third-run.md).
- [Legacy correspondence code-only read-back](reviews/legacy-correspondence-blind-third-run.md).
- [Final legacy security code-only read-back](reviews/legacy-security-blind-third-run.md).
- [Legacy security ordinary review and remaining fidelity gate](reviews/legacy-security-third-run.md).

Checks distinguish the exact published slice from the larger integration branch. All run builds
use Lean 4.34.0 and VCVio `6bf6c91b66dfa159342c355a4b81d65b55cb54a4`, with private dependency
snapshots and serialized writes. That VCVio revision is the run's chosen snapshot, not the current
ArkLib main dependency pin (`d7089e46`).

## Latest integration checkpoint

At `a68580672`, the integration includes the checked S2 operational core as an unpublished
checkpoint. Full validation passes: 972 modules, 19,299 declarations, 285 baseline sorry-tainted
declarations, and no new taint or nonstandard axioms. S1's salt-aware/native-source repair and
the final stopped/eager noninteractive event corollary are still being developed in isolated
worktrees. Their earlier restricted results are not substituted for the requested full claims.
