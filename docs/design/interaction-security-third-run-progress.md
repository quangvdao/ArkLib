# Third interaction-security run: checked progress

Run: October 4, 2026, 05:07:49–10:37:49 UTC. Status: **MUST 1, MUST 2, SHOULD S1 and SHOULD S2 proved, reviewed and published**.
Final acceptance checkpoint: October 4, 2026, 09:32 UTC, before the 10:37:49 UTC deadline.
Both MUSTs and both SHOULDs met their completion conditions; the conditional duplex HOPE is unfinished.
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
  The port updates existing Ajtai binding API names for the pinned VCVio; no mathematical change.

- [#1276](https://github.com/Verified-zkEVM/ArkLib/pull/1276): canonical coin-bearing
  single-salt knowledge-security transport, stacked on #1275. Head `6b8a3d0dc`; 825 additions.
  Full validation: 926 modules, 18,067 declarations, no new taint. Its SR premise is explicit
  at this transport layer and is discharged on the selected native fragment in #1279.
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

- [#1280](https://github.com/Verified-zkEVM/ArkLib/pull/1280): salt-aware honest compilation,
  actual native interactive-source correspondence, and completeness transfer; 1,155 additions.
  Head `717eecf76`, stacked on #1277. Full isolated validation: 946 modules, 18,577 declarations,
  286 baseline sorry-tainted declarations, no new taint. Ordinary and code-only reviews approve
  the repaired salt-aware/native-source statement.
- [#1281](https://github.com/Verified-zkEVM/ArkLib/pull/1281): matched accepted-failure equality
  between canonical FS and actual native stopped verification; 697 additions, 2 deletions.
  Head `11bd25ec5`, stacked on #1279. Full isolated validation: 965 modules, 18,792 declarations,
  285 baseline sorry-tainted declarations, no new taint. The final ordinary and code-only reviews
  close the earlier event-connection fidelity gate.

- [#1282](https://github.com/Verified-zkEVM/ArkLib/pull/1282): arbitrary encoded-domain
  adversary simulation, including private memoized off-image answers, exact cache/log
  reconstruction, and distinct-key/weighted-charge transport; 810 additions.
  Head `232ba86e7`, stacked on #1274. Full isolated validation: 942 modules, 18,473 declarations,
  286 baseline sorry-tainted declarations, no new taint. Ordinary and code-only reviews approve
  this operational reduction. The dependent native coupling and final external security theorem
  are separate remaining obligations.

- [#1283](https://github.com/Verified-zkEVM/ArkLib/pull/1283): actual external encoded-domain
  stopped security, joint challenge/cache/log coupling, and exact weighted query accounting;
  1,453 additions and 1 deletion. Head `d8220cd98`, stacked on #1282.
  Full isolated validation: 950 modules, 18,554 declarations, 286 baseline taint, no new taint.
  Ordinary and independent code-only reviews cover the full probability/cost chain. Review found
  and the implementation repaired a missing external joint-charge-to-budget inequality.

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

**MUST 1, MUST 2, SHOULD S1 and SHOULD S2 are complete on their stated fragments.**
The final `fsNARGFailure_eq_actual_singleSaltAccepted` theorem identifies the actual canonical
noninteractive failure experiment with the actual native lazy/stopped accepted-failure event for
the same arbitrary private-coin prover and terminal seed. Its NARG specialization uses
statement-only guards, terminal acceptance, and observation; the SR bridge also permits checks
on the salted input. It compares accepted events, not post-rejection log/cache/cost equality.

S1 now allows `GlobalSalt → HonestProver`: the prover strategy is selected after the independent
salt draw. The source is actual `executeStrategies` on the guarded native public protocol with
a uniform verifier and preserved private continuations. The compiled target is the existing
actual logged `singleSaltAcceptedExecution`. Their projected optional accepted outputs are equal,
so any source completeness probability transfers exactly, without assuming probability one.

S2 now proves the actual external stopped accepted-failure event bound, including arbitrary
adaptive/private-coin/off-image queries and one shared external cache. The strict codec simulation
memoizes off-image answers privately. The challenge conversion preserves the joint value, ordered
log and complete cache distribution. Exact weighted-charge transport gives the full chain

    Pr[accepted and the named extracted witness is invalid]
      <= E[sum of encoded round-error weights over actual distinct joint keys]
      <= max(round errors) * E[distinct keys of the original external adversary]
          + sum(round errors).

Off-image keys have zero local-error weight; repeated keys are charged once. Failed selections
and rejection keep their executed costs. The resource bound is independent of the security
certificate. Terminal acceptance is the supplied relation `Rout` on the stopped path. External
key domains may be infinite; every native challenge type must have a supplied bijection with
one finite uniform common type. Concrete byte encodings, biased decoding and varying challenge
cardinalities remain outside this result. Public names use `challengeEquiv` and
`EncodedChallengeCoupling`, rather than the earlier internal fibre terminology.

HOPE remains unimplemented: the original conditional duplex stack needs its own API port and
sampler/auxiliary-oracle compatibility before the native certificate can supply its premise.
The concrete `KeyLemmaSecurityWitness` is still an explicit unproved boundary. No main branch
was merged or another author's branch edited.

## Review record

- [Stopped ordinary fidelity ledger](reviews/stopped-fidelity-third-run.md).
- [Revised code-only read-back](reviews/stopped-blind-third-run.md).
- [Canonical port ordinary review](reviews/canonical-fs-port-third-run.md).
- [Canonical code-only read-back](reviews/canonical-fs-blind-third-run.md).
- [Native FS ordinary review](reviews/native-fs-third-run.md).
- [Native FS code-only read-back](reviews/native-fs-blind-third-run.md).
- [Legacy correspondence code-only read-back](reviews/legacy-correspondence-blind-third-run.md).
- [Final legacy security code-only read-back](reviews/legacy-security-blind-third-run.md).
- [Legacy security ordinary review and resolved fidelity gate](reviews/legacy-security-third-run.md).
- [Accepted-event code-only read-back](reviews/accepted-event-blind-third-run.md).
- [Honest FS ordinary review and repairs](reviews/honest-fs-third-run.md).
- [Repaired honest FS code-only read-back](reviews/honest-fs-final-blind-third-run.md).
- [Encoded operational reduction ordinary review](reviews/encoded-operational-third-run.md).
- [Encoded operational reduction code-only read-back](reviews/encoded-operational-blind-third-run.md).
- [Common-challenge coupling and cost ordinary review](reviews/encoded-fibre-third-run.md).
- [Common-challenge coupling code-only read-back](reviews/encoded-fibre-blind-third-run.md).
- [Actual external event ordinary review](reviews/encoded-event-third-run.md).
- [Final encoded security ordinary review and repaired resource-chain gate](reviews/encoded-security-third-run.md).
- [Encoded security code-only read-back](reviews/encoded-security-blind-third-run.md).
- [Final resource-chain and renamed-API code-only read-back](reviews/encoded-resource-chain-blind-third-run.md).

Checks distinguish the exact published slice from the larger integration branch. All run builds
use Lean 4.34.0 and VCVio `6bf6c91b66dfa159342c355a4b81d65b55cb54a4`, with private dependency
snapshots and serialized writes. That VCVio revision is the run's chosen snapshot, not the current
ArkLib main dependency pin (`d7089e46`).

## Integration checkpoint

The isolated PR slices above have each passed full validation. Mathematical integration source
`3086698dc` contains all published results. Combined full validation passed: 983 modules,
19,448 declarations, 285 baseline sorry-tainted declarations, no new taint or nonstandard axioms.
The integration branch also retains the run contract, literature comparison, review evidence and
open questions. The latest observed main remains `7717f73cd09e5a6b8952ff00bdfccc158330bcac`;
no new main commits required reconciliation at the final source check.

## Main exported entry points

| Contract target | Checked declaration and owner |
| --- | --- |
| MUST 1: sharp actual stopped security | `randomizedStopped_badRelation_le_expectedFreshCharge` in [StateRestorationStopped](../../ArkLib/Interaction/Oracle/Security/StateRestorationStopped.lean) |
| MUST 1: actual adversary/verifier costs | `expectedStoppedFreshCharge_le_actualAdversary_and_sum` in [StateRestorationStoppedBudget](../../ArkLib/Interaction/Oracle/Security/StateRestorationStoppedBudget.lean) |
| MUST 2: native compiled security | `singleSalt_knowledge_soundness` in [SingleSaltSecurity](../../ArkLib/Interaction/Oracle/FiatShamir/SingleSaltSecurity.lean) |
| MUST 2: one canonical extractor before all query budgets | `singleSalt_knowledgeSoundness_of_nativeCertificate` in [LegacyCertificateSecurity](../../ArkLib/Interaction/Oracle/FiatShamir/LegacyCertificateSecurity.lean) |
| MUST 2: actual canonical/native event equality | `fsNARGFailure_eq_actual_singleSaltAccepted` in [LegacyStoppedConnection](../../ArkLib/Interaction/Oracle/FiatShamir/LegacyStoppedConnection.lean) |
| S1: actual interactive-source completeness | `honestSingleSaltAccepted_logged_eq_native` and `honestSingleSaltAccepted_native_completeness` in [HonestSingleSalt](../../ArkLib/Interaction/Oracle/FiatShamir/HonestSingleSalt.lean) |
| S2: actual external security and complete cost chain | `encodedExternalStopped_knowledge_soundness_sharp`, `encodedExternalStopped_expectedCharge_le_adversaryCount`, and `encodedExternalStopped_knowledge_soundness_adversaryCount` in [EncodedSecurityEvent](../../ArkLib/Interaction/Oracle/Security/EncodedSecurityEvent.lean) |

## Merge order and retained research boundaries

Complete the existing dependency chain through #1269 before integrating #1274. Then the three
lanes are:

1. #1274 -> #1277 -> #1280 (stopped security, native single-salt compilation, honest completeness).
2. #1275 -> #1276; together with #1277 these are the parents of #1278 -> #1279 -> #1281
   (attributable canonical transport, native/legacy bridge, and actual accepted-event connection).
3. #1274 -> #1282 -> #1283 (encoded-domain operational reduction and full security/cost chain).

#1278 currently targets `integration/fs-bridge-pr-base-20261004`, the explicit dependency join of
#1276 and #1277. Retarget it after those dependencies land; do not merge the join branch as an
independent mathematical contribution. The original #848 should import/rebase on the shared
canonical owner modules instead of merging duplicate declarations. Its author's branch is intact.

This run does not retire the legacy layer or complete the textbook pipeline. Effectful guards,
variable/dependent schedules, nonuniform challenge transport, general output-oracle realization,
extractor runtime/access restrictions, concrete serialization and domain separation, multi-session
auxiliary information, online Merkle protocols, and hash-chain/duplex Fiat–Shamir remain research
work. The conditional duplex port and its concrete Key Lemma obligations remain separate. The
[open questions](guarded-restoration-open-questions.md) and [FS overlap audit](fiat-shamir-open-pr-overlap.md)
retain these boundaries rather than choosing new definitions for them implicitly.

## Final checks and publication status

At the final acceptance checkpoint, all ten PRs (#1274–#1283) were open and mergeable against
their current bases. Every triggered check passed; #1275's docs publication was intentionally
skipped. #1276 triggered only the summary workflow, so that is not evidence of a GitHub proof
build for its slice; its isolated full local validation and axiom regression passed separately.
The final #1283 interaction check passed at 09:31:27 UTC. Every published slice received full
local validation, and the complete mathematical integration passed the 983-module check above.

The final published encoded files match the reviewed integration source byte-for-byte. Main
was fetched again at 09:28 UTC and remained at the recorded revision. All run changes and review
notes are saved on `integration/interaction-third-run-20261004` in the quangvdao/ArkLib fork.
No PR was merged, no main branch was modified, and no original FS author's branch was edited.
