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

## Verified frontier and remaining obligations

The stopped theorem derives a bad queried key from an all-prefix local certificate. Its endpoint
uses an explicit terminal seed and the named backward extractor. Independent review caught an
unnecessary terminal-witness equivalence: the implementation now requires only a forward seed map
and acceptance implying terminal validity. The input witness remains generic. The total seed map
on rejected paths remains a known restriction, to revisit if a concrete client needs partial seeds.

The native public executor now has a checked equation to guarded completion under arbitrary
response-type-preserving key embeddings (`656806253`, integrated as `159e4077e`). The final
specialization to the restoration program is still in progress. Root's native single-salt game,
actual terminal check, log/cache preservation and conditional security assembly have targeted
checks; the final public theorem must discharge the execution correspondence rather than expose it
as a hypothesis. Sumcheck's concrete terminal check is tied to its returned native closed claim.

The canonical coin-bearing knowledge games and single-salt reduction have passed isolated full
validation (926 modules, 18,067 declarations) on `6b8a3d0dc`; their independent code-only read-back
and PR publication remain pending. This theorem is conditional on legacy SR security. Supplying
that premise from native certificates is still outstanding and is not implied by the port.

Legacy transcript inverse, message-prefix, query-key and dependent response transport are being
proved in separate modules. The actual legacy prover/program/table correspondence and resulting
`coinKSExperimentProb` bound remain required. The legacy eager game completes a full transcript;
its proof uses the full restoration experiment, not a false equality with stopped final caches.

MUST 1 and MUST 2 remain **incomplete** until their native endpoints and legacy-game bridge are
proved, integrated and reviewed. SHOULD completeness/encoded queries and HOPE conditional duplex
have not been claimed. No main branch was merged or another author's branch edited.

## Review record

- [Stopped ordinary fidelity ledger](reviews/stopped-fidelity-third-run.md).
- [Revised code-only read-back](reviews/stopped-blind-third-run.md).
- [Canonical port ordinary review](reviews/canonical-fs-port-third-run.md).

Checks distinguish the exact published slice from the larger integration branch. All run builds
use Lean 4.34.0 and VCVio `6bf6c91b66dfa159342c355a4b81d65b55cb54a4`, with private dependency
snapshots and serialized writes. That VCVio revision is the run's chosen snapshot, not the current
ArkLib main dependency pin (`d7089e46`).
