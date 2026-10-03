# Second interaction-security run: evidence and progress

Status: final integration checks underway. Both MUSTs and every SHOULD are proved,
independently reviewed, fully validated in their publication slices, and preserved in substantial
PRs. The HOPE design note records the unresolved guarded-adapter choices. The [authorized contract](interaction-security-next-night-contract.md)
controls scope. Historical checkpoints below are retained as an evidence trail.

Current accepted PRs: VCVio [#824](https://github.com/Verified-zkEVM/VCVio/pull/824),
[#825](https://github.com/Verified-zkEVM/VCVio/pull/825), and
[#826](https://github.com/Verified-zkEVM/VCVio/pull/826); ArkLib
[#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267),
[#1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268),
[#1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269), and
[#1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270), and
[#1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271).
No PR has been merged by this run.

## Publication and dependency order

| PR | Main contribution | Review head | Base | GitHub changed lines |
| --- | --- | --- | --- | ---: |
| VCVio #824 | Actual expected distinct-query bound with interleaved private randomness | `e417e35a` | main | 1,355 |
| VCVio #825 | Native-measure Merkle owner bound, unchanged constants | `7ec28e1d` | main | 166 |
| VCVio #826 | Arbitrary-domain new-key bound from a fixed initial cache | `c50275fb` | #824 | 430 |
| ArkLib #1267 | Actual cached randomized restoration games and query accounting | `0815f8c74` | prior #1264 | 1,193 |
| ArkLib #1268 | Scalar and closed-output expected knowledge-security bounds | `8e290aa71` | #1267 | 817 |
| ArkLib #1269 | Sumcheck ordinary restoration soundness and native output replay | `afe42b588` | #1268 | 669 |
| ArkLib #1270 | Native terminal-batch Merkle real-to-ideal transfer | `f6d8d94cf` | main | 1,447 |
| ArkLib #1271 | Causal terminal query programs and adaptive path agreement | `e9ee95267` | #1270 | 790 |

The two smaller VCVio PRs are complete, independently useful units. The initial-cache proof
generalizes existing code, so its net addition is smaller than a duplicated probability proof.
The native-measure owner migration is the prerequisite for the two Merkle consumers.
VCVio #824 and #825 can be reviewed independently; #826 follows #824. The restoration chain
is #1264 → #1267 → #1268 → #1269. The Merkle chain is #1270 → #1271 and uses VCVio #825.
Exact downstream pins are retained until a separately validated move to merged upstream.

## Run and ownership

- Start: October 3, 2026, 17:34:15 UTC.
- Six-hour checkpoint: 23:34:15 UTC.
- Deadline: October 4, 01:34:15 UTC (October 3, 21:34:15 America/New_York).
- Root orchestrates and integrates. Workers use gpt-6-sol at high reasoning effort.
- Integration: `integration/interaction-second-night-20261003`, initially ArkLib main
  `ace55c3e29da1fc55a321378ada55ea4f7ed8790` plus prior reviewed integration
  `b2ec8214150121c00f2d4ec468f72f1be34d8f22`.
- VCVio worker: `feat/expected-fresh-query`, worktree `VCVio-expected-query`.
- Native restoration worker: `feat/randomized-state-restoration`, worktree
  `ArkLib-randomized-restoration`.
- Merkle worker: `feat/native-merkle-terminal-batch`, worktree `ArkLib-merkle-terminal`.
- Builds serialize shared dependency writes; each project has private build outputs.
- No main merges are authorized. Substantial PRs and checkpoint pushes are authorized.

## Validated merged-upstream baseline

VCVio PR 823 merged at 17:31:21 UTC as
`d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0`. Current execution baseline is
`bc3433e3c94a85ff5b70a00109cf74394ad5c401`, also containing PR 820.
The ArkLib migration changes its exact VCVio pin and four uses of renamed binding-security
identifiers in the Ajtai proof. The binding experiment and mathematical proof are unchanged.

- Integration migration commit: `31ca1b19d`.
- Worker migration cherry-pick: `324fd0bf3`.
- Contract commit: `a9f7757aa`; pushed integration head verified remotely.
- Full `./scripts/validate.sh --axioms`: passed in 159.8 seconds after the name migration
  and line-length repairs. Production build, compile-time clients, runtime checks, source
  policy, documentation checks, and axiom regression all passed.
- Axiom audit: 18,341 declarations, 933 modules, 286 existing sorry-tainted declarations,
  zero nonstandard-axiom-tainted declarations; no regression.
- Independent ordinary review found no issue in the dependency/name migration.
- Dependency revisions and origin URLs match the manifest. The only untracked entry in
  the new VCVio cache checkout is the cache manager's `.lean-deps-immutable` metadata.

## Early statement review

The initial independent reviewer checked the proposed interpreter and native definitions
before being reassigned to the Merkle workstream. This is an ordinary review, not a blind
read-back, and is not a final verdict on the eventual theorems. It requires actual cached
expectation, returned failure with retained log/cache, independent uncached private draws,
finite-support treatment of infinite key domains, and exact native phase handoff.
That worker cannot independently approve its own later Merkle implementation.

The Merkle design uses one native public root emission per sequential commitment. Each
checkpoint is recorded at that step. A proposed grouping of all roots into one public move
was rejected pending a stronger causal refinement proof; final transcript equality alone
would not certify commitment-time extraction.

## First-hour checked progress

These are checked supporting results, not completion of the main security targets.

- VCVio `97530943`: the joint cached interpreter returns output, ordered hash-query log,
  and cache; private sampling uses the separate uncached summand.
- VCVio `8fc8bae0`: public finite-query restriction APIs. Full
  `./scripts/validate.sh --axioms --test` passed (340.4 seconds; 22,079 declarations,
  781 modules, 14 existing sorry-tainted declarations, zero nonstandard axioms).
  Independent ordinary review found no P1/P2 issue.
- VCVio `0327fa34`: the finite-domain joint lazy/eager measure equality, including
  interleaved private samples and arbitrary initial caches; also the deterministic finite
  expected-charge theorem. Target module checked; configured lint cleanup remains in progress.
- VCVio `8dd83a7d`: restriction to finitely many possible hash keys preserves the complete
  mixed computation, with arbitrary initial cache and all outside cache entries retained.
  Ordered logs preserve order and multiplicity; distinct-query charge is unchanged.
  Target module checked without its own warnings; independent ordinary review found no P1/P2.
- VCVio `41111c50`: expected actual distinct-query charge is invariant under that restriction.
- VCVio `ef4ebfea`: every supported actual cached result is supported by some fixed-table run,
  with identical output, ordered log, and final cache, even for an infinite key domain.
  The latter two target modules checked; independent final review is still required.
- ArkLib `b19906256`: randomized native scalar/closed execution structure and deterministic
  charge decomposition. Full validation with axiom audit passed (934 modules, unchanged
  286 sorry-tainted declarations, zero nonstandard axioms). The expected probability theorem
  is not part of that checkpoint.

The restoration worker has additionally checked same-cache phase handoff, equality of source
and interpreted hash logs, and support-level bad-output and charge implications in scratch
against the new VCVio modules. These are exploratory checks until committed against a clean
pinned dependency and validated again. The Merkle worker has checked actual native/source
execution and public/private verification correspondence; event and probability transfer
remain in progress.

## First-hour proof frontier (historical)

The interleaved own-cell bad-query probability bound is the central remaining VCVio step.
Its finite-domain expected bound then transfers through the checked finite-support bridge.
Native expected knowledge security and the real-to-ideal Merkle bound remain unfinished.
Final acceptance requires revision-specific validation, independent statement read-back,
contract comparison, and coherent PR assembly. No headline theorem has been marked complete.


## Second-hour checkpoint (2026-10-03, approximately 19:20 UTC)

VCVio's required general expected-charge theorem is now kernel-checked and fully validated
at `e0ff3044330b8fc9bf8afc855a0ebb590a6ee0a9`, pushed on `feat/expected-fresh-query`.
`./scripts/validate.sh --axioms --test` passed in 264.8 seconds: 22,138 declarations,
785 modules, 14 existing sorry-tainted declarations, zero nonstandard-axiom taint,
and no new taint. The generated umbrella includes all new modules. Its base-to-head
diff is 1,326 insertions and 25 deletions across six files.

The public arbitrary-domain theorem is
`OracleComp.prEvent_randomOracle_le_expectedFreshQueryCharge`. Its finite-domain core is
`OracleComp.prEvent_interleavedFreshBad_le_expectedCharge`. Private uniform draws are fresh,
hash replies are cached, and the charge uses the actual distinct queried keys. The proof
preserves the joint output, ordered query log, and cache through finite-support restriction.
A fresh reviewer recorded the statement independently before receiving the contract;
final contract comparison and review are underway.

ArkLib's randomized scalar and closed-output expected knowledge bounds and actual-support
query-cap corollaries have passed exploratory checks. Their canonical validation is in
progress against the exact new VCVio pin. They are not yet recorded as accepted deliverables.

The native Merkle terminal-batch proof has passed targeted checks. To support its native
probability statement without introducing a new retired-probability dependency, VCVio's
existing owning ROM theorem was migrated directly to native measure semantics at
`7ec28e1df3b660e65943d8a10cc1dfcf76239472`. Its exact numerical bound is unchanged,
legacy callers are bridged explicitly, and no lint exemption was added. Full validation
with axioms and lint passed. The ArkLib client is being checked against this exact revision.

The Sumcheck restoration certificate is saved at `fd24cd3b7` on
`feat/sumcheck-state-restoration`. Its preservation and local degree/cardinality error
proofs use only standard Lean axioms. The terminal certificate relation now agrees with
the checked fixed-round evaluation in an exploratory proof. The actual aborting native
execution correspondence and final restoration application remain unfinished. The Unit
witness encodes ordinary truth and does not claim substantive witness extraction.


### First accepted PR

[VCVio #824](https://github.com/Verified-zkEVM/VCVio/pull/824) contains the complete general
expected-charge theorem (1,351 changed lines). Independent blind readback and contract/proof
review recommend approve with no blocking findings; the durable evidence is
[expected-query-second-night.md](reviews/expected-query-second-night.md). Its base was rechecked
as current VCVio main `bc3433e3c94a85ff5b70a00109cf74394ad5c401` immediately before opening.


### Required restoration result and review

Both randomized restoration modules are frozen at `578a55f098c7075d446f77d476e788370a84ee2e`.
Full `./scripts/validate.sh --axioms` passed in 130.1 seconds: 18,428 declarations across
935 modules, unchanged 286 sorry-tainted declarations, zero nonstandard-axiom taint.
The new source has no warnings. A fresh blind readback followed by MUST 2 comparison
approved the two slices and their stack with no blocking findings; see
[randomized-restoration-second-night.md](reviews/randomized-restoration-second-night.md).
The integration branch now contains the full result. Publication slices have been assembled
on the existing nonuniform-restoration PR and are undergoing validation on those exact bases.

[VCVio #825](https://github.com/Verified-zkEVM/VCVio/pull/825) contains the native-probability
migration required by the Merkle application. Its independent review is saved in
[merkle-native-measure-second-night.md](reviews/merkle-native-measure-second-night.md).

The Merkle client's full validation passed, but independent review found a P2 gap: the
ideal experiment was only a projection after honest opening verification. A separately
bounded verification-free ideal experiment needs an explicit marginal equality. That repair
is underway; the original review is retained in
[merkle-terminal-second-night.md](reviews/merkle-terminal-second-night.md). The principal
SHOULD is therefore not accepted yet.

The Sumcheck native replay correspondence is checked at `f9719a0d0`: failed sum checks abort,
while successful outputs retain exactly the original oracle behavior under the same field
coins. The terminal truth equivalence and replay theorem use only standard Lean axioms.
The final ordinary restoration bound is being implemented using the reviewed general theory.


### Publication slices and CI follow-up (approximately 19:40 UTC)

- [ArkLib #1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267): randomized games and
  actual cached query accounting, stacked on #1264. Publication head `bc17d91d9`, 1,193 changed
  lines; full validation with axioms passed (18,260 declarations, 931 modules, unchanged debt).
- [ArkLib #1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268): shared scalar and closed-output
  knowledge bounds, stacked on #1267. Publication head `89793deaa`, 817 added lines; full
  validation with axioms passed (18,291 declarations, 932 modules, unchanged debt).

The two publication checkouts were validated on their actual PR bases; their new theorem
sources are byte-identical to the independently reviewed worker result. Both retain 286
existing sorry-tainted declarations and zero nonstandard-axiom taint.

VCVio #824's CI environment linter found a direct retired-probability reference generated
by broad simplification in a finite-table proof. Commit `e417e35a` replaces that step with
explicit indicator rewrites and the native impossible-event lemma. The statement is unchanged;
its target builds cleanly and an independent proof-only review found no semantic weakening.
The full environment-lint recheck is pending. No lint baseline or exemption was changed.


### Combined upstream validation

VCVio integration `034aa6938e379b303b178c18589812e79b7f508a` combines the reviewed expected-query
result, its native-probability proof repair, and the reviewed native Merkle owner migration.
`./scripts/validate.sh --axioms --lint --test` passed in 204.7 seconds: 22,138 declarations,
785 modules, 14 unchanged sorry-tainted declarations, zero nonstandard-axiom taint. The exact
lint baseline is unchanged. ArkLib integration now pins this combined revision in its own
clean cache entry. VCVio #825's GitHub checks are all green.

The restoration publication branches now pin `e417e35a`: #1267 head `0815f8c74`, #1268 head
`8e290aa71`. Each complete ArkLib source build passed again after that pin-only update;
the reviewed theorem source files are unchanged. The expected-query lint repair itself
passed the complete environment linter at its exact head.


### Principal Merkle and Sumcheck milestones accepted

The Merkle clean-ideal repair `daa80f50e` passed an independent follow-up review; the public
numerical and eta bounds now use the verifier-free ideal experiment, with equality proved
for every Boolean event. Honest verification can change cache/log state, and no full-state
equality is claimed. The repair review is saved in
[merkle-ideal-repair-second-night.md](reviews/merkle-ideal-repair-second-night.md).

The clean-main publication slice needed the existing `executeStrategies_done` and
`executeStrategies_public_sender` owner lemmas from the earlier theory stack. They were copied
byte-for-byte, independently checked for effect order and retained dependent outputs, and
built on main. Initial clean-base builds exposed these missing helpers and an out-of-order
umbrella import; both packaging issues were repaired. Final `./scripts/validate.sh --axioms`
on `f6d8d94cf` passed in 93.3 seconds: 18,190 declarations, 922 modules, unchanged 286 sorry
debt and zero nonstandard axioms. Its complete publication diff is 1,447 changed lines.

[ArkLib #1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269) is the Sumcheck application,
669 added lines on #1268. Publication head `afe42b588` passed full validation with axioms
(201.6 seconds including setup; 18,338 declarations, 935 modules, unchanged debt). Its
source is identical to worker `de806e13c`. Both an ordinary independent review and a fresh
blind readback of the frozen probability statements approved the milestone. The fresh
readback is saved in [sumcheck-restoration-final-blind-second-night.md](reviews/sumcheck-restoration-final-blind-second-night.md).

The two remaining Further SHOULD lanes have exact durable contracts:
[causal terminal queries](adaptive-terminal-query-contract.md) and
[new queries outside a fixed initial cache](initial-cache-query-contract.md).
These are extensions; the accepted MUST results and completed Sumcheck/Merkle statements
are preserved independently. No online-opening compiler, arbitrary guarded restoration,
substantive new witness reconstruction, or machine-efficiency result has been asserted.


### Combined primary integration checkpoint

All accepted second-night source changes now coexist in the integration branch. Full
`./scripts/validate.sh --axioms` passed in 139.3 seconds on source checkpoint `f0a7268c0`,
with 18,699 declarations across 939 modules, unchanged 286 sorry-tainted declarations,
and zero nonstandard-axiom taint. Later commits at this checkpoint only update research and
review records. The integration VCVio pin is the fully validated combined `034aa6938`.

ArkLib [#1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270) publishes the native Merkle
transfer against main. ArkLib main was rechecked as `ace55c3e2` and VCVio main as `bc3433e3`
after the primary integration check. Ongoing extension work is isolated in
`ArkLib-merkle-adaptive` and `VCVio-initial-cache`; it is not counted as accepted yet.

### Causal terminal programs accepted

[ArkLib #1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271) adds the general finite
`QueryProgram`, exact terminal transcript checking, recursive real/extracted path agreement,
native execution marginals, and the ROM and eta transfers. Its ideal program depends only on
the public roots and immutable extracted vectors. A proved Boolean marginal erases the entire
malicious terminal-opening and honest verification suffix. This is causal evaluation of a
terminal batch, not online opening exchange.

The frozen code `3e643980c` passed full `./scripts/validate.sh --axioms` in 150.7 seconds:
18,272 declarations, 923 modules, unchanged existing sorry debt, zero nonstandard-axiom taint.
Fresh blind readback and subsequent strict contract/proof review approved the slice without
actionable findings; see [adaptive-terminal-second-night.md](reviews/adaptive-terminal-second-night.md).
Publication head `e9ee95267` has the identical complete source tree after incorporating its
parent's import-order fix. The PR is 790 added lines on #1270. Integration cherry-pick
`a2f8a8ee8` preserves the reviewed source and regenerates the combined umbrella.

The fixed-initial-cache extension `c50275fb` has passed `validate.sh --axioms --lint --test`
in 222.8 seconds, with 22,159 declarations across 786 modules, unchanged exact lint baseline,
and no new axiom/sorry taint. Its fresh blind review is pending, so it is not yet accepted.

The HOPE design work is recorded in [early rejection and restoration](guarded-restoration-open-questions.md).
It distinguishes the proved Sumcheck replay from candidate generic obligations and keeps
execution, cache handoff, padding costs, challenge carriers, and witness reconstruction open.

### Fixed initial-cache extension accepted

[VCVio #826](https://github.com/Verified-zkEVM/VCVio/pull/826), stacked on #824, publishes
`prEvent_randomOracle_le_expectedNewQueryCharge` at `c50275fb`. It generalizes the existing
per-key proof, retains the old empty-cache API, and proves the arbitrary-domain result through
the actual joint-run finite-support bridge. The charge counts distinct queried keys absent
from the supplied initial cache. The trace hypothesis must identify a bad key among those
newly sampled keys; an initially cached bad answer alone is not covered.

A fresh mathematical readback followed by contract, proof and API review approved the exact
head with no findings. The review also checked the author's complete validation log; see
[initial-cache-second-night.md](reviews/initial-cache-second-night.md). GitHub reports 393 insertions
and 37 deletions across three files. VCVio combined integration `7aa43ec4` retains this source
byte-for-byte together with the native Merkle owner migration. Its full combined validation
and the final downstream pin check are in progress.

The HOPE note passed a separate ordinary review. Two precision improvements were applied:
rejected runs can differ in cache/log state, and output replay alone does not establish
prefix effect agreement. See [the note review](reviews/guarded-restoration-note-second-night.md).
