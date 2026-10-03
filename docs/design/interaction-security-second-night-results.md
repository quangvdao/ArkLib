# Second interaction-security run: evidence and progress

Status: active. The [authorized contract](interaction-security-next-night-contract.md)
controls scope; no main theorem is declared complete by this progress record.

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

## Current proof frontier

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
