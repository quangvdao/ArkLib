# Quantitative Reed–Solomon release: completion handoff

## Continue here

Work on branch `quang/reed-solomon-quantitative-bounds` in
`/Users/quangdao/Documents/Lean/ArkLib-rs-math-completion`.
The branch was renamed from `quang/rs-math-completion`; do not recreate the old branch.
The mathematical base is `ffab000e71c5b19e8a19bebadcc0050eac1366e3`.
The independent decoder branch remains at the published checkpoint
`2c75cdd6fe6cf723aea5254006d2d6c8389d7aad`; do not merge decoder work into this pass.

Paper worktree: `/Users/quangdao/Documents/Research/rs-capacity-and-correlated-agreement`,
starting head `8123a36d90e78aee1f40727c08a61e655d0a09bd`.
Preserve its pre-existing decoder handoff changes. Read `AGENTS.md` and `WRITING.md` there.
The abstract remains soft-locked. This handoff does not authorize changing it.

The author's [headline watchlist](../reed-solomon-results.md) pins the result families and
the standard for docstrings and inline annotations. Update statuses there as work is verified.
Do not create a separate competing checklist.

## Decisions already made

- Keep the paper's bounded-input list-recovery theorem and appendix. Explicitly exclude
  list recovery from formalization. Do not implement a list-recovery definition or proof.
- Remove the separate exact-on-the-first-order-curve endpoint corollary. Do not implement
  its zero-gap Lean bridge. The positive-gap headline theorem and constant-code cases stay.
- Retain and formalize independent optimization of the squarefree ordinary-factor threshold.
- Give core statements readable docstrings and inline annotations; preserve already-good prose.
- Separate the mathematical entrypoint from decoder imports. Preserve decoder source unless
  the author later requests a physical release slice.
- Running-time analysis and complete deployed-system verification are outside this pass.

## Immediate edits already made

1. Renamed the branch to its public-facing name.
2. Removed `cor:first-order-endpoint` and its proof from `core/first-order.tex`.
3. Replaced the endpoint/list-recovery alignment paragraph in `appendices/E-lean-statements.tex`
   with an explicit list-recovery exclusion. Added the same exclusion to the introduction's
   `shared/lean-formalization.tex`; retained the appendix and all list-recovery math.
4. Corrected the contradictory list-recovery instruction in `docs/public-release-plan.md`.
5. Removed `ListDecoding.PaperAlgorithms` from the mathematical `PaperGuide` imports and
   added the two exact `Capacity.FixedRateExplicitGate` imports. Updated its source map.
6. Expanded the selected fixed-rate list theorem and fixed-rate MCA theorem docstrings and
   statement annotations. Their theorem types and proofs are unchanged.
7. Added the public reader's watchlist and this continuation handoff.

The worktree now has an isolated build environment copied from the integrated decoder
worktree, with matching manifest/toolchain and independently verified clean dependency
revisions and origin URLs. Do not share its writable build directories with another task.
The annotated modules and both guides have compiled. Before later commit/push operations,
run the full prescribed validation again; a historical checkpoint is not validation of new edits.
The scoped paper changes are published on `main` at
`546af79c2c05c6d5e629466d9d5aa4a7f4e5cdac`; its unrelated decoder handoff edits remain uncommitted.

Immediate checks passed: the paper builds at 129 pages (within the 130-page soft target),
with no final undefined-reference or overfull-box warnings; the abstract source is unchanged.
Static traversal of both guide imports reaches 540 local modules (512 production, 28 example),
with none in the excluded executable families listed in Task 3. Comment-stripped Lean tokens
in the two annotated theorem files are unchanged. Documentation links, repository documentation
integrity, generated umbrella imports, and whitespace checks pass. These checks do not replace
Lean elaboration or the final axiom audit.
An independent Sol High source review found no mathematical or scope blocker. Its request
to pin the two Reed–Solomon tensor-fold declarations was applied, together with the suggested
application-facing squarefree wrapper. The reviewer did not rebuild Lean.

Publication validation on September 13, 2026 passed with artifact caching disabled:
`./scripts/validate.sh --axioms` checked 36,942 declarations across 1,542 modules,
with 289 unchanged historical `sorryAx`-tainted declarations, zero nonstandard axioms,
and no new taint. Builds, tests, runtime suites, source policy, imports, and documentation
checks passed. The log is `/tmp/rs-math-publication-validation.log`, SHA-256
`cd8126a81aa5dc912747d847f837e894c6fdc638d22746d1de62843b3cf6c164`.
This validates the immediate annotation/import changes, not the unfinished optimization
wrapper or remaining readability tasks below.

## Task 1: finish the squarefree ordinary-threshold wrapper

Paper contract: `core/first-order-counting-interface.tex`, `lem:first-order-factorwise`,
and `core/first-order-tuning.tex`. The ordinary contribution minimizes over integer
`D+1 ≤ L0 ≤ A`, independently of the regular-family retention parameter `L`.

Existing reusable pieces, relative to `ArkLib/Data/CodingTheory/ReedSolomon`:

- `MutualCorrelatedAgreement/Ordinary/Factors/UnifiedBudget.lean`:
  `ordinaryUnifiedPowerFactorRawAt`, `ordinaryUnifiedPowerFactorAt`, and
  `ordinaryUnifiedPowerFactorAtOrHeight` describe a freely chosen ordinary retention.
- `MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean`:
  `exists_exceptional_ordinaryPowerEquation_freeRetention` and its base/all-degree variants
  already prove the ordinary semantic theorem.
- `MutualCorrelatedAgreement/FirstOrder/HybridCurveTransfer.lean`:
  `curveRetentionMinimum`, its attainment theorem, `hybridCurveAtDegree`, and
  `hybridCurveAtDegree_le_pair` provide the finite-minimum pattern.
- `MutualCorrelatedAgreement/FirstOrder/Squarefree/Sharp.lean` currently uses
  `retainedSquarefreeOrdinaryCurveMCARaw`, whose ordinary threshold is fixed to `D+1`.
  Its sharp semantic theorem, certificate wrappers, and envelope need the new parameter/minimum.
- `MutualCorrelatedAgreement/FirstOrder/HybridCurveProfile.lean` packages the `best` envelope
  and the exact powers-family witnesses consumed by applications.

Implement an explicit-retention squarefree theorem first. Then minimize the ordinary term
using an attained minimum on `Finset.Icc (D+1) A`, and carry it into the curve certificate.
Preserve the old fixed-retention interface as a specialization or conservative compatibility
bound: downstream frozen arithmetic must not silently change by definitional reduction.
Prove that the new envelope is no larger than the old one by selecting `L0=D+1`.

The 32 frozen application rows currently use the fixed-threshold squarefree envelope or a
conservative bound. No changed query count or byte claim is needed. Recheck their exact
envelope equalities and inequalities when integrating, particularly `CurveMigration.lean`,
ZisK `Interpolation.lean`, and LambdaVM `Certificates.lean`.

Acceptance: exact paper formula; both retention choices genuinely independent; complete
common-witness semantics, not just a smaller arithmetic expression; nonempty minimization
domain from `D<A`; correct `A=n`, derivative-degree-zero, and constant-code dispatch;
all-characteristic ordinary tail with unchanged positive-order characteristic guard;
old application certificates preserved; no new axioms, admissions, or hypothesis oracles.

## Task 2: complete the readable headline surface

Work through R1–R12 and A1–A3 in the watchlist. Inspect the actual statement and its property
definitions before editing. The current exact fixed-rate annotations are a first example,
not a requirement to copy their sentence structure everywhere.

For each group, record the exact paper theorem/equation it supports and whether all
hypotheses match. Fix source-map omissions, not theorem types, when the proof already exists.
In particular, `fixedRatePartitionOrder_list_bound_selected` and
`fixedRatePartitionOrder_lineMCA` already formalize the explicit fixed-rate formula;
`exists_fixedRate_capacity_bounds` is a different eventual-small-gap formulation.

Do not confuse existing constant/full-code endpoint dispatch with the removed zero-gap
corollary. Do not cite older inverse-cubic/inverse-quintic first-order wrappers as the
headline result. Keep arbitrary-field finiteness and the order of MCA quantifiers visible.

Acceptance: an independent reader can explain the guarantee and all major premises from
the declaration and immediately linked definitions. Annotate parameter dependencies and
conclusion groups without turning the source into a second paper. Compile all edited modules.

## Task 3: verify the mathematical release boundary and paper map

1. Compute the local transitive import closure of the mathematical and application guides.
   Check that no executable `ListDecoding`, `Computation`, `FastTaylor`, `Rojas`, or
   `ToCompPoly` module is reachable. Mathematical root-counting/Taylor modules remain necessary.
2. Check user-facing import compatibility. The generated `ArkLib.lean` is still the full
   repository umbrella; do not claim it is mathematics-only and do not hand-edit it.
3. Check the retained paper statements and all literal Lean snippets against the final source.
   Preserve the simplified-decoder citation as a separate artifact; this math branch's guide
   is not its new validation evidence. Do not overwrite source pins with unvalidated edits.
4. Refresh public guidance, scope measurements, and artifact manifests only after validation.
   Keep historical reports historical; do not rewrite every old checklist.
5. Run `./scripts/validate.sh --axioms`, the applicable documentation/import checks, and
   all maintained application certificates. Have an independent reviewer check the exact diff,
   declaration contracts, and final evidence. Do not weaken policy gates or alter baselines
   to hide regressions.

Final acceptance: list recovery remains in the paper but outside the Lean claim; the removed
endpoint has no live references; the squarefree formula has an exact semantic Lean theorem;
all watchlist statuses are resolved; application constants are preserved; the paper builds;
the mathematical entrypoint and full repository gates pass; the abstract is unchanged.
