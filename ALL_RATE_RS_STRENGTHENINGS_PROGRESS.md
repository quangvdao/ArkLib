# Strengthening progress log

## September 4, 2026 — initial audit

- Base/head: `77ad3e8b12f5c0537f99aaba1d10511edd5e4e4f`, clean private branch.
- Read root policies, strengthening plan, review skill references, paper-note allowlist,
  canonical geometric/symbolic/CA proofs, and donor permission record in full.
- Donor reuse is supported by the recorded project-owner attestation, with credit;
  no blanket license or axiom trust inferred. No new donor adaptation yet.
- Dependency pin: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
  CompPoly `a09455a22fea4623a2a1c5b363cf6efc61486a83`, Lean `v4.33.1`.
- Created 20 private package links after checking exact revisions, URLs and cache
  identities. Some entries contain only the advisory untracked `.lean-deps-immutable`
  marker; do not call their literal Git status empty. Mathlib and CompPoly are clean.
  Dependency-local declared toolchains can differ from the enclosing pinned Lean
  version; no toolchain/manifest updates or shared cache mutations were made.
- Three bounded Sol/high workers active; ownership table and dependency graph are
  in the plan. Targeted Lean only until a full-build slot is coordinated.
- Manuscript affine section changed to an existing ArkLib theorem; use that shorter
  path. No complete strengthening theorem or validation checkpoint claimed yet.

## Validation ledger

The first six-module checkpoint passed the full repository gate, independent statement
review, axiom fixture matrix, and regression sweep; details appear below.

## September 5, 2026 — sprint start

- Exact cutoff propagated to all three workers at 05:52 UTC: implementation freeze
  09:21:04 UTC, handoff by 09:36, final stop 09:51:04. No continuation beyond deadline.
- Source-verified baseline artifacts copied read-only from central with its confirmation;
  7009 artifacts now independent private files. No symlinks into central outputs.
- `MutualAgreement.lean` exact-full-set bridge and `SupportWeight.lean` passed targeted
  Lean checks with warnings as errors. `TaylorSupport.lean` literal universal jets and
  residual support theorem passed initial targeted Lean; strict/source/axiom review next.
- Direct rational-chart counting may bypass image closure I/V. Correct handling of
  actual degree `<k` requires high-coefficient cuts first, paid through the invariant
  sum(degree(component)*b^dimension(component)); retained components cost nothing,
  proper cuts reduce dimension and multiply degree by at most b. Concrete Bezout
  remains unproved infrastructure. This is a proposed route, not a certified result.

## First checkpoint preparation (06:05 UTC)

- H and primitive H are complete, including actual RatFunc rank, gcd division, unit
  ideal, and nonzero specialization over arbitrary field extensions. Principal
  theorem axiom reports contain only propext, Classical.choice, Quot.sound.
- U proof and exact-set bridge independently reviewed with no correctness findings;
  floor-half odd case verified explicitly.
- Taylor support proves the literal universal Hasse-jet identity, later-coefficient
  Taylor-weight bound, and ordinary coefficient total-degree bound. Canonical
  residual evaluation and rational numerator recurrence remain next obligations.
- Auditor caught a duplicate newly drafted weighted-degree module; it was removed
  before staging and replaced with existing `Data/MvPolynomial/WeightedDegree`.
- First attempted import generation correctly rejected untracked work-in-progress
  modules. An inadvertently started warm build was interrupted; no pass claimed.
  Active new work moved to ignored scratch, frozen source staged, and generated
  imports updated successfully to 796. The real full gate is now running.
- Host has 16 logical CPUs and 64 GiB RAM; coordinated one full build plus targeted
  workers, no simultaneous full gates or shared dependency mutation authorized.

## First checkpoint certified (06:18 UTC)

- Full `LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true ./scripts/validate.sh` passed:
  4621 build jobs and all requested repository checks, including source policy,
  warnings, import coverage, runtime fixtures, documentation, and knowledge-base checks.
- `scripts/test-axiomsweep.sh` passed its complete fixture matrix. The subsequent
  `lake exe axiomsweep --check` passed: 22431 declarations, 797 modules, 312 existing
  sorry-tainted declarations, zero nonstandard-axiom taint, no new taint.
- Source trust comparison against `77ad3e8b12f5c0537f99aaba1d10511edd5e4e4f`:
  admissions 183→183, explicit axioms 0→0, native trust 0→0; no added constructs.
  The existing axiom baseline was not changed.
- Frozen checkpoint includes polynomial kernel height, primitive kernel specialization,
  half-gap exact correlated agreement, the full-set MCA bridge, support-weight algebra,
  and literal universal Taylor support. It does not establish full geometric list bounds.
- Operational correction: the fixture script invokes VCVio submodule preparation.
  This was inadvertently run through a shared package symlink; inspection afterward
  found all pinned submodules present and no source changes (only the preexisting
  `.lean-deps-immutable` marker). Future fixture runs must omit that preparation step.
- Full-build slot released to the central integration task at 06:18 UTC. Subsequent
  proofs remain isolated scratch until this checkpoint is committed.

## Second checkpoint preparation (06:26 UTC)

- Central independently read all six first-checkpoint proofs and passed its full
  integration validation and axiom sweep. Its sole integration branch owns publication.
- Six next modules are frozen and independently audited: actual half-gap line/affine
  MCA bounds; actual filtered quotient Hilbert principal-cut inequality; fixed band
  margin for actual global/local dimensions; universal residual evaluation; exact
  Taylor denominator support budget; literal denominator clearing and numerator degree.
- All six passed targeted builds and strict source checks. Full gate is next; active
  rational numerator recurrence and symbolic received-line matrix proofs stay scratch.
- The geometric Hilbert polynomial/degree/Bezout layer remains open. The filtered
  quotient inequality does not claim or assume that missing layer.

## Second checkpoint certified (06:32 UTC)

- Full default validation passed all 4636 build jobs and every repository check.
  During promotion, the gate caught five unused DecidableEq hypotheses in the MCA
  wrappers and a missing scratch-file copyright header; both were corrected before
  the passing run. No suppression or proof option was added.
- Axiom sweep passed with no new sorry taint and zero nonstandard-axiom taint.
  The unchanged sweep executable's fixture matrix was already certified in the first
  checkpoint; its shared-submodule preparation was not repeated.
- Source trust inventory versus `7898fefd` has zero delta in every category. The
  six new modules have independent mathematical review and targeted Lean checks.
- Full-build slot released. Active symbolic matrix/local-rank and rational Taylor
  recurrence work remains outside tracked source during this frozen checkpoint.
