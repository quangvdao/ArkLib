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

## Third checkpoint preparation (06:49 UTC)

- R now constructs actual recursive numerator polynomials and proves their degree bound,
  their rational residual equation, and equality with every actual regular solution's
  Taylor coefficients under the exact binomial-pivot nonvanishing hypotheses.
- A literal common-denominator chart has degree bound `1+2K(v-1)`, retains its initial
  coordinates, and is injective. Its initial hypersurface has the actual separant as
  a derivative. High-coefficient cuts followed by k distinct agreement cuts leave at
  most one regular jet. No geometric degree axiom enters these proofs.
- Independent canaries prove a positive ZMod5 quadratic and necessity of both pivot
  hypotheses via same-jet collisions at the characteristic boundary and at a singular
  characteristic-zero jet. Actual build lint caught flexible simp in a canary; fixed.
- S constructs the concrete polynomial-challenge matrix with a finite active-row
  reduction of the genuinely infinite local row index. An actual rank bound gives a
  primitive kernel and an interpolant nonzero at every extension/challenge specialization.
- Actual local rank is invariant under point translation and cannot increase under
  coefficient-field extension. Soundness of specialized concrete interpolants is proved
  from actual local constraints and band support. The final stacked-band adapter and
  unconditional prescribed symbolic certificate remain active scratch work.
- All seven source modules received independent statement/proof review. Targeted builds
  passed for six; promoted soundness enters the full gate next. Central second checkpoint
  integration passed; it released the full-build slot at 06:48 UTC.

## Third checkpoint certified (06:55 UTC)

- Full default validation passed every requested check. Axiom sweep passed over 22620
  declarations and 810 modules: 312 preexisting sorry-tainted declarations, zero
  nonstandard axioms, and no new taint. The baseline remains unchanged.
- Source trust comparison versus `f34ca271`: admissions 183→183, explicit axioms/native
  trust 0→0; exactly three new kernel-checked canary examples, no other new constructs.
- Seven frozen modules total 2163 source lines. Each has an independent mathematical
  audit; actual targeted builds and the full warning/source-policy gate passed.
- General field-independent list and small/intermediate MCA bounds are still open.
  Their missing degree-sum/Bezout layer is not hidden behind the proved chart or rank APIs.
- Full-gate slot released. Next scratch: prescribed unconditional symbolic-band
  certificate, actual retained-minimal-prime cut/dimension theory, zero-dimensional
  coordinate-algebra point bounds. Deadline remains 09:21:04 implementation freeze.

## Fourth checkpoint preparation (07:09 UTC)

- The prescribed small-gap symbolic certificate is now unconditional under its actual
  source parameter package: no rank or height premise remains. Its challenge degree is
  below `338(2m-1)`, total jet degree at most `2m-1`, and every extension/challenge
  specialization is nonzero and satisfies the full differential root identity for all
  close degree-<k polynomials. Independent audit and strict targeted check passed.
- G now has actual finite retained minimal-prime covers, proper-cut Krull dimension
  drop, and finite extension-field zero-locus cardinality bounded by the dimension of
  the actual zero-dimensional quotient algebra.
- The actual affine Hilbert function equals the finite count of standard monomials.
  Division by all nonzero ideal polynomials supplies unique degree-nonincreasing normal
  representatives; Dickson supplies a finite forbidden-divisor basis. No abstract degree
  laws or eventual-polynomial hypotheses were assumed in this reduction.
- Exact graph recognition/descent over every extension field and at most n accidental
  challenges are proved. Every arbitrary-field RS list is genuinely finite for A>=k,
  with `list.card * choose(A,k) <= choose(n,k)`; this weaker combinatorial estimate is
  not substituted for the manuscript's desired polynomial-in-n bound.
- Next core G work is monomial counting to actual eventual Hilbert polynomials and
  principal-cut polynomial degree bounds. Equidimensionality/minimal-prime multiplicity
  additivity and the refined Bezout degree sum remain explicitly unproved.

### Fourth checkpoint certification (07:17 UTC)

- Full default validation passed with 816 generated umbrella imports, including warning
  budget, source policy/plugin fixtures, all compiled runtime checks, import consistency,
  timing fixtures, documentation integrity, and knowledge-base lint.
- Axiom sweep passed: 22702 declarations / 817 modules, 312 preexisting sorry-tainted
  declarations, zero nonstandard-axiom taint, and no new taint. The unchanged fixture
  executable reuses the previously certified matrix; shared dependency preparation was
  deliberately not rerun. No axiom baseline change.
- Source audit versus `ef320a7f` is exactly unchanged: 183 admissions, 679 examples,
  zero explicit axioms and native-trust references; no added or removed constructs.
- The seven independently audited modules total 1386 lines. All actual target builds
  and full validation passed after two overlong documentation lines were shortened.
- Scratch progress after this frozen checkpoint: the actual standard-monomial count is
  an eventual rational polynomial; principal-cut eventual-polynomial degree/coefficient
  bounds are proved. Canonical integration and independent audit are ongoing. These are
  not yet a refined Bezout theorem or the final manuscript list/MCA bounds.

## Fifth checkpoint certification (07:29 UTC)

- Four independently audited modules (888 lines) prove eventual polynomiality by
  actual standard-monomial counting, define the unique canonical affine Hilbert
  polynomial, and prove genuine principal-cut polynomial degree/coefficient bounds.
- Public canonical existence needs only a finite variable type and a field. The
  auxiliary finite ordering is confined to the proof; uniqueness is with respect to
  the actual filtration. Constant Hilbert polynomial implies a finite-dimensional
  quotient by filtration stabilization, and finite quotients have constant polynomial
  equal to their dimension. Actual zero-dimensional point counts are bounded by its
  constant coefficient over every extension field.
- A prime principal cut has zero Hilbert polynomial or degree at most parent degree
  minus one and top possible coefficient at most b*d*leadingCoeff(parent). A minimal
  prime over a proper cut has relative height exactly one in the parent quotient.
  Relative height is not asserted to equal the missing ambient degree difference.
- Actual targeted builds passed with no warnings. The first full gate caught a
  missing module-level docstring in HilbertPrincipalCutDegree; after adding it, the
  entire default validation passed (820 root imports, 4665 build jobs). Two prior
  targeted source-style warnings in monomial counting were fixed before this gate.
- Axiom sweep passed: 22753 declarations across 821 modules, 312 preexisting
  sorry-tainted declarations, zero nonstandard-axiom taint, no new taint, unchanged
  baseline. Source audit versus ca66997c is exactly unchanged in all four categories.
- Remaining critical geometry: finite-prime separator injections/coefficient sums
  and proof that each minimal component of a principal cut has the expected Hilbert
  polynomial degree. Scratch localization-growth work is pursuing the latter directly;
  the final manuscript list and small/intermediate MCA bounds remain unproved.

## Sixth checkpoint certification (07:46 UTC)

- Five independently audited modules (731 lines) establish finite-prime separator
  injections, their canonical top-coefficient sum inequality, radical invariance of
  Hilbert-polynomial degree, an actual principal-localization filtration sandwich,
  and polynomial growth invariance under linear rescaling.
- Radical invariance is proved directly: if radical(I)^t lies in I with t>0, exponent
  division/remainder injects standard(I) into standard(radical(I)) times t^r residue
  vectors. Thus HF(I,N)<=t^r HF(radical(I),N), while ideal inclusion supplies the
  reverse degree comparison. No multiplicity or dimension law is assumed.
- The separator theorem handles every finite incomparable prime family, including
  empty and singleton families. The earlier unconsumed two-prime scratch theorem was
  omitted because the finite-family theorem subsumes it; its scratch remains preserved.
- The localization statement is an actual finrank bound for bounded numerators and
  denominator powers, not yet a canonical Hilbert-polynomial presentation theorem.
- Full default validation passed after adding a missing module docstring; root825.
  Axiom sweep passed over22787 declarations/826 modules,312 preexisting sorry-tainted,
  zero nonstandard axioms and no new taint. Source audit vs9c45b50c is exactly unchanged.
- One targeted Away build initially read an evolving scratch snapshot after its frozen
  version; the exact audited snapshot was restored and passed actual target/full gates.
  No certificate includes that failed intermediate snapshot. Future transfers pin hashes.
- Remaining central obstruction: principal-cut HP degree lower bound/purity for every
  minimal component. The preceding coefficient sum does not count lower-degree children.
