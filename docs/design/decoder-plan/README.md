# Decoder status and remaining work

This is the single current handoff for the Reed–Solomon decoder on
`quangvdao/ArkLib:quang/decoder-realign-p4-integration`. The four September 13
workstreams are collected here. Collection does not mean that the public
positive-order decoder is complete.

The public zeroth decoder now works over supplied effective fields. First-order
filtering has chart-local exactness from actual source coverage. The largest
remaining tasks are constructive common-center normalization and boundary
production, unconditional dense root solving, and public composition.

The paper specification is commit
`24276c570658604e12dd9c3d119f2b6f3200b54d` of
`quangvdao/rs-capacity-and-correlated-agreement`. Do not silently adopt a later
algorithm change. The paper and its soft-locked abstract are outside this
handoff's edit scope. Mathematical list/MCA extensions and application
certificates will be handled separately.

## Scope and completion contract

Finish the executed decoder and prove its correctness. Arithmetic, bit, RAM and
native runtime analysis are excluded. Termination, no-failure proofs, field-size
guards, and degree/dimension/cardinality bounds needed by finite searches remain
in scope. So does correspondence with the prescribed algorithm: a correct slower
backend can remain a named reference, but renaming it does not establish that the
canonical program executes the paper's procedure.

The final supplied-equation and certified-support entrypoints must return the
existing `ReedSolomon.ListDecoding.ExactOutput`: all degree-`<k` messages with at
least `A` agreements, no others, and no duplicate fixed-width coefficient vectors
or polynomial images. Include the zero polynomial and impossible-agreement case.

The supplied-equation theorem may assume its checked nonzero bounded equation
vanishes on all wanted messages. The certified-support entrypoint must compute
such an equation. Neither final theorem may assume a good center, candidate
families, an internal successful run, solver factorization, unknown roots, or
producer coverage. Intermediate theorems may expose these premises; final
composition must discharge them from the executed producers.

Do not replace symbolic reconstruction by exhaustive field/message enumeration.
Keep exhaustive decoding only in justified bounded-instance branches or as an
independent small-instance test oracle. Proof-only algebraic closures and
factorizations are semantic tools, not executable inputs.

## Collected sources and history

| Source | Exact collected checkpoint | Contribution |
| --- | --- | --- |
| Integration baseline / P4 | `a9dde639a5c39797962cfed34659f7e72aec5706` | Checked Taylor preparation, public effective-field zeroth decoder, earlier integrated foundations |
| P1 | `7e3087d143f99ac4d3ff113677ce752b94c2acbd` | Ordinary common-center path, finite normalization infrastructure, trace semantics and partial guard budgets |
| P2 | `f8590d112eb0be4fb275372fb83761fe351cbb47` | Nonreduced recovery, chart-local curve filtering and source-coverage exactness |
| P3 | `0ba900818a264b46f04836cd0ca111bfae7aef0f` | Robust/exhaustive chart selection, dense quotient and deformation foundations |

The union retains all four inputs as ancestors. Its baseline already contains
P1 `46dd735e71c2ca0874faf752bf12ed4d92f839c6` and the reviewed P3 safe-map,
deformation and root-data slices. Do not replay those commits. Toolchain,
dependency pins and the axiom baseline are unchanged.

Integration preserves P4's unique standalone Rojas test names where incoming
files used a shared root `main`. The legacy first-order pipeline explicitly
uses `WellFormed.nonreduced` when passing its stronger squarefree-fiber output
to the generalized recovery consumer; candidate execution is unchanged.

The earlier plans and adoption ledger remain recoverable at the immutable
[pre-consolidation documentation tree](https://github.com/quangvdao/ArkLib/tree/a9dde639a5c39797962cfed34659f7e72aec5706/docs/design/decoder-plan).
They are historical evidence, not alternate task boards. This page supersedes
their model policies, staffing proposals, deadlines and obsolete algorithms.

The combined source gate checks 44,957 declarations across 1,826 modules, with
289 unchanged historical `sorryAx` taints and no new or nonstandard-axiom taint.
The adopted test delta has 49 executable suites and 29 compile-time-only clients;
20 suites were already registered, and this integration registers the other 29.
Standalone test names are unique and each suite runs once. Builds, warning
budgets, source policy, runtime suites, imports, documentation and axiom checks
are required together; the constituent worker gates do not replace this union gate.

## Completed interfaces to reuse

In the table, `RS/` means `ArkLib/Data/CodingTheory/ReedSolomon/`, `LD/` means
`RS/ListDecoding/`, and `FT/` means `RS/HiddenDerivative/RootFinding/FastTaylor/`.
These are path abbreviations, not Lean namespaces.

| Component | Source and principal endpoint | Established boundary |
| --- | --- | --- |
| Public zeroth decoder | `LD/ZerothOrderDecoder/EffectivePublicDecoder.lean`: `run?_exists_exact`, `run?_ne_none` | Data-only interpolation, normalization, centers, transport and recovery under public `Valid`; no positive-order characteristic promise |
| Effective fields | `ArkLib/Data/FiniteField/ExplicitConstruction/` | Supplied arithmetic, staged inverse Frobenius, relative quotients, effective extension/center search and transport |
| Nonreduced towers | `LD/TowerRepresentation.lean`, `LD/TowerAlgebra/PrimarySplit.lean`, `LocalizeFiber.lean` | Powered splitting, full primary multiplicities, geometric partition and dimension accounting |
| Shared recovery | `LD/AgreementRecovery/` | Exact interpolation/filtering/deduplication for represented families; tower and reduced multiplication-table consumers |
| Curve candidate execution | `LD/FirstOrderCurveCandidates/Producer.lean` | Closed-component removal, lowest-resultant coefficients, threshold, one radical, localization, actual-denominator inversion and centered materialization |
| Chart-local exactness | `LD/FirstOrderCurveCandidates/SourceCoverage.lean`: `decode_exact_of_source_coverage` | Exact output from an actual successful source constructor and source coverage; no threshold-root, candidate-membership, representation or payload oracle |
| Candidate budgets | `LD/FirstOrderCurveCandidates/ProducerBudget.lean`: `run_base_degree_mul_le`, `run_dimension_mul_le` | Base-degree and full nonreduced-dimension bounds in terms of the computed coefficient-degree budget |
| Checked Taylor preparation | `FT/TriangularPreparation.lean`, `TriangularChart.lean` | Division-free shift, actual initial root, checked separant inverse, characteristic-certified binomial units, recurrence and cleared-numerator provenance |
| Existing chart constructor | `FT/Constructor.lean`, `Contract.lean`, `Coverage.lean` | Concrete one-chart construction and global agreement contract using the retained Newton backend |
| Varying order | `FT/VaryingOrder.lean`, `SemanticTraversal.lean` | Dependent stage dispatch, input-derived fuel, strict descent, prefix identities and regular-stage coverage |
| Ordinary common-center partition | `ArkLib/Data/Polynomial/FunctionFieldAlgorithms/CommonCenter/OrdinaryFinalization.lean`: `run_exists_partition`; `OrdinaryDegreeBounds.lean`: `run_exists_of_kappa` | Actual trivariate ordinary-tail/regular-curve partition and large-characteristic cutoff |
| Robust selection | `LD/HigherOrderProducer/RobustBallCoverage.lean`, `RobustBallChart.lean` | Executable field-independent selection, agreeing full-span capture, actual equations/Jacobian/isolation under chart hypotheses |
| Dense special cases | `ArkLib/Data/Polynomial/Rojas/Producer/MacaulayEmptyMinor.lean` | Unconditional quotient and perturbation success for univariate and affine-linear square systems |
| General dense foundations | `ArkLib/Data/Polynomial/Rojas/Producer/` | Conditional safe maps, deformation and root-data results; general factorization and isolated-root coverage remain open |

Preserve these distinctions at every consumer:

- Chart numerators store ascending Taylor coefficients at the center. Public
  recovery consumes descending Horner coefficients in the original variable.
  Use the proved translation/reversal in `CenteredMaterialize`, not a bare reversal.
- The tower base is squarefree where required; the monic fiber may be nonreduced.
  The split `gcd(h, e^r mod h)` retains complete primary factors. Do not run the
  legacy fiber-radicalization path to satisfy an obsolete invariant.
- Invert the actual stored denominator. Its geometric nonvanishing follows from
  the chart identity; literal equality with an unreduced separant power is not needed.
- P2's final source theorem still requires source scheduling/coverage, source
  squarefreeness, positive weighted equation degree and its `Bjet` bound, the
  agreement range `k <= A <= n`, and a certified executable inverse Frobenius.
  It does not enumerate global charts or show one arbitrary chart covers every message.
- Supplied cyclic Frobenius coordinates certify bijectivity and rotation, not
  linear normal-basis structure unless that additional structure is supplied.

## Remaining work

### 1. Switch the canonical Taylor constructor

`FT/Constructor.lean` still calls `FundamentalMatrix.nonlinearNewton?`. The checked
replacement exists in `TriangularPreparation` and `TriangularChart`; reuse it.
Feed its recurrence output into local recovery and global normal-form
reconstruction. Transfer `Contract` and `Coverage` using cleared-numerator
provenance, preserving the projection, confluent sample, actual root, separant
inverse and coefficient order. Equality with the old Newton output is unnecessary
if the new executed path directly establishes the required semantic contract.

Next connect the general dyadic block/cache schedule in `RelaxedConvolution` to
the full recurrence and prove gate equivalence. The single quadratic cached
example is not a general scheduler proof. Reconcile the rational boundary
recurrence with the prescribed execution as well; its current inversion backend
needs explicit accounting, not a runtime theorem.

Acceptance: the canonical constructor executes the new path and retains global
agreement at every regular point, not only the chosen sample. Keep nonzero-center,
nonidentity-projection, repeated-fiber and nonconstant-unit regressions, including
`X^p` and `X^(p+1)` cases that reject factorial-based shifts.

### 2. Compute the first-order normalization

Work in `ArkLib/Data/Polynomial/FunctionFieldAlgorithms/CommonCenter/`. Its finite
representations and conditional laws are not yet an integral-closure producer.

1. Derive `ProjectionGrid.BadSlopeControl` from the actual reduced equation,
   separant, degree and characteristic hypotheses.
2. Construct the projected order and actual bases/multiplication tables for its
   finite windows and every intermediate order.
3. Instantiate the trace-kernel converse on these actual algebras, deriving the
   Artin decomposition, residue-field and characteristic facts it currently takes
   as inputs. Compute a complete radical basis.
4. Execute endomorphism enlargement, prove strict progress, and implement the
   bounded iteration.
5. Prove the Grauert–Remmert stabilization criterion applies and that the terminal
   order is the integral closure.
6. Extract the free basis and multiplication table with integrality, degree and
   denominator-height bounds from the original input.

The immediate bounded linear-algebra seam is the missing public theorem
`homogeneousKernelBasis_span_eq_kernel`. Returned vectors are sound, but the
normalization/coverage solver needs them to span the whole kernel. Prove this for
the entire basis; the first returned witness cannot solve general affine
constraints. Cover empty matrices, rank defects and free coordinates in the
augmented-system adapter.

Also finish the ordinary path's original-input denominator/cleared-degree bound
and reconcile its initial content convention with the pinned paper. Reuse its
actual partition rather than creating another ordinary-tail algorithm.

Acceptance: compute normalization without a supplied normal order, radical basis
or stabilization certificate. Include already-normal and genuinely nonnormal
curves, not only supplied multiplication-table tests.

### 3. Produce the common guard and single boundary family

This depends on actual normalization, not just its abstract representation.

- Construct the normalized derivation, `g = d*eta`, denominator ideal `I = (N:J)`,
  generators `c_l` and cleared products `b_li`. Prove their coverage identity on
  the actual normalization instead of assuming it in a supplied presentation.
- Replace caller-supplied `later` factors in guard assembly by the computed
  module, denominator, derivation, pivot and coverage factors. Prove that one
  nonzero guard specializes the whole construction correctly, within its budget.
- Construct `N_a / g_a N_a`, compute its reduced quotient, and build its algebra
  presentation. Complete the trace and powered/inverse-Frobenius branches under
  their respective characteristic hypotheses.
- Compute the idempotent ideal, lifted coefficients, combined denominator `c_*`
  and rational system. Prove its unit initial denominator and original-message
  coordinate map; invoke the generic rational recurrence.
- Prove coefficientwise coverage by this one finite boundary family.

Acceptance: return the boundary family from computed normalization with no
coverage or recurrence-success oracle. The cusp `Y^2 = (Z-1)^3` must exercise a
point missed by the original-open chart. A combined test must distinguish
ordinary-tail, original-open and boundary contributions.

### 4. Assemble the first-order decoder

Run common-center preparation, compute the base/quadratic center, and produce the
ordinary tail, original-open Taylor curve and reduced boundary families. Apply
P2's curve filter only to the open curve. Recover messages from the union using
the shared consumer and final agreement check.

Use `SourceCoverage.decode_exact_of_source_coverage` and its pointwise lemmas;
threshold capture is already proved. Derive source squarefreeness, positive
weighted degree and its `Bjet` bound, constructor success and scheduling from
actual producers. Connect chart coefficient-degree
bounds to `ProducerBudget` wherever a finite search or candidate bound uses them.
The existing budget is in terms of computed filter degrees, not a complete
original-input runtime estimate.

Replace the legacy norm/universal-component pipeline as the canonical path;
preserve it as a named compatibility implementation until its consumers move.
Keep the new uniform threshold `t = A-k+1`, rather than the old component-specific
threshold or a full multiplicity decomposition.

Under the standing positive-order guard `p > k-1`, dispatch first order to the
common-center path when `p > 2*(Bjet+1)^3`. Preserve the many-center route and
bounded-message accounting in the intermediate characteristic regime. Bounded
characteristic over an extension field does not imply bounded block length.

Acceptance: an exact first-order supplied-equation run with no chart-family
coverage premise, including extension transport, all three families, rejection,
deduplication and characteristic-boundary tests.

### 5. Close the general dense solver

Use `ArkLib/Data/Polynomial/Rojas/Producer/`. Keep its completed univariate and
affine-linear cases; they do not imply general nonlinear totality.

1. Prove Macaulay-specific divisibility of `extraneousFactor system` into
   `characteristic system`. `MacaulayFactorization` reduces this exactly to
   polynomial descent of `fractionSchurDet`; the descent remains open.
2. Derive `PerturbationFactorization` from the computed perturbation. Prove
   complete isolated-root coverage over the algebraic closure, including
   zero-coordinate roots beside positive-dimensional components. Nonsingular
   base-field root divisibility after success is not this theorem.
3. Execute coordinate recovery under `|E'| > (s+1)^2 D^(2s)`. Eliminate the caller's
   `CrossCollisionSeparated` premise using actual isolated-root geometry or a
   newly justified recovery construction.
4. Prove general run success and representation of every required isolated root,
   then expose that producer to both selection modes.

Do not retry the disproved generic matrix/valuation argument. The current
avoidance estimate has a cubic root-count term and does not establish the
quadratic field guard. Reviewed counterexamples refute these generic bridges,
not the paper's solver theorem: the prime-733 example breaks fixed-alpha
subresultant safety, while prime-90001 breaks cardinality-only avoidance for
arbitrary point lists. The latter lists cannot be the isolated roots of the
claimed degree-bounded complete intersection. Exploit that geometry rather than
silently strengthening the field guard.

The scratch counterexamples are recorded in the historical P3 report. Before
using them as regression dependencies, bring their exact source into reviewed
durable tests; temporary files are not shipped theorems. A general sparse/toric
library is not a separate completion requirement unless the chosen dense proof
needs it. Any such dependency needs a precise theorem and consumer.

### 6. Compose higher-order stages and public dispatch

The robust selector is complete locally. Instantiate
`RobustBallChart.exists_robust_selectedChartSystem_capture` with actual Taylor
equations, nonzero normal, agreement zeros and tangent gap. Consume its actual
selected systems, Jacobian and isolation result; do not reintroduce a supplied
basis, expansion estimate or successful-selection oracle.

Connect both all-subsets and robust modes to the completed dense solver. Localize
its parameter algebra, substitute coefficient maps, apply the characteristic-safe
radical where prescribed, materialize and recover. Existing varying-order
traversal supplies dependent semantics and canonical fuel; finish concrete stage
producers and their coverage.

Replace `HiddenDerivativeDecoder.symbolicDecode`'s unavailable result. Generalize
remaining legacy prime-only options to the advertised effective-field interface.
Preserve separate guards for impossible agreement, constant messages, order and
message bounds, finite grids, characteristic promises and justified bounded
cases. Failure of a promise does not authorize unrestricted enumeration.

Acceptance: exact supplied-equation and certified-support entrypoints for both
selection modes and all emitted orders, without internal success or coverage
premises. Test lower-positive and zeroth descendants, not only the top order,
and extension-only parameters representing base-field messages.

### 7. Finish prescribed interpolation correspondence

Normalized local/global frames and Jordan actions are available under
`RS/Computation/Interpolation/Module/`. Implement the prescribed shifted
minimal-basis selection, connect its row to the support cutoff and constraints,
and prove that it explains every wanted message. Record the ordinary backend's
relation to the paper's fast GS interpolation separately.

Keep current valid matrix and Lee–O'Sullivan/Mulders–Storjohann variants as named
references. Exactness from a valid interpolant is not JNSV execution
correspondence. This task can proceed independently of normalization and Rojas.

### 8. Keep auxiliary variants explicit

The deterministic decoder is the first target. A release claiming all decoder
variants in the pinned paper must also cover:

- Sampled centers: soundness for every sample, completeness on the coverage event,
  and the finite independent-sampling/union bound. This is Monte Carlo completeness,
  not unconditional exact output or a Las Vegas claim.
- Bounded-input list recovery: position/symbol labels, distinct positions,
  symbol-aware splitting and interpolation, full input-list checking, and
  singleton compatibility. The mathematical labeled-incidence/rate theorem is
  separate; do not hide that missing proof in an executable assumption.

Do not silently add these to the deterministic milestone or omit them from a
claim covering all variants. Full nested-tower CRT equivalences remain optional
unless a concrete consumer needs them.

## Continuation and acceptance

Assign bounded tasks by source area and named consumer, not historical Personal
numbers. One coordinator owns shared interfaces, public dispatch, generated
imports and runtime registration. Use an independent nonauthor reviewer. The
user chooses models and effort levels; this page imposes no staffing policy.

The shortest independent next tasks are the canonical Taylor switch, complete
kernel-span theorem and interpolation correspondence. Normalization/boundary and
dense solving are the two deep parallel tracks. Global first-order and
higher-order composition depend on their respective tracks, not on each other.

Before publishing:

1. Record the exact base, input heads, changed contracts and remaining premises.
2. Stage new production/tests and run `./scripts/update-lib.sh`. Never hand-edit
   the generated `ArkLib.lean` or omit new modules from the checked root.
3. Register each executable regression once centrally. Keep compile-time clients
   in `ArkLibTest`; compilation alone is not execution evidence.
4. Run `LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true ./scripts/validate.sh --axioms`
   on the combined candidate. Do not change pins or broaden the axiom baseline
   to pass. Existing historical taint is not a new decoder axiom.
5. Independently review executed contracts, input-derived coverage, merge
   compatibility, tests and this page. Repair and rerun affected checks.
6. Commit the reviewed tree, verify the exact-head gate, non-force push to the
   authorized branch, and read back the remote SHA.

The final integration handoff records the validation log and publication SHA.
The command above remains the acceptance gate for each continuation. This source
union does not claim public positive-order completion or formalized runtime analysis.
