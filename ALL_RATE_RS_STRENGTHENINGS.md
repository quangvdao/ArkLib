# Field-independent lists and mutual correlated agreement: follow-on plan

## Active MCA implementation: September 5 restart

### Completed qualitative all-rate MCA endpoints

For the paper-to-Lean correspondence and an introduction requiring no Lean knowledge,
start with [Reading the MCA theorem](ALL_RATE_RS_MCA_READING_GUIDE.md).

The public mathematical statements are
[`exists_allRate_correlatedAgreement`](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/AllRateCorrelatedAgreement.lean)
and
[`exists_allRate_affineAgreement`](ArkLib/Data/CodingTheory/ReedSolomon/AllRateListDecoding/AllRateAffineAgreement.lean).
For every positive gap, they choose `N`, `d`, and positive `C` before the block length,
rate, field, evaluation set, or received family. Characteristic zero or characteristic
at least `n` suffices; in particular arbitrary prime-field evaluation sets with `q ≥ n`
are covered.

For every line `f + z*g`, at most `C*n^(d+1)` challenges are exceptional. Outside that
single set, every degree-`<k` polynomial with at least `k + δ*n` agreements decomposes
into a base-field pair whose common agreement set is **exactly** the original full
agreement set. Over a finite field, the line MCA error is at most `C*n^(d+1)/q`.
For every positive affine dimension, the affine MCA error is at most
`C*n^(d+1)/(q-1)`, independently of dimension, with exact constituent witnesses.

`PrescribedLineMCA` retains `d = ceil(exp(6.76/δ))` for `0 < δ < 1/4`, prescribed
multiplicity and `n ≥ 8m`, with an explicit, coarser gap-only prefactor. The public
all-positive-gap wrapper uses a smaller gap when necessary. It does not claim the
paper's sharper prefactor or its intermediate-gap order-one refinement.

The construction is unconditional: actual symbolic interpolation, regular-stage
coverage, Taylor reconstruction, component recognition, excluded incidence, finite
pair counting, uniform exceptions, all-rate parameters, and base-field descent are
connected. `SymbolicCertificateMCA` retains the actual stage orders and exponent-cap
metadata. `RegularSymbolicLineMCA` keeps arbitrary `k ≤ L ≤ A` and the `n-L` accidental
challenge term. Only the convenient final corollary coarsens these data.

The chronological checkpoint descriptions below describe their historical frontiers,
not current open obligations. No decoder or cost-model implementation was replaced.
Remaining paper work includes sharper MCA constants and newer low-order/interleaving
refinements; these are not prerequisites for the qualitative all-rate MCA endpoint.

Final validation: `./scripts/validate.sh --axioms` passed on September 5, checking
30,536 declarations across 1,100 modules with no new admission/axiom taint.
Both public endpoint statements received independent review of their quantifiers,
threshold conversion, exceptional-set uniformity, and exact agreement witnesses.
Their axiom cones contain only `propext`, `Classical.choice`, and `Quot.sound`.
The repository still contains pre-existing unrelated admitted declarations; none is
a dependency of these endpoints. All three bounded MCA worker lanes have stopped.

### Fourth checkpoint: actual chart counts and witness transport

`CorrelatedPairChartCounting` proves the finite admissible-pair bound at one common
scalar. It derives injectivity from all reconstructed coefficients, without assuming
the pairs solve the full differential equation. `SourceChartIncidence` instantiates
excluded incidence with the actual admissible-pair graphs, discharging all joint-degree
and component-recognition hypotheses from the source jet-degree/height bounds.

`SymbolicTaylorWitnessEmbedding` puts any finite family of actual, challenge-dependent
regular solutions at one common center. It proves their chart equations, reconstructed
polynomial equality, and exact agreement-cut semantics. `SymbolicCertificateStages`
connects the existing interpolation certificate to regular-stage coverage;
`SymbolicCoefficientExtension` transports symbolic coefficients to extension fields.

Remaining assembly: finite bad-witness counting, one global exceptional set for each
regular symbolic equation, union over actual derivative stages, and all-rate parameter
instantiation. The current three lanes own respectively bad-witness counting, the
global regular-equation exception set, and elementary all-rate budget arithmetic.

Fourth-checkpoint validation: full `./scripts/validate.sh --axioms` passed
(30,497 declarations across 1,090 modules; no new axiom/admission taint).
Independent reviews covered all-coefficient pair-counting injectivity, certificate
stage coverage, field-extension transport, and the actual witness/degree interfaces.

### Third checkpoint: components and hypersurface incidence

The component-recognition bridge is now proved in `SourceComponentRecognition` and
`SourceComponentAgreement`: a positive-dimensional regular prime containing the
high cuts and any `L ≥ k` agreement cuts yields a base-field pair with at least `L`
common agreements. Its initial equation, high cuts, and **all** reconstruction
coefficient errors restrict to zero along the pair graph; its restricted separant
is nonzero. These are derived from actual source equations, not assumed graph laws.

`SymbolicJetPrefix` transports each symbolic chain equation to its actual highest
order before specialization, preserving coefficients, degree caps, height, and
the selected separant. `AffineHypersurfaceCutFamily` proves retained-component
coverage, dimension, degree potential, and excluded incidence for a concretely cut
hypersurface. In joint challenge/jet coordinates its exponent is `r + 1`.

Still in progress: the specialized source-incidence theorem, admissible-pair
counting at one scalar, and a common-center embedding of finite witness families.
Then assemble stage exceptions and instantiate the all-rate theorem. No full-MCA
endpoint is claimed by this checkpoint.

Third-checkpoint validation: full `./scripts/validate.sh --axioms` passed
(30,449 declarations across 1,085 modules; no new axiom/admission taint).
The generic hypersurface incidence argument and concrete component recognition
were independently reviewed, including empty-coordinate and arbitrary-threshold cases.

### Second checkpoint: symbolic degrees, stages, and exact pair exceptions

The all-rate transfer remains the critical path. Sharp concrete numerical constants
are deferred. Keep the actual active derivative order and every individual exponent
cap in the stage data; keep the agreement threshold `L` free. Each retained pair
contributes at most `n - L` accidental challenges, not `n`.

The second checkpoint adds the following proved interfaces:

- `SymbolicTaylorHeight`, `SymbolicTaylorDegree`, and `SymbolicTaylorCutDegree`:
  joint challenge/jet degree bounds for the actual symbolic recurrence and cuts,
  derived from the source coefficient height and jet degree at a constant center.
- `SymbolicTaylorCuts` and `SourceGraphRecognition`: actual regular Taylor points
  with high-coefficient cuts and a common `k`-sample reconstruct one base-field pair,
  uniformly in the challenge, with all `K` cleared coefficient identities.
- `SymbolicSeparantChain`: an actual finite symbolic derivative chain, strictly
  decreasing jet degrees, nonincreasing active orders, per-variable selection caps,
  and uniform regular-stage coverage outside at most `h` terminal-obstruction roots.
- `CorrelatedPairExceptionalSet`: one exceptional set for a finite retained pair
  family, of size at most `pairs.card * (n - L)`, with equality of the full agreement
  sets outside it. The single-pair bound retains `n - common.card`.

Full smaller-gap MCA is **not yet proved**. The next dependency chain is component
recognition (including all coefficient identities and the restricted separant),
counting admissible pairs at one common scalar, excluded incidence in joint source
space, and assembly over actual-order stages. Only then instantiate the all-rate
parameters and transfer from lines to affine families. No completed capacity proof
or decoder implementation needs replacing.

The three current worktrees are `ArkLib-mca-degree-epoch2`,
`ArkLib-mca-cuts-epoch2`, and `ArkLib-mca-descent-epoch2`; integration stays in
`ArkLib-mca-integration-epoch1`. Each has separate writable build outputs.
The chronological first-checkpoint record below remains useful background.

Second-checkpoint validation: full `./scripts/validate.sh --axioms` passed,
including source policy, warning budget, compiled runtime fixtures, import boundaries,
and the certified axiom sweep (30,396 declarations across 1,081 modules; no new
axiom or admission taint). Independent review covered degree/challenge retention,
coefficient-height preservation, graph recognition, and the `n - L` bound. The
parent also reviewed the actual symbolic descent and its uniform exceptional set.

This section supersedes the historical worktree assignments below. The current
base is checkpoint 1, `0dbbcd160468d441ce4d85e2b3528104137df819`: mathematical
capacity lives in `CapacityList.lean`, separately from decoder execution.
The sole final integration branch remains `quang/all-rate-rs-capacity-formalization`.

The first MCA checkpoint proves three parallel prerequisites plus the
parent-owned graph-pullback bridge:

| Lane | Owned surface | First acceptance condition |
|---|---|---|
| Symbolic Taylor | `SymbolicTaylorNumerator` and pure-ring substitution naturality | Polynomial specialization commutes with the concrete recurrence |
| Incidence | `AffineAgreementIncidenceExcluded` | Dimension induction with hereditary exclusion, including empty and zero-dimensional cases |
| Correlated pairs | `CorrelatedPairFamily` | Finite sample cover and simultaneous injectivity at a challenge outside finitely many collisions |
| Integration | `AffineGraphPullback` | Vanishing on a positive-dimensional regular graph gives polynomial identities and a nonzero restricted denominator |

Each worker uses a separate `ArkLib-mca-*-epoch1` worktree and writable build
directory. Integration and complete validation belong to the parent; algorithmic
machine files are outside these lanes. No compatibility facade is planned.

Checkpoint validation: combined `./scripts/validate.sh --axioms` passed; the
library sweep checked 30,306 declarations with no new axiom/admission taint.
Principal new exports use only `propext`, `Classical.choice`, and `Quot.sound`.
Source-trust inventory found no added admissions or native-trust constructs.
Independent review covered incidence, graph pullback, pair families, and
symbolic recurrence transport. Scratch specialization tests cover disappearing
coefficients and zero separants. Existing capacity statements and proofs are unchanged.

The revised route counts directly in joint challenge/initial-jet space. It avoids
image-closure, generic-fiber, and multigraded intersection machinery. Its target
is the same all-rate MCA conclusion and `C_delta*n^(d+1)` exponent, initially
with a larger explicit prefactor than the manuscript's sharper transfer bound.
For jet degree `nu`, challenge height `h`, and `M=nu*(nu+1)/2`, the proposed
sufficient prefactor is

```text
h + (M + nu*h) * (2*(2*nu + 2*h - 1)/delta)^(d+1)
  + M * (2*(2*nu - 1)/delta)^d.
```

This formula is a reviewed implementation target, not a proved Lean MCA theorem.
The existing displayed sharper constant is not claimed verified by this route.
Source-component recognition must establish all reconstructed Taylor coefficient
identities; initial jets alone are insufficient. Relevant pairs are counted at
one scalar in an infinite extension avoiding finitely many collisions and
separant roots, using the existing finite regular-high-cut-jet theorem.

After these prerequisites: prove joint degree bounds and source recognition;
assemble excluded incidence and pair counting; handle symbolic separant stages;
then produce one exceptional set valid for every close polynomial and instantiate
the prescribed parameters and affine-family transfer. Small message dimensions
can use direct sample double-counting. Full smaller-gap MCA remains unfinished.

## Priority and acceptance boundary

This track is active in parallel with the decoder, by Quang’s explicit authorization on
September 4, 2026. The Astra/medium strengthening coordinator may use three bounded
Sol/high workers with no further nesting. The current three decoder workers keep their
assignments. All strengthening edits belong to the private `quang/rs-strengthenings`
worktree, starting at `77ad3e8b12f5c0537f99aaba1d10511edd5e4e4f`; central owns
the sole final integration branch `quang/all-rate-rs-capacity-formalization`.
The pre-strengthening decoder theorem and its exact program cost remain separate
obligations. No geometric result is a prerequisite for that decoder milestone.

The decoder target is the manuscript at commit `26e8ea0` in the private
`all-rate-rs-list-decoding` repository: `shared/main-theorem.tex` and
`shared/main-theorem-bounds.tex`. It includes bit-operation bounds, not merely
field-operation counts. The existing machine ledger, its base-field lowering,
and a bit-cost implementation/refinement are separate obligations. A polynomial
overhead in `q` can suffice for the headline bound; an efficient `poly(log q)`
scalar implementation is not the only possible proof route. Any such route must
still account for data access and allocation without losing the intended exponent.

The reference Lean checkpoint for this plan is `3f2cac5d`. Its prepared-decoder
exactness is proved under explicit setup/parameter hypotheses; it is not the
completed algorithmic theorem. See [the active tracker](ALL_RATE_RS_FORMALIZATION.md).

## Manuscript snapshot read

The canonical writing was resolved through the paper-note writings index. It is
`~/Documents/Research/all-rate-rs-list-decoding/main.tex`, which now includes
`core/geometric-list.tex`, `core/symbolic-interpolation.tex`, and
`core/correlated-agreement.tex`. These three new sections were read in full,
together with the main statements, decoder procedure, proof, and cost discussion.
The manuscript checkout contains uncommitted work. This plan does not edit it,
commit it, or claim that its current sources equal its Git HEAD.

Snapshot SHA-256 values, recorded September 4, 2026:

| Artifact | SHA-256 |
|---|---|
| `main.pdf` | `a435946eb586859e70eec91d409515f65efd6b1a0e8c99753f2e437c1ec8b49f` |
| `core/geometric-list.tex` | `c4d9d81d4d71964c0888a3d1bcc2fca6d392ba52381d486ffc350d1faec138a8` |
| `core/symbolic-interpolation.tex` | `19277c99aa4094f59f88a97fb30e3e57c97f4fa63fb4d044b1a6640b1165ac00` |
| `core/correlated-agreement.tex` | `26ca7cb6256fa69ed27aa2c75610db3046d06c27276d7ddcee07a23239dc7dbe` |

The hashes identify what was planned against; they are not verification claims.
Reconcile any later paper edits before freezing the corresponding Lean statements.

## Stronger endpoints to preserve

Write `d = ceil(exp(6.76 / delta))` and `m = ceil(100*d^2*H_(d-1))`
for `0 < delta < 1/4`.

1. **Field-independent exact-list cardinality.** For `n >= 8m`, distinct
   evaluation points, degree `< k`, and integer `k + delta*n <= A <= n`, prove
   `|List(y,A)| <= 4*m^2*(4*m/delta)^d*n^d`. Cover prime fields `q >= n`;
   also state the paper's field-general version in characteristic zero or `> n`.
   For infinite fields use a proved finite set/cardinality, never the default
   value of `Set.ncard` on an infinite set. `A > n` gives the empty set.
   Combine with the old bounds by taking a minimum. Do not improve the decoder
   runtime merely because fewer candidates survive agreement filtering.
2. **Mutual correlated agreement on a line.** Fix `f,g` first. Produce one finite
   exceptional set `E` that works simultaneously for every challenge `z` outside
   it and every close polynomial `P`. There must be degree-`<k` witnesses `F0,G0`
   with `P = F0 + z*G0` and **equality of the full agreement set** with the common
   agreement set of `F0,G0`. Merely having `A` common agreements is weaker.
3. **Explicit line bounds.** Small gaps: `N_CA=8m`, `E_delta(n)=C_delta*n^(d+1)`
   with the displayed constant in `eq:ca-small-gap-constant`. Intermediate gaps
   `1/4 <= delta < 1/2`: order one, `N_CA=512`, and the paper's explicit quadratic
   bound. Gaps `>=1/2`: `E_delta(n)=2n`, `N_CA=1`, every characteristic.
   Keep these CA parameters distinct from the order-zero decoder branch.
4. **Affine families.** For `s>=1`, at most `s*E_delta(n)*q^(s-1)` exceptional
   parameter tuples; preserve equality of full and common agreement sets for all
   `s+1` witnesses. Derive probability `<= s*E_delta(n)/q`, with the usual
   additional trivial upper bound one. Bridge to ArkLib's actual MCA error API.

These are paper claims to formalize, not results already certified by Lean.

## Dependency graph

```text
Existing interpolation and regular Taylor-lift algebra
      |                          |
      |                 rational coefficient degree recurrence (R)
      |                          |
      |        geometric degree/cuts (G) --> rational image (I)
      |                 |                  |
      |           agreement incidence (A) + root envelope (V)
      |                                    |
      |                             FIELD-INDEPENDENT LIST
      |
polynomial kernel height (H) + translation/rank scalar extension (S)
      |                         + quantitative band margin (M)
      +-------------------------+
                   |
          symbolic interpolation (Q)
                   |
R + bidegree image (B) + generic-fiber compatibility (F)
                   |
            joint root envelope (J)
                   |
A + J + graph-line recognition/accidental roots (L)
                   |
            MUTUAL LINE AGREEMENT
                   |
 function-field descent + parameter induction (P)
                   |
         AFFINE MUTUAL AGREEMENT + MCA API bridge

H --> independent all-characteristic half-gap line proof
H + order-one local rank/counts --> intermediate-gap symbolic certificate
```

Geometry does not feed back into the old decoder. The field-independent list
can land before the joint-envelope and correlated-agreement work.

## Work packages and falsifiable acceptance criteria

| ID | Mathematical contract and source locator | Dependencies / owner guidance |
|---|---|---|
| H | `lem:polynomial-kernel-height`: polynomial matrix entry degree `<=b`, rank `s<N` over `F(Z)`, nonzero kernel vector with entry degree `<=floor(sb/(N-s))`; primitive entries generate the unit ideal and never all specialize to zero over any extension | Polynomial coefficient spaces, actual rank-nullity, row-span extension, PID/gcd. Treat `s=0`, `b=0`, zero entries, and strict `N-s>0` explicitly. No executable kernel-height algorithm is required by the new list/CA statements. |
| R | `eq:geometric-lift` and `eq:geometric-numerator-degree`: actual rational Taylor recursion `c_(r+h)=A_h/S^(2h-1)`, numerator degree `<= (2h-1)(v-1)+1`, plus challenge-degree `<= (2h-1)*zeta` | Reuse regular-lift leading coefficient and separant algebra. Prove the Taylor-weight restriction on every residual monomial. Denominator nonvanishing and `H=0` are explicit cases. |
| G | Mixed-dimensional total degree, finite irreducible decomposition, proper hyperplane cut, linear intersection, and refined Bezout inequality for retained components | First audit pinned Mathlib. Choose a concrete affine algebraic-set/ideal representation and a proved degree, not a degree function carrying the desired inequalities as axioms. Largest infrastructure risk. |
| A | `lem:agreement-incidence`: finite qualifying set outside excluded positive-dimensional subsets; bound `Delta*((n-L+1)/(A-L+1))^s` | G. An abstract induction lemma may be proved early, but it does not discharge G. Cover reducible sections, finiteness before cardinal arithmetic, repeated hyperplanes, and `1<=L<=A<=n`. |
| I | `lem:rational-image-degree`: closure of rational image has dimension `<=s`, total degree `<=Delta*b^s` | G, constructibility and generic-section argument. Permit positive-dimensional fibers; do not replace the claim with a generically finite special case. |
| V | `thm:geometric-envelope`: contain actual root coefficient vectors with dimension `<=d` and degree `<=mu^2*(1+2K*(mu-1))^d` | R+I, actual descending separant chain, transcendental center and algebraic extension. Distinguish `mu=0` (no roots) from `mu>=1`; use characteristic zero or `>max(K-1,mu)`. |
| O | `cor:geometric-actual-degree`, `cor:field-independent-output` | V+A+Vandermonde uniqueness. Intersect with actual degree-`<k` space before applying incidence, retaining agreement gap `A-k`, not ambient gap `A-K`. Reuse actual interpolant or field-general band witness. |
| S | `prop:symbolic-interpolation`: polynomial challenge matrix, rank stable under translations/scalar extension, degree of entries `<=nu`, primitive nonzero specialization and multiplicity soundness | H + existing local constraints. State soundness after arbitrary coefficient-field extension, not only base challenges. Preserve total jet degree, not just individual degrees. |
| M | `cor:symbolic-band`: `N > (456976/455625)*n*r0` and challenge height `<(455625/1351)*nu<338*nu` | Reuse numerical endpoint inequalities in the 6.76 proof; extract the stronger margin before coarse rounding. Strict dimension surplus alone is insufficient. Include `r0=0`. |
| B | `lem:bidegree-image`: `alpha*b1^(d+1)+(d+1)*beta*a1*b1^d` | G+I plus a justified multiprojective degree or elementary equivalent. No unsupported Chow-ring calculation; zero bidegrees, vertical components and positive-dimensional fibers need coverage. |
| F | Generic fiber of rational image closure equals closure of generic image, with degree/dimension control | Constructibility, dominance/base extension, excluding vertical components. Never assert equality for every special fiber. Freeze this statement before relying on J. |
| J | `lem:joint-envelope`: joint degree Delta and generic-fiber degree `<=nu^2*b^d`; terminal exceptional set size `<=zeta` | R+B+F+actual separant chain. Handle jet-independent Q and specialization where the terminal polynomial vanishes. |
| L | `thm:symbolic-transfer`: graph lines, generic-fiber line count, off-line incidence count, accidental-agreement exclusion | J+A+Vandermonde. All common witnesses descend to the base field. The exceptional set is independent of the chosen close polynomial. |
| C | `thm:ca-explicit`, small-gap and intermediate-gap constants | S+M+L; independently formalize order-one support/rank counts `28152`, `1904`, `120700`, and challenge height `<=1449`. Keep `n>=512` separate from decoder `N=1`. |
| U | Half-gap line theorem in every characteristic | H+ordinary polynomial root bounds/Vandermonde; independent of G through J. Prove V is nonzero, choose usable positions, and exclude accidental roots. This can be an early complete CA endpoint. |
| P | `cor:affine-mutual-ca` and probability/MCA translation | L/C/U as appropriate; multivariate rational function field, coefficient independence, witness descent and induction. Preserve exact sets, not just existence of witnesses at one parameter tuple. |

## User-authorized parallel strengthening team

This team has three Sol/high workers plus its Astra/medium coordinator, with no worker
nesting. It operates alongside, without redirecting, the existing decoder team.
The rows below are dependency waves, not promised one-epoch completions.

| Wave | Lane A | Lane B | Lane C | Central |
|---|---|---|---|---|
| Foundations | H then S | R, including bidegree recurrence | G inventory and smallest concrete degree/cut core | Freeze endpoints, reuse/API audit, incidence induction A |
| First complete outputs | M, then U | V after I is available | I, then missing G refinements | O and field-independent exact-list assembly |
| Correlated geometry | Order-one counts and C parameters | J after B/F | B and F, split by independently provable prerequisites | L, graph-line/base-field descent and exceptional sets |
| Final synthesis | P/function-field induction | Statement/countermodel audit | Geometry/degree audit | MCA probability bridge and public packaging |

If geometry stalls, A and B can finish H/S/M/U/R and exact order-one certificates
without waiting. Do not keep creating downstream conditional wrappers while G,
B or F remains unproved. Identify and assign the smallest missing prerequisite.
Additional collaborators can take unclaimed prerequisites only after central
ownership coordination; the local three-worker concurrency cap is unchanged.

No credible epoch count for the geometric track is available yet. The decoder
estimate does not include it. G/B/F require an infrastructure audit before sizing.

## Pinned-library findings and reuse limits

At the current dependency pin, Mathlib has `RatFunc`, multivariate rational
function rank, algebraic independence, Nullstellensatz, rational maps, and
`PrimeSpectrum.isConstructible_comap_image` (Chevalley for finite presentation).
These are ingredients, not the paper's rational-image degree theorem.
The inspected `RingTheory/Polynomial/HilbertPoly.lean` handles coefficients of
`p/(1-X)^d` and explicitly leaves graded-module Hilbert polynomials as a TODO.
`AlgebraicGeometry/AlgebraicCycle/Basic.lean` provides cycles and pushforward;
it is not a ready-made multiprojective intersection-degree package.
A targeted search did not locate the required refined geometric Bezout bounds.
Do not confuse the available PID/Bézout-ring API with geometric Bezout.

ArkLib already has `ProximityGenerator/Basic.lean` (`IsMCA`, `mcaError`,
`IsMCAGenerator`) and `ProximityGap/Errors.lean` (`epsMca`). `IsMCA` is the
**bad event**, not the desired good property. Prove that this bad event is
contained in the finite exceptional set before deriving error bounds.
The exact-set theorem is stronger than the API's projection statement and should
remain separately visible. Reuse actual definitions rather than adding a second
incompatible meaning of correlated agreement.

## Statement and proof audit checkpoints

- Excluded incidence sets must contain all positive-dimensional irreducible
  subsets supported on enough hyperplanes, not merely the top-level components.
- Algebraic degree must count lower-dimensional components; hyperplane sections
  may be reducible or have unexpected dimension.
- A transcendental center is chosen over a field containing the root coefficients.
  State the extension embeddings and coefficient-space maps explicitly.
- The generic-fiber degree is not a uniform bound on special fibers. Fiber/image
  closure interchange is a theorem to prove, not a simplification rule to assume.
- The characteristic-zero branch must be a disjunction or separate theorem;
  `ringChar F > bound` alone excludes it.
- The affine induction applies the line theorem over a rational function field.
  For the small-gap `q=n` prime endpoint, prove the exact condition
  `char F > max(K-1,nu)` over that function field too; a theorem restricted to
  prime fields cannot simply be reapplied to it.
- For every good challenge, quantify over **all** close polynomials. Witnesses
  may depend on the challenge and polynomial, but the exceptional set may not.
- Equality is of the witnesses' common agreement set. Individual witnesses may
  agree on additional coordinates; forbidding that would strengthen the claim.
- Preserve the original constants when reasonably direct. A coarser polynomial
  bound can be an explicitly named intermediate theorem, never a silent replacement.
- Cite the paper's source labels and its Heintz/Fulton/Stacks/Milne dependencies
  at the lemmas that use them. Prove or import every needed geometric fact;
  an assumed geometry interface does not make an unconditional RS theorem complete.
- Each checkpoint needs strict builds, source/import checks, principal axiom
  footprints and nonvacuous boundary tests. Final closure requires the repository
  full gate and an independent statement audit. No new axioms/admissions are allowed.

## Active source reconciliation and ownership (September 4, 2026)

The current `core/correlated-agreement.tex` SHA-256 is
`2edc6d8dfce412b59b1579c5260d929aa78d2a57020c0a8ce34443eb6b6f18d2`.
The geometric-list and symbolic-interpolation hashes above are unchanged.
The revised affine proof uses `lem:line-affine-mca` (BCGM25 Lemma 7.1):
exceptional cardinality at most `E_delta(n)*q^s/(q-1)`, probability at most
`E_delta(n)/(q-1)`, independently of `s`; the line retains `E_delta(n)/q`.
This implies the earlier `s*E_delta(n)*q^(s-1)` contract for `s>=2`, since
`q/(q-1)<=2<=s`. The exact full-set equality follows from subset MCA and
RS uniqueness on at least `k` positions. The former function-field induction P
is superseded by this shorter route, not an additional prerequisite.

Pinned ArkLib already proves the core reduction in
`AffineMCALemmas.exists_line_bound` and
`AffineMCAMain.isMCAGenerator_affineSpaceGenerator_of_affineLineGenerator`
in `ProximityGenerator/AffineGenerator.lean`. Audit its axiom cone and reuse it.
Do not reimplement this averaging/quotient argument.

| Owner | Exclusive active scope | Acceptance |
|---|---|---|
| Kernel worker | New `ArkLib/ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean` | Genuine coefficient-space kernel vector, first row-count bound, then fraction-field rank bound; no assumed kernel existence |
| Half-gap worker | New `AllRateListDecoding/HalfGapCorrelatedAgreement.lean` | All-characteristic line endpoint, one finite set before all challenges and polynomials, cardinality `<=2n`, exact full-set equality |
| Independent geometry auditor | Read-only G/I/B/F and source audit | Exact pinned declarations; smallest absent substantive prerequisite; no assumed degree structure |
| Coordinator | This plan, `ALL_RATE_RS_STRENGTHENINGS_PROGRESS.md`; unclaimed substantive prerequisite selected after audit | Integrate and independently check worker evidence; coordinate shared edits and full builds |

The shortest central route still requires concrete degree and proper-cut theory G,
then rational image I together with rational lift R, root envelope V, and incidence A.
Small-gap CA additionally requires joint/generic-fiber geometry B/F/J.
The independent half-gap lane does not close these obligations.

## Hard sprint cutoff (supersedes persistence instructions)

Quang authorized a four-hour sprint starting September 5, 2026, 05:51:04 UTC.
Stop new proof/implementation at **09:21:04 UTC** (02:21 Phoenix). Deliver verified
commits and separately preserved unfinished work to central by **09:36 UTC**, then
stop. The final deadline is **09:51:04 UTC** (02:51 Phoenix), with no extension or
automatic continuation. Read the clock before new substantial objectives.
The coordinator must confirm all three workers have stopped at freeze/end.
The read-only geometry worker remains reserved for independent integration audit.

Central owns the final 30 minutes for consolidation, validation, push, and report.
The strengthening team must coordinate its full gate to avoid contention.

## First verified proof frontier and shortened geometric route

Targeted strict checks and independent source review have passed for H (including
primitive coordinates and nonvanishing over arbitrary extensions), the unconditional
all-characteristic U endpoint, and the canonical MCA-to-exact-set bridge. Full repository
validation passed privately and centrally. Checkpoint `7898fefd` is committed and
integrated by the central coordinator; the remaining geometric list theorem is still open.
The U theorem proves the slightly stronger integer threshold `A>=k+floor(n/2)`
for `k>0` and `A<=n`, with one finite exceptional set of size at most `2n` before
all challenges and close polynomials. Its odd-length surplus is `k`, not `k+1`;
`k*height<=n` is sufficient.

For the field-independent list bound, count directly on regular rational Taylor charts.
A stage of jet degree v and highest active order r<=d starts on the principal-open
hypersurface `T(a,u)=0, S(a,u)!=0` in r+1 initial coefficients. The rational map
retains those coefficients, so is injective. Pull back high-coefficient equations
`c_k=...=c_(K-1)=0` first, then pull back agreement equations. All have degree<=b.
The potential `sum(deg(C)*b^dim(C))` is nonincreasing under a degree-b cut: a
retained component costs nothing, and each proper cut has children with dimension
at most dim(C)-1 and summed degree at most b*deg(C). Discard children lying entirely
on the denominator-zero locus after **every** cut; they contain no requested points.
Vandermonde uniqueness then excludes positive-dimensional retained sets supported
on k agreement equations. Incidence induction yields the original v*b^r factor.
Thus list counting can bypass rational-image closure I and the V envelope; it still
requires actual refined Bezout, dimension drop, and finite component theory.

The independent pin audit recommends a concrete filtered-Hilbert route to Bezout:
finite total-degree pieces of polynomial quotients; eventual Hilbert polynomial;
leading-term degree; proper principal-cut degree inequality and minimal-prime
additivity. Mathlib has finite minimal primes, primary decomposition, principal
ideal height, and homogeneous polynomial pieces, but lacks the required quotient
Hilbert-polynomial/multiplicity stack. A fabricated degree-law structure is not an
acceptable substitute.

Current frontier: checkpoints `7898fefd` and `f34ca271` passed private and central
full validation. R literal numerators, solution comparison, common-denominator chart,
and high/agreement-cut uniqueness are proved and entering the third gate. S concrete
symbolic matrix, extension nonvanishing, local rank/base-change, and soundness are proved;
the stacked-band adapter and final prescribed symbolic certificate are next. Coordinator
owns actual geometric component/cut infrastructure; auditor independently reviews proofs
and owns only the small falsifying canary module. The quotient Hilbert-polynomial and
refined degree/Bezout layer remain open, so the general list and remaining MCA endpoints
are not claimed. Active work remains ignored scratch during each frozen full gate.
