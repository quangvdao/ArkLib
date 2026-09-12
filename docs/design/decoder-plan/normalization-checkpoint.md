# Saturated ordinary normalization checkpoint

The collection incorporates source commit
`672739e2a9c2bcb870d6afc13bdc44e925772eda`, based on
`e065bd441a1ab3cce5cc11d569d23fa9cf1c65a8`, from
`quang/decoder-ordinary-normalization` in `quangvdao/ArkLib`.
This is a successful-output checkpoint, not full normalization or decoder completion.

## Included source and provenance

Five production modules and their matching tests live under
`ArkLib/Data/Polynomial/FunctionFieldAlgorithms/` and
`ArkLibTest/Data/Polynomial/FunctionFieldAlgorithms/`:

| Module | Established boundary |
| --- | --- |
| `CanonicalRepresentative` | Computable canonical stored-fraction representatives |
| `ClearDenominators` | Computed denominator clearing, primitive descent and global divisibility bridges |
| `BivariateReducedSupport` | Executable bivariate conversion and checked joint Frobenius contraction with graph and degree lemmas |
| `RegularCenterObstruction` | Computed obstruction, degree bound and nonvanishing-to-regular-fiber/inverse guarantees |
| `OrdinaryNormalization` | Saturation, recursive radical execution, separable-part execution and actual returned-output certificates |

The checkpoint includes byte-identical copies of N1
`11aa1eaf1813645ab44b03da4d325c59321539be` and N2
`bce6be3114ae72da04539e11536fdbe66a07855f`. Do not apply those files again.
The separate D1 driver `5af1d00c2ae35145d7f56cc5eafb73989d95ad96` is not part of this collection.
An extra N2 push to canonical upstream was reported by its author; it is preserved and is not
an upstream merge or an integration dependency. Collection publication targets the personal fork.

## Executed program and proved boundary

`OrdinaryNormalization.run` converts the actual interpolant, removes content, executes
`radical`, then computes `separablePart` and the stored obstruction. Saturation uses
`G = gcd(H, H_X, H_Y)`, `V = H/G`, and `R = H/gcd(H,V^ell)` before joint-root recursion.
Zero input, constant regular output, normalized output and arithmetic failure remain distinct.

`run_normalized_provenance` identifies the actual input and radical call.
`run_normalized_divisibility_bounds` proves global regular-output divisibility and X/Y degree
bounds **relative to the computed support**. `run_normalized_isPrimitive`,
`run_normalized_coprime`, `certifiedInput`, `run_normalized_obstruction_degree` and
`run_normalized_fiber` connect successful output to the obstruction producer and regular fibers.

There is no theorem yet identifying the computed support with the original input's radical.
Consequently the bounds and graph guarantees are not yet original-input guarantees.
`runCertified` binds the characteristic to the field and accepts an inverse-Frobenius law when
`p` is at most the input Y-degree; it does not prove the algorithm cannot fail.

## Subsequent correctness closure

The [three-track collection](three-track-checkpoint.md) includes Personal 1's
`6d4c45aff0fda14bc9e992538ec8ded6d57cc531`, closing the generic radical, no-failure,
original-input graph/degree and constant-case obligations listed below. Personal 3's concrete
coefficient inverse is also collected. Final decoder application composition remains separate.
The following section records the boundary at the original successful-output checkpoint.

## Remaining producer obligations at the original checkpoint

Personal 1 next closes the full radical invariant and no-failure theorem under primitive,
nonzero, degree-bounded input assumptions. Then connect `runCertified` to original-input graph
preservation, divisibility and both degree bounds, and prove the constant branch has no polynomial
graph for nonzero original input. Zero input cannot be classified as having no graphs.

Personal 3 supplies the concrete polynomial-basis inverse Frobenius. Personal 4 owns application
composition, actual center selection and final decoder exactness. No supplied support correctness,
success result, good center or coverage hypothesis replaces its assigned producer.
The separate positive-order decomposition and norm obligations remain open.

The revised zeroth-order specification is paper commit
`b1be8b89069542faacac40a7e92068857b43e97a`: supplied polynomial-basis F_q, q >= n,
unrestricted characteristic and extension degree. Positive-order decoding retains prime-field
scope. The terminology candidate cover describes existing one-way coverage contracts.

## Collection validation

The shared agreement-recovery executable registers all five new namespaced runtime suites.
Cases distinguish visible-factor saturation, p and p-squared multiplicities, binary mixed
inseparability, denominator-zero fibers, meeting factors, constant regular output and zero input.
The umbrella is regenerated from tracked production sources.

Before publication the collection runs `./scripts/validate.sh --axioms` with these registrations,
unchanged dependency pins and unchanged axiom baseline, and independently reviews the exact
source checkpoint. The source author's passing gate is evidence for that slice, not a substitute
for collection validation. Exact collection SHA and validation evidence are recorded in the
coordinator handoff.
