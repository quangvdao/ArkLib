---
kind: paper
bibkey: DKTZ26
title: "Reed--Solomon List Decoding up to Capacity at Every Rate"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: null
source_metadata: ../sources/DKTZ26/metadata.yml
status: active-private-manuscript
---

# DKTZ26

## At A Glance

Dao, Kominers, Thaler, and Zheng strengthen the hidden-derivative method to every fixed rate and
every fixed positive capacity gap over prime fields. The paper also sharpens the quantitative
parameters, root bounds, endpoint analysis, and characteristic limitations.

## What ArkLib Uses From This Paper

- rate-uniform ambient padding and the finite-cover alternative;
- the order-zero proof for gaps at least one quarter;
- the asymmetric-band certificate with constant `169/25`;
- primitive, separant, resonance, and exact local-rank refinements;
- exact-capacity and inverse-gap lower bounds;
- the linearly-growing-characteristic extension and Frobenius-plane obstruction.

## Main ArkLib Touchpoints

- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/Capacity/Basic.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/`
- `ArkLib/Data/CodingTheory/ReedSolomon/ListDecoding/Capacity.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/CorrelatedAgreement/Capacity.lean`
- `ArkLib/Data/CodingTheory/ReedSolomon/CorrelatedAgreement/AffineCapacity.lean`

## Version Notes

The formalization is synchronized to private manuscript commit
`9e4d6488ead94be47cca69e5be915b5667143b66`. Recheck source correspondence before using
later manuscript changes for quantitative or refinement work.

## Known Divergences From ArkLib

The first ArkLib capstone intentionally permits coarser qualitative constants. Optimized results
are separate parameter packages layered over the stable qualitative proof interfaces.

## Open Formalization Gaps

The qualitative all-rate line and affine MCA conclusions are proved in the modules above.
Sharper MCA constants and low-order refinements are separate obligations. The executable
machine and cost work remains tracked in the
[algebraic-machine plan](../../design/rs-algebraic-machine-plan.md); the mathematical
agreement theorems do not assert a running-time bound.

## Source Access

- Source metadata: [`../sources/DKTZ26/metadata.yml`](../sources/DKTZ26/metadata.yml)
- The source repository is private; the pinned commit is recorded above for authorized collaborators.
