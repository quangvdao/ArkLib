# Decoder realignment adoption manifest

This is the append-only source manifest for the September 13 decoder realignment. Each adoption
entry records immutable inputs and the coordinator commit that combines them. Later entries may
supersede a validation or publication state, but do not rewrite source provenance.

## I0: P1/P4 interface union

| Item | Exact value |
| --- | --- |
| Paper specification | `24276c570658604e12dd9c3d119f2b6f3200b54d` |
| Personal 4 source | `fc558221a8a37bbead025fd807409308d602e363` |
| Personal 1 source | `46dd735e71c2ca0874faf752bf12ed4d92f839c6` |
| P1/P4 merge base | `c1fe369f08b5a75c9b2ca5771424ee8b5a5e26c2` |
| Coordinator merge | `be8f0b2a9e97ce82451fdc37c6bb95b9dca4128f` |
| P3 source awaiting union adoption | `67bf095639d8323f22bb7ca2bbb2748ea16c1e39` |
| P4 topic branch | `quang/decoder-realign-p4-integration` |

The P1 head is a two-parent reviewed union. It was merged as one exact head because its histories
contain cherry-pick-equivalent component commits. Replaying those commits chronologically would
duplicate implementations. The merge contributes the repaired reduced-denominator consumer,
first-order and recursive general component construction/readiness, universal recovery, agreeing
label preservation, and the exact Gabber–Galil energy theorem. It does not modify the toolchain,
Lake manifest, generated umbrella or central runtime.

The P4 parent contributes the completed supplied polynomial-basis zeroth decoder, one-chart Taylor
constructor and global contract, semantic separant traversal, computed canonical fuel, dependent
varying-order dispatch, and first-order recovery seam.

### Dependency pins

| File | SHA-256 at the union |
| --- | --- |
| `lake-manifest.json` | `01cba20b029e340aad3b21aa5887552b34a52597efed0842c942d6be14d2ebd9` |
| `lakefile.toml` | `95cd4585731c94eae5b896f4bb01777fa62400a4e107a7512980ae3e700c7a10` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

### Ownership retained for this wave

Personal 4 owns shared Fast Taylor interfaces, generic triangular and rational recurrence engines,
effective finite-field presentation adapters, zeroth-order transport, support interpolation,
public `HiddenDerivativeDecoder` composition, final higher-order materialization, generated
`ArkLib.lean`, the central runtime and integration documentation. Personal 1 owns common-center
normalization and boundary production. Personal 2 owns tower/recovery and first-order curve
candidate internals. Personal 3 owns Rojas, robust-ball selection and the direct-system
Jacobian/isolated-root bridge.

### Validation tree

The source union is `be8f0b2a9e97ce82451fdc37c6bb95b9dca4128f`. Coordinator umbrella and
runtime registration are a subsequent owned integration change. Their exact validated and
published heads are recorded in later manifest entries after the combined gate and independent
review.
