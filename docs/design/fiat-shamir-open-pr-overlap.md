# Fiat–Shamir work already in flight and the next native contract

Static source investigation, October 4, 2026. This is a reuse/planning audit, not a merge review or
new kernel/axiom validation. No source changes or reviews were posted to the authors' PRs.

## Exact reviewed stack

- [#469](https://github.com/Verified-zkEVM/ArkLib/pull/469), `dsfs-section5`, head
  `036d6f561f6e33cc02d0712095c09ebfc3f1ffb1`: Section 5 constructions and infrastructure.
- [#848](https://github.com/Verified-zkEVM/ArkLib/pull/848), head
  `1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb`, based on #469: security definitions,
  canonical single-salt FS reductions, and conditional Section 6 DSFS results.

Both PRs credit Chung Thai Nguyen, Michele Orrù and Yuxi Zheng. The reviewed stack uses Lean
4.33.1 and VCVio `eb22883264cd2fd513df4ee7db1bc5a86ec789c7`; the native integration uses Lean
4.34.0 and VCVio `6bf6c91b`. Shared mathematics is not automatically import-compatible.

## What #469 supplies

Explicit single-salt and salted duplex constructions; protocol codecs and decoding-bias interfaces;
salt encoding; protocol nondegeneracy; trace data; lookahead/backtracking/candidate extraction;
prover and trace transformations; concrete bad-event definitions and structural exclusion lemmas;
and endpoint/hybrid experiments `Hyb_0` through `Hyb_4` with quantitative interfaces.

Useful proved pieces include uniform-preimage sampling/distribution lemmas in `Preliminaries`,
structural bad-event lemmas 5.10/5.12/5.14/5.16, and protocol/trace representation laws. These are
not proofs of the corresponding whole hybrid statistical-distance chain.

`KeyLemma.lean` explicitly defers the paper-level Claims 5.21–5.24 and Lemmas 5.8/5.1. Its generic
`tvDist_hybridChain4` combines supplied distances; it does not discharge the concrete transitions.
Basic and single-salt completeness remain deferred.

The old main-snapshot audit must not be reused as a diagnosis of this PR. The reviewed branch has
explicit salts, DS-to-single-salt trace conversion, capacity-exponent error expressions and a
backtracking distinct-pair condition. It replaces the old `True` key-lemma placeholder with
meaningful experiments and an explicit unfinished proof boundary. This does not certify all
Section 5 interfaces or the paper correspondence.

## What #848 proves, and what it assumes

In `SingleSalt.lean`:

- `fsNARGSoundnessExp_eq_srExp` proves an actual game/readout equality.
- `single_salt_fiat_shamir_soundness` (lines 494–525) transports a supplied coin-bearing
  state-restoration soundness premise, preserving its error and an explicitly related prover class.
- `single_salt_fiat_shamir_knowledge_soundness_of_fixedExtractor` and its family theorem
  (lines 930–1003) transport a supplied SR knowledge guarantee; one extractor is chosen before
  the budget family. Logged transcript reconstruction and extractor-failure equality are proved.

These are substantive proved reductions. They do not derive their SR hypotheses from native
round-by-round certificates; our restoration theory addresses that complementary obligation.

`Soundness.KeyLemmaSecurityWitness` (lines 225–250) packages two unproved Section 5 obligations:
the concrete endpoint statistical-distance bound and the transformed prover's challenge-query
bound. Section 6 consumes this witness rather than establishing it.

`duplex_sponge_fiat_shamir_soundness` (Soundness:1251 onward) assumes both this witness and SR
soundness, then proves the additive `epsilon_SR + etaStarTotal` bound. The knowledge theorem
(KnowledgeSoundness:897 onward) similarly consumes a witness family and a budget-uniform SR
extractor guarantee. Neither theorem alone closes the Section 5 proof.

The knowledge statements explicitly permit randomized extractors, both prover and verifier logs,
and base-oracle access; DS trace conversion uses an additional alphabet sampler. They do not prove
the deterministic prover-trace-only extractor contract or an extraction-time bound. Preserve that
qualification when calling them adaptations of CO25 Theorems 3.19 and 6.2.

## Overlap and genuine differences

| Concern | Existing stack | Proposed native work |
|---|---|---|
| SR implies basic FS | Already proved conditionally | Reuse/generalize/transport this result; do not present a duplicate as new theory |
| Source of SR security | Explicit premise | Derive from native local knowledge certificates with quantitative query bounds |
| Protocol representation | Legacy `ProtocolSpec`/`Verifier` | Native Interaction and an explicit public-message/restoration bridge |
| Verification timing | Derive full transcript, then call verifier (`SingleSalt:157–167`) | Interleave checks and challenge queries; stop at first rejection |
| Resource theorem | Explicit prover classes and query-operation budgets | Expected weighted distinct keys of the actual stopped joint run |
| Random oracle realization | Concrete uniform instantiation samples a finite full table | Lazy shared cache, including arbitrary input domains |
| Query domain | Well-typed challenge keys; no malformed/off-image challenge queries | Explicit injective/decodable encoding and memoized off-image simulation |
| Duplex reduction | Algorithms, interfaces and conditional security already exist | Do not rebuild them; concrete Key Lemma remains a separate major proof project |

The full-table/lazy-cache distinction requires a proved bridge; it is not an automatic rewrite.
The concrete uniform table sampler is constructed using finite compatible statement, message and
challenge types (`OracleSampling.lean:206–245`, `Defs.D_IP_salted`, `Soundness.srInitDIP`).
One must not claim it already covers the native theorem's infinite input domain.

The extractor interfaces have a plausible compatible fragment: the old SR extractor receives a
full transcript, and a deterministic native backward extractor could ignore extra logs. This is
an inferred embedding, not a proved result. It requires exact transcript/seed/extraction equality,
source-observation interpretation, and one extractor uniform across budgets.

## Recommended revision to the next six-hour contract

1. Make the legacy/native semantic bridge and supplying the existing SR hypothesis explicit
   targets. Pin the exact legacy definitions and prove ordinary acceptance, knowledge failure,
   extractor identity, and query-budget transport on a named common fragment.
2. Retain stopped verification and actual expected distinct-query cost as the new general-theory
   contribution. Equality with full-completion verification concerns acceptance on rejecting runs,
   not equality of post-rejection cache/logs or charges.
3. Reuse or generalize the canonical FS-to-SR proof from #848. Prefer a shared theorem or proved
   correspondence over two permanently independent implementations. If a native port is needed
   due to legacy representation/probability differences, preserve attribution and exact scope.
4. Match the single-global-salt construction: incorporate `(statement, salt)` into native Input,
   keeping the restoration per-round salt `PUnit`. An unsalted protocol is then a specialization.
   Honest salt generation and transcript correspondence still need proofs.
5. Keep honest completeness as a meaningful SHOULD: it remains unproved in the stack. Do not
   accidentally claim the old merged #317 delivered it; that one-line change filled a default
   oracle-table value, not the final completeness proof.
6. Keep online Merkle work secondary. Do not also promise to prove the entire duplex Key Lemma
   within this six-hour run. Its forward/inverse permutation coupling and hybrid bounds are a
   distinct substantial project.

The initial next-run draft was written before this stack audit. Its mathematical stopped-cost
and native execution targets remain useful, but its reuse baseline and compiler scope must be
revised before launch. No run is started by this note.

## Selected source links

- [Single-salt construction and security](https://github.com/Verified-zkEVM/ArkLib/blob/1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb/ArkLib/OracleReduction/FiatShamir/SingleSalt.lean)
- [Section 6 soundness and KeyLemmaSecurityWitness](https://github.com/Verified-zkEVM/ArkLib/blob/1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb/ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Soundness.lean)
- [Section 6 knowledge interface](https://github.com/Verified-zkEVM/ArkLib/blob/1c5c5bd7ed9d4a6407974a12ff95893fbdbc02bb/ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KnowledgeSoundness.lean)
- [Section 5 experiments and deferred claims](https://github.com/Verified-zkEVM/ArkLib/blob/036d6f561f6e33cc02d0712095c09ebfc3f1ffb1/ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemma.lean)

## Third-run execution update

The comparison above is the pre-run audit. The third run has now supplied the canonical SR
premise on the finite common fragment: #1278 proves concrete transcript/key/table transport,
and #1279 proves the actual coin-bearing SR bound from native certificates, then applies the
attributed #848 single-salt transport. #1277 separately proves native stopped compiler security.
The matched-check accepted-event connection is now proved in #1281; full and stopped rejected
runs are not identified at the log/cache level. Honest salt-aware native compilation and its
completeness transfer are proved in #1280, including a connection to the actual native executor.

The conditional duplex HOPE needs more than substituting a theorem name. At the pinned #848
snapshot, its knowledge theorem uses `srInitDIP`, `srImplLift`, and private auxiliary interface
`(Unit →ₒ U) + unifSpec`, with structural bound `θStar` and the exact `ηStarTotal` term. The new
native bridge currently uses its explicit native-table pushforward initializer, empty ambient
oracle, and `unifSpec`. A further sampler/auxiliary-query correspondence is required before
instantiating Section 6. `KeyLemmaSecurityWitness` must remain explicit.

The pinned Section 5/6 stack also differs from the run's baseline by roughly 11,000 added lines
across the duplex modules and original SingleSalt file, including definitions, codecs, traces,
and transforms. Porting that entire dependency surface would need its own reviewed stack; a
small wrapper on the current baseline would not prove the promised conditional duplex result.
No such wrapper is counted as a completed result of this run.

The narrow #848 ports retain shared declaration names and attribution. When the remainder of
that original stack is rebased onto #1275–#1276, it should import the shared owner modules and
remove duplicated declarations; both copies should not be merged unchanged. The original authors'
branches have not been edited by this run.
