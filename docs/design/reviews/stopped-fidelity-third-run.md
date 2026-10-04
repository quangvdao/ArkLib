# Third-run stopped-security fidelity ledger

Reviewed: blind code-only read-back at `849d526164a4c0c50d31aea9ef59ddeae842eca0`, contract `docs/design/interaction-security-third-run-contract.md`, and root's Sumcheck expected-round addition in `ArkLib-third-run` at `80bcc82b0a2a3c35019e80e172c28dbf13675d3e` plus uncommitted diff. Read-only ordinary review; no independent build.

## Blind read-back versus source and contract

The blind read-back correctly identifies the theorem's `Option` failure event, all-prefix local certificate assumptions, private-uniform-plus-random-oracle adversary, shared cached logged joint run, distinct-key expected weighted charge, and two-step budget. It also correctly describes `guardPrefixAtKey_update` as own-answer invariance of ancestor/target guard outcomes, not invariance of later guards. No mathematical misreading found in the read-back.

Contract MUST 1 ledger:

| Obligation | Evidence/status at 849d |
| --- | --- |
| Generic accepted-invalid-extraction bound using named backwards extractor | Present in `StateRestorationStopped.lean:552–590`, conditional on explicit endpoint laws and local certificate. |
| Bad queried key from fixed-table accepted trace | Present in `StateRestorationStopped.lean:354–375, 460–500`; the trace implication is discharged, not left as hypothesis. |
| Own-cell guard/pre-challenge invariance | Present in `StateRestorationStopped.lean:94–149`, including rejected prefixes. |
| Actual distinct adversary keys and executed verifier-round cost | Present in `StateRestorationStoppedBudget.lean:348–379`; adversary failure retains spent keys and verifier rejection skips suffix queries. |
| Native guard-visible `executeStrategies` equality of result, ordered log, final cache | Not in the blind slice. This remains necessary before full MUST 1 acceptance. |
| Native Sumcheck corollary | Abstract stopped-program corollary is present; verified native-executor endpoint remains pending. |

Contract MUST 2 is not discharged by this slice: no common-fragment native/legacy transport, finite eager/lazy observation and extractor connection, induced FS adversary, or actual native compiled/stopped-game equality. The canonical #848 port is a separate conditional legacy theorem, not an automatic discharge of its SR premise.

## Terminal seed restriction

`badStoppedRelation` and both security headlines require `terminalWitness : ∀ z path, W ≃ (extractor z).terminalState path |>.Witness` (`StateRestorationStopped.lean:510, 526, 565`; `StateRestorationStoppedBudget.lean:205, 361`). The proof projects only `terminalWitness z path w` into the terminal witness type. The deeper `badExtractOnPath` and fixed-table certificate lemmas already accept a forward function. Consequently the equivalence's inverse and injectivity/surjectivity are unused security assumptions inherited from the older `extractInputWitness` convenience definition (`StateRestorationGame.lean:92–97`).

This is a real abstraction restriction for the general acceptance-derived seed promised by MUST 1/2. A proof-only FS prover supplies output witness `Unit` in canonical #848 (`OracleReduction/FiatShamir/Legacy/SingleSalt.lean:534–545`), but a transported terminal knowledge state may have, for example, a `Bool` seed type with a canonical seed determined from `(z,path)`. The map `Unit → Bool` exists and can be validated on acceptance; `Unit ≃ Bool` does not. The current Sumcheck client happens to construct a Unit terminal witness equivalence and is unaffected. The current source does not yet establish a concrete non-Unit FS terminal state, so this is a potential blocker to the contracted general native FS connection, not a proved failure of that specific forthcoming construction.

Smallest repair: in the new stopped relation/headlines accept a dependent forward seed function `∀ z path, W → terminalState.Witness`, and define the named input extractor directly as `(extractor z).extractWitness path (seed z path w)` or add a forward-map variant of `extractInputWitness`. Require only `Rout z path w → terminalState.holds (seed z path w)` for the output law. Existing equivalence clients specialize using `.toFun`; legacy APIs need not change. If a terminal witness type can be empty on rejected paths, even a total forward map is too strong and an accepted-path dependent seed or `Option`-valued seed is necessary. Do not add that extra abstraction unless the concrete FS bridge encounters it.

### Recheck of root's uncommitted seed-map repair

Reviewed the exact uncommitted four-file diff on `ArkLib-third-run` at base `80bcc82b0a2a3c35019e80e172c28dbf13675d3e`: `StateRestorationStopped.lean`, `StateRestorationStoppedBudget.lean`, `StateRestorationStoppedFinite.lean`, and `Sumcheck/Interaction/StoppedSoundness.lean`. **Approve this scoped repair; no P0/P1 defect found.** The event now computes `extractWitness path (terminalWitness z path witness)` directly (`StateRestorationStopped.lean:505–518`). The bridge to the existing bad-extraction event uses precisely acceptance→terminal `holds` (`:521–547`), so it neither assumes the input relation nor selects an existential terminal witness. The generic expected-charge proof still invokes the same fixed-table bad-key theorem and key resampling bound (`:552–588`). All three budget headlines and the finite eager comparison pass the forward map through without changing the charged run or event. Sumcheck passes `.toFun` from its existing equivalence and the `.mpr` direction of its existing terminal iff (`StoppedSoundness.lean:84–110`), preserving the same Unit seed and false-acceptance event. The new expected-round corollary remains as reviewed below.

This repair removes the unnecessary inverse/bijection requirement but still requests a *total* seed for every path, including rejecting paths. An empty terminal witness type on any rejecting path can still obstruct a client. Whether the native FS bridge encounters this is presently unknown; defer a larger accepted-path or optional-seed interface unless that concrete case appears. Root reports target builds pass; `/tmp/arklib-third-run-20261004/seed-map-validation.log` shows the full build and warning checks succeeded, with the axiom validation still in progress at this read-only check. I did not build independently.

## Root Sumcheck expected-round addition

The new `stoppedSumcheck_expected_round_bound` in `ArkLib/ProofSystem/Sumcheck/Interaction/StoppedSoundness.lean:114–143` is a sound corollary of `stoppedSumcheck_expected_soundness` plus the established actual-round resource theorem: `fieldError * E[adversary distinct hash keys] + E[executed verifier hash-call weights]`, and the latter is at most `n * fieldError`. Its guard is the current polynomial sum check before that round's challenge query. `sourceLaw` explicitly identifies the native source handler with the polynomial realization; the acceptance event uses `nativeObservedOutput` and `Native.outputRelation`. It is ordinary false-claim soundness with Unit output witness, not substantive extraction. The cost counts executed verifier calls, including cached hits, so it is an upper bound rather than the exact extra distinct-key charge. No P0/P1 issue found in this narrow theorem. It still runs the abstract stopped program; native `executeStrategies` result/log/cache correspondence is outside this addition.
