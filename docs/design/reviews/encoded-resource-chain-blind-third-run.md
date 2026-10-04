# Blind read-back: final encoded resource chain

**READBACK COMPLETE**

This independent report translates the code supplied by `python3 /tmp/arklib-third-run-20261004/blind/read-encoded-resource-chain-module.py MODULE`, under the original blind protocol. Source identity is **961caa039-plus-final-resource-chain**. No contract, intended claim, author reports, source docstrings/comments, git history, builds, or Lean edits were inspected or performed. Earlier independently inspected definitions were reused only after checking source identities; changed definitions/modules and the probability statements were reread. This report gives no fidelity verdict or proof/axiom certificate.

The permitted raw Lean `#check` output in `/tmp/arklib-third-run-20261004/encoded-elaborated-signatures.txt` was inspected only for the earlier same-named sharp and adversary-count probability declarations. It identifies their witness-state universe as a generalized `u_1`. That output is from the earlier compiled 60a source, not an elaboration check of the current snapshot. The present source statements retain the same displayed binders; current compiled signatures were not inspected.

## Source hashes and API identities

| Module | Reader SHA256 |
|---|---|
| ArkLib.Interaction.Oracle.Security.EncodedSecurityEvent | 98f4730604c0733c2a29f59334c3a5682ffba5394a135448506e3afa6201ceba |
| ArkLib.Interaction.Oracle.Security.EncodedCharge | 39a7b27ec3a14a26388317a368a7cec2577c8e14a4bf6cf30e195fe7d92007e6 |
| ArkLib.Interaction.Oracle.Security.EncodedChallenges | 5548cfcc01ef33cbaa0c0e0f74c22d66d679d1f6d67e679c5c4ce04a70bc1769 |
| ArkLib.Interaction.Oracle.Security.EncodedChallengeCoupling | b6569366873ad2cc3624b944c1da19f5c63881f0821900f2b0c5bf7e9b5f6dda |
| ArkLib.Interaction.Oracle.Security.EncodedChallengeCost | b932a260d2e823c64ee2739cafa9a5889f7f8021b46c0ced6285253eae8ee7a0 |
| ArkLib.Interaction.Oracle.Security.EncodedCompletion | 4792e1ebf9d20ac43cc3d1e4020907dbdf4078b8b6c951a48b2ec5f0c60943ad |
| ArkLib.Interaction.Oracle.Security.EncodedSecurity | e1915947bd18ae7066d5c39a8c7c964ffd96e70bd3a31fb3d523edc7ed48f999 |
| ArkLib.Interaction.Oracle.Security.EncodedCodec | 204a8474d2152bd72ed5add4f1244034e10a98618882fab4b5b2a8f662313fbd |
| ArkLib.Interaction.Oracle.Security.EncodedReduction | 5c6bc83bb71d713907b26a585152b2eca2ff5d20a1fbc8b1c9c66d83d762e2de |
| ArkLib.Interaction.Oracle.Security.EncodedLog | cb7573546c31e47e35a7302f18fad03f895c89d9c23ee6feb92424ca218b0d36 |
| ArkLib.Interaction.Oracle.Security.EncodedWeighted | 07c21afbe908d9086142e65b15744cb2419adbf87e1da5b9f5ade7a2278a79a7 |
| ArkLib.Data.OracleComp.RandomOracleCost | 0431bcd5637060a32f7183dfbab0a3cc74c64c7714ce4c255bb121db454edb10 |
| ArkLib.Interaction.Oracle.Security.StateRestoration | 63df21e0ed1135f771e7c26e7c69a1bc53e96d5c391c923b58a5dba54057e70a |
| ArkLib.Interaction.Oracle.Security.StateRestorationRandomized | 01a72e2880ed62d1d3651541bf04cbb45a92f4426e4266cd28f424e34aa271ff |
| ArkLib.Interaction.Oracle.Security.StateRestorationStopped | a4926c1e185adb683c9e536b0e8a2db2307c8aa77552a87ec159a51ec4d2f23d |
| ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget | 5bd91b535a579152292ede55427b5e1ee943c2948221da32ff5346af20194e1f |
| ArkLib.Interaction.Oracle.Security.StateRestorationBudget | 3ed9356728b3a5915a40995e5fff7de10279ccca4364a9fc387f619dfd618d11 |
| ArkLib.Interaction.Oracle.Security.Knowledge | 803dbe0bc24e46178b9384d9a0fc5ed87c90b6f4e24971f2bcc46fb5e39cd22b |
| VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun | 8eaacb6ca6cbde5c9597230cbf33fc8490f8458a1d85ed32628f426cfe05d0ca |
| VCVio.OracleComp.Constructions.SampleableType.Basic | 09d7e9ef3fe9cf7db1cb5fa0c418a7a2bd87f354183c661f7cc73a446d32b0b1 |

Changed hashes relative to the preceding 60a read-back include EncodedSecurityEvent, EncodedCompletion, EncodedSecurity, and EncodedCodec; the last was reread and its codec fields/laws remain as described below. Renamed modules were read under their new identities. The unchanged hashes above justify reuse of the previous independent reads of native state/event, sampling, and log/cost definitions. ArkLib reader paths have the snapshot identity above; VCVio reader paths remain under `/Users/quangdao/Documents/Lean/.third-run-deps-20261004/VCVio/...`.

The current modules are `EncodedChallenges`, `EncodedChallengeCoupling`, and `EncodedChallengeCost`, corresponding to the previously read EncodedFibre modules. The `CommonChallenge` field is now **`challengeEquiv`**, with type `(key : Key Input Salt rounds) → key.Challenge ≃ C`. The uniform-answer theorem is now **`CommonChallenge.evalDist_challengeEquiv_uniform`**. Complete rereads show these public identifiers in the definitions and statements; no old-field alias appears in the inspected renamed module. The main coupling theorem `CommonChallenge.evalDist_randomOracleLoggedRun_simulateNative` and main cost theorem `CommonChallenge.expectedFreshQueryCharge_simulateNative` retain their declaration names.

`EncodedSecurityEvent` imports EncodedSecurity, EncodedChallengeCoupling, RandomOracleCost, and the new EncodedCharge. EncodedCharge imports EncodedWeighted. EncodedCompletion imports EncodedChallenges; EncodedSecurity imports EncodedCompletion and EncodedChallengeCost. These are import identities, not a complete checked dependency lockfile.

## Definitions and the executions being compared

All primary declarations are in `Interaction.Oracle.Security.StateRestoration`. Fix implicit `Input Salt C D W : Type`, and explicit `rounds : List Round`. Let `K = Key Input Salt rounds`, native oracle `N = oracleSpec Input Salt rounds`, common oracle `H = K →ₒ C`, and external oracle `E = D →ₒ C`.

A round supplies a finite message type with decidable equality and a finite nonempty native challenge type with certified uniform sampler. K is Empty for no rounds; otherwise it is `(Input × Message × Salt) ⊕ (Message × Salt × tailKey)`. Keys contain the selected input and message/salt prefix, and their dependent answer type is the challenge type at the selected round. Input, Salt, D, and the overall key space need not be finite.

`common.challengeEquiv k`, written `e_k`, is an actual supplied bijection from native `k.Challenge` to C. `StrictCodec K D` supplies encode/decode and exactly both laws `decode (encode k) = some k` and `decode d = some k → encode k = d`. It therefore recognizes precisely an injective encoded image; there are no decoded aliases. Define `wE(d) = codec.encodedWeight w d`: this is zero on decode-none keys and w(k) on decode-some k keys.

`codec.decodeImageLog` filters the external list of key/common-answer pairs: it drops off-image entries, and replaces a decoded external key by its native key, leaving its C answer unchanged. `freshKeysOfLog L` is the finite set of keys occurring anywhere in L, ignoring multiplicities and answers. `freshQueryCharge w L` sums w once per distinct such key. `expectedFreshQueryCharge P w` integrates that charge over the outer hash-log coordinate of `randomOracleLoggedRun P`, always with the default empty initial hash cache. These are ENNReal quantities and may be infinite. Uniform coins and sampler-internal choices are not hash-log entries.

`codec.routeProgram P off` returns `((output, externalLog),finalOffCache)` as a program over H plus uniform randomness. Image queries become common queries at their decoded key; off-image queries are answered from a separate cache with fresh uniform C samples on misses. Hits and misses both enter the returned external log. Off-image queries induce no common-native hash query, but their answers remain observable to the program and may affect later queries/output. `common.simulateNative` then replaces common queries by native queries followed by e_k and forwards uniform choices. These transformations do not impose a nonadaptive-query assumption.

An external adversary is any total oracle program `external : OracleComp (unifSpec + E) (Option (Input × Messages Salt rounds × W))`. It chooses a whole message/salt tuple before completion. Define X = `encodedExternalStoppedExecution rounds common codec guards external`, whose body is external bound to its encoded completion. On none selection completion returns none; on some `(z,messages,w)` it checks each Boolean guard before that round's challenge query. If true it queries E at encode k, converts the answer with `e_k.symm`, and continues with the next guard schedule selected by that challenge. If all rounds pass it returns some `(z,path,w)`; any guard failure yields none. The same external lazy cache persists across adversary and completion, including reuse of adversary queried encoded keys. Completion itself queries image keys only.

Define B = `encodedNativeAdversary common codec external`: project the selection value from `common.simulateNative (codec.routeProgram external empty)`. Its private off-cache is erased from the returned output after the adversary phase. Native direct completion makes no off-image query and does not need that erased cache. Define J = `randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards B`. J keeps the adversary source log alongside the selected completion result. Its outer logged run returns `(((result,adversarySourceLog),jointNativeHashLog),finalNativeCache)`, whereas the actual external logged run of X returns `((result,jointExternalHashLog),finalExternalCache)`. Outer caches start empty in the main formulas below. Native and external logs may differ, especially through off-image queries.

Random-oracle misses use certified uniform answer samplers; repeated queries reuse answers. `SampleableType C` is a sampling computation plus a uniform-law certificate, and entails finite nonempty C. The quantified OracleComp/ProbComp programs are inductively total computations with adaptive continuations, not arbitrary divergent or primitive-failure algorithms. None is returned data and retained probability mass.

## New declarations in EncodedCharge

`StrictCodec.freshImageCharge_eq` has implicit `K D C : Type`, explicit `codec : StrictCodec K D`, `[DecidableEq K] [DecidableEq D]`, then **every** `weight : K → ENNReal` and **every** `log : QueryLog (D →ₒ C)`. It states exactly

`freshQueryCharge weight (codec.decodeImageLog log) = freshQueryCharge (codec.encodedWeight weight) log`.

There is no sampler, execution, support, cache, or consistency assumption. All decoded image keys in an arbitrary external log appear in the decoded list, with repetitions discarded on both sides; the encoded external weights of all remaining off-image distinct keys are zero. This is an equality, including when the charge is infinite. It does not assert equality of total distinct key counts: weighting all external keys by one would also count off-image keys.

`StrictCodec.expectedNativeCharge_eq_external` has implicit `K D C A : Type`, explicit codec, `[DecidableEq K] [DecidableEq D] [SampleableType C]`, then **every** `program : OracleComp (unifSpec + (D →ₒ C)) A` and **every** fixed `weight : K → ENNReal`. It states exactly

`expectedFreshQueryCharge (codec.routeProgram program empty) weight`

`= expectedFreshQueryCharge program (codec.encodedWeight weight)`.

The LHS charges the **outer common-native hash log**, not the external log retained inside the routed program's output. The routed initial off-cache and each expected-cost run's initial hash cache are empty. The external program may be adaptive, may repeat keys, and may query any off-image point. No finite-expectation or worst-case query bound is required. This is an equality of scalar expectations, not equality of full programs or raw native/external logs. Off-image work and internal random sampling operations are not charged on either weighted side.

## New declarations in EncodedSecurityEvent

`encodedExternalStopped_expectedCharge_eq_native` has implicit `Input Salt C D W : Type`, instances `[DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]`, then explicit parameters in order `rounds`, `common`, `codec`, `guards`, **every external adversary**, and **every weight : K → ENNReal**. It states

`expectedFreshQueryCharge X (codec.encodedWeight weight)`

`= expectedFreshQueryCharge J weight`.

Both charges include the entire adversary-plus-stopped-completion execution, with default empty outer caches. Native source-log retention does not enter the cost: its outer joint native hash log does. On the actual external side, encoded overlap between adversary and completion is counted once. No extractor, witness law, valid relation, membership restriction Z, local probability bound, or guard correctness assumption is required. Weight is a fixed arbitrary key function, not a random outcome-dependent value. This equals the weighted charge rather than merely upper bounding it.

`encodedExternalStopped_expectedCharge_le_adversaryCount` has implicit `Input Salt C D W : Type`, only `[DecidableEq D] [SampleableType C]`, and parameters in order `rounds`, `common`, `codec`, `guards`, `errors : Fin rounds.length → ENNReal`, and **every external adversary**. It states

`expectedFreshQueryCharge X (codec.encodedWeight (keyError errors))`

`≤ Finset.univ.sup errors * expectedFreshQueryCharge external (fun _ => 1) + ∑ j, errors j`.

Here keyError selects the error for the round represented by a native key. The supremum is over all round indices, with empty supremum zero. The RHS counts **all distinct D hash keys from the adversary phase alone**, including off-image keys, and adds the sum of errors for all rounds. It is not an actual-completed-round budget, and can overcount stopped rounds and adversary/completion overlaps. No security-event hypothesis appears: this is a resource inequality for every such execution, independent of extraction correctness. Input/Salt equality decisions are supplied internally by `classical` in the proof, not additional hypotheses in this exported declaration.

## Literal reread of the probability statements

`encodedExternalStopped_evalDist_result_eq_native` still has implicit `Input Salt C D W : Type`; `[DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]`; and then explicit `rounds`, common, codec, guards, and every external adversary. Using powerset measurable space on Result = `Option (Input × protocolPath × W)`, it states

`𝒟[(fun joint => joint.1.1) <$> randomOracleLoggedRun X empty]`

`= 𝒟[(fun joint => joint.1.1.1) <$> randomOracleLoggedRun J empty]`.

`encodedExternalStopped_prEvent_eq_native` has exactly those execution parameters and classes followed by any `event : Result → Prop`, and states equality of event probability on those selected-result projections. No event decidability or measurable-event hypothesis is present. It includes none outcomes when event counts them. These statements do not equate full native/external caches or logs, or common random tapes or program syntax.

The two knowledge-soundness statements have implicit Input/Salt/C/D/W types, only `[DecidableEq D] [SampleableType C]`, explicit rounds/common/codec/guards/errors/external, followed in order by:

1. `state : Input → KnowledgeState`, and `extractor : ∀ z, RoundExtractor protocol.tree (state z)`.
2. `Z : Set Input`.
3. `preserving : ∀ z ∈ Z, extractor z.IsProverPreserving protocol.roles`.
4. `bounded : ∀ z ∈ Z, extractor z.IsLocallyBounded protocol.roles (roundErrorSchedule rounds errors)`.
5. `Rin : ∀ z, state z.Witness → Prop`, and `Rout : ∀ z path, W → Prop`.
6. `terminalWitness : ∀ z path, W → (extractor z.terminalState path).Witness`.
7. `inputLaw : ∀ z u, state z.holds u ↔ Rin z u`.
8. `outputLaw : ∀ z path w, Rout z path w → terminalState.holds (terminalWitness z path w)`.

A knowledge state is an arbitrary witness type and predicate. The supplied extractor consists of deterministic after-states and backward witness maps for every message/challenge edge; `extractWitness path` composes those maps. Prover-preserving means all message transitions preserve goodness under their backward maps, recursively at every continuation. Locally bounded means at every receiver challenge transition, the probability under that round's uniform native challenge sampler of `∃ afterWitness, ¬ before.holds (backward afterWitness) ∧ after.holds afterWitness` is **≤ errors j**, recursively for all message/challenge choices. These hypotheses hold for all paths of each input in Z, not just reachable or guard-passing paths. The input/output laws and total terminalWitness function quantify over all inputs, paths, and witness values, including outside Z and support. OutputLaw is only an implication. terminalWitness is not required to be bijective, and the theorem does not construct it.

Define `I(z,p,w) = extractor z.extractWitness p (terminalWitness z p w)`. `badStoppedRelation` is false on none and on some `(z,p,w)` is exactly `z ∈ Z ∧ Rout z p w ∧ ¬ Rin z I(z,p,w)`. It is failure of the supplied extracted witness, not nonexistence of every input witness. There is no independent extraction algorithm, random extractor seed, salt entropy assumption, or running-time bound.

`encodedExternalStopped_knowledge_soundness_sharp` states exactly

`Pr[joint ← randomOracleLoggedRun X empty; badStoppedRelation ... joint.1.1]`

`≤ expectedFreshQueryCharge X (codec.encodedWeight (keyError errors))`.

`encodedExternalStopped_knowledge_soundness_adversaryCount` states exactly the same event probability is

`≤ Finset.univ.sup errors * expectedFreshQueryCharge external (fun _ => 1) + ∑ j, errors j`.

The present proofs use the new exact charge transport and the resource inequality, respectively. They retain their event and assumptions; those source statements were reread rather than inferred from names. Earlier raw #check output confirms that their unannotated KnowledgeState binder generalized its witness universe to `u_1`; it did not restrict witnesses to Type 0. That earlier output does not check the current snapshot's new declarations.

Combining the exported current statements gives the literal mathematical chain

`actual external bad-event probability ≤ actual whole-execution weighted image-key expectation = native whole-execution weighted expectation ≤ εmax · expected number of distinct external adversary keys + εsum`.

The equal sign is justified by the new expectedCharge_eq_native declaration; the final resource bound does not require security hypotheses. Every expected quantity here comes from the specified actual lazy-oracle run from empty caches, not an assumed independent transcript distribution or a supplied query-bound number.

## Renamed challenge probability/cost interface

`CommonChallenge.evalDist_challengeEquiv_uniform` requires common, `[SampleableType C]`, and any key; it asserts `𝒟[e_k <$> uniformSample k.Challenge] = 𝒟[uniformSample C]` in the powerset space on C. Native samplers are the round-induced instances. Their implementation/coin counts need not match the common sampler.

In EncodedChallengeCoupling, `encodeJoint ((a,L),c)` remains `((a,toCommonLog L),toCommonCache c)`: keys/order/repetitions are retained; answers are mapped with challengeEquiv; cache none/some values are converted pointwise at every key; a is unchanged. `evalDist_randomOracleLoggedRun_simulateNative` quantifies over common, Input/Salt decidable equality, SampleableType C, implicit output type A, every program `P : OracleComp (unifSpec + H) A`, and every native initial cache c. It states the full-joint measure equality

`𝒟[encodeJoint <$> randomOracleLoggedRun (simulateNative P) c]`

`= 𝒟[randomOracleLoggedRun P (toCommonCache c)]`.

This theorem allows arbitrary initial cache functions, even infinite-support ones; it concerns full converted cache/log/output law. It does not produce equal sampler syntax or an explicit shared-tape coupling. The single-step logged query laws and bind law remain quantified over arbitrary initial caches; the bind law assumes prefix equality for every cache and continuation equality for every intermediate output and cache, not only supported ones.

In EncodedChallengeCost, `freshKeys_toCommonLog` assumes only Input/Salt decidable equality, common, and arbitrary native log, and states equality of distinct key sets under answer conversion. `expectedFreshQueryCharge_simulateNative` assumes those equalities and SampleableType C, then common, every common-native program P, and every key weight, and states `expectedFreshQueryCharge (simulateNative P) weight = expectedFreshQueryCharge P weight`, from the default empty caches. The field/module renaming does not introduce an arbitrary nonuniform sampler or change the cost to per-query multiplicity.

## Boundaries and verification limits

All resource weights/errors are ENNReal and may be infinite; no finiteness, integrability, ≤1 error, or probability clipping is asserted. The strict codec equality does not apply to arbitrary off-image-positive weights. The main expected equality/count bound has no nonempty-cache parameter. Arbitrary adaptivity and repeated keys are included within the total computation type; no infinite interaction or divergence guarantee is supplied.

Aborted selections/completions contribute false to the security event but retain any preceding query costs. None is not conditioned away, and there is no division by success probability. Empty Z, false Rout, always-none adversaries, or rejecting guards can make the event vacuous. Empty rounds yield no native/image keys and zero error budget; off-image queries can still occur externally, but have zero encoded weight. CommonChallenge and StrictCodec parameters can be uninhabited if their required bijections/injection do not exist. Salt/Input/message emptiness can eliminate keys; SampleableType C still forces finite nonempty C even then. No guard law guarantees nontrivial acceptance.

No tests/builds or current compiled-signature checks were performed, as required by the assignment. Source identities and raw earlier two-declaration signatures are recorded separately. The custom predicates and cost/execution definitions needed for this read-back are resolved; current proof checking remains outside this report.

**READBACK COMPLETE**
