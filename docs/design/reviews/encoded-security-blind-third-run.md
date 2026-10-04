# Blind supplemental read-back: encoded completion and security event

**READBACK COMPLETE**

This is an independent code-only translation under `/tmp/arklib-third-run-20261004/blind/protocol.md`. Lean was inspected only using the supplied comment-stripping readers. No intended contract, author explanation, source comments/docstrings, other agents' reports, git history, builds, or Lean edits were inspected/performed. Only this report is authored here. It supplies no intended-claim fidelity verdict and no proof-checking or axiom certificate.

## Revision and source hashes

The first supplemental reader labeled ArkLib sources `encoded-security-targeted-0901`. Following a parent notification about validation changes, the final main event module was reread completely with `read-encoded-security-final-module.py`; main and relevant dependency identities were verified against its immutable source identity **60a93402b**. The observed `EncodedSecurityEvent` SHA256 did **not** change between those two reads: both returned `e463eb81b28c5f8fc5d10389bd0943ac3deff5eb7cd0e70758b11b93d78ffaac`. The other verified module hashes likewise did not change. Thus the recorded change is the snapshot/revision identity, with no observed source-hash difference. No inference is made about source states not observed by these readers.

The unchanged fibre/codec/sampler definitions were inspected in my preceding independent fibre read-back and their hashes verified anew here. This report restates all semantics needed for the present statements. ArkLib modules below are identified by the final reader as `60a93402b:ArkLib/...`; dependencies are under `/Users/quangdao/Documents/Lean/.third-run-deps-20261004/...`.

| Module | SHA256 |
|---|---|
| ArkLib.Interaction.Oracle.Security.EncodedSecurityEvent | e463eb81b28c5f8fc5d10389bd0943ac3deff5eb7cd0e70758b11b93d78ffaac |
| ArkLib.Interaction.Oracle.Security.EncodedCompletion | b46be6e0624a91966e42a3e0f026a2e116e80c06ed7494164b22a4f358dcb30d |
| ArkLib.Interaction.Oracle.Security.EncodedSecurity | 811c706c47a4ccb7dc5157fa24719392cbd0828251e4b520564dbd511e7593ba |
| ArkLib.Data.OracleComp.RandomOracleCost | 0431bcd5637060a32f7183dfbab0a3cc74c64c7714ce4c255bb121db454edb10 |
| ArkLib.Interaction.Oracle.Security.EncodedFibre | 63bbebb61d4afe46be7f04592a48dda6add5e16f164b02bbf07dfa6b85947a6f |
| ArkLib.Interaction.Oracle.Security.EncodedFibreCoupling | bcfcaf14a7bae64ef084058125e95afbc99d0e2e8396c46477d437e1d4a5bdfb |
| ArkLib.Interaction.Oracle.Security.EncodedFibreCost | c9cf648fa7a33d86f874766f8c5ceaa40a9034c447936db393fb9fc0b95a7ed0 |
| ArkLib.Interaction.Oracle.Security.EncodedCodec | 89dee413727f50ce3956c3ff8de15366fce224a6814119ce331ae11a7145bafb |
| ArkLib.Interaction.Oracle.Security.EncodedReduction | 5c6bc83bb71d713907b26a585152b2eca2ff5d20a1fbc8b1c9c66d83d762e2de |
| ArkLib.Interaction.Oracle.Security.EncodedWeighted | 07c21afbe908d9086142e65b15744cb2419adbf87e1da5b9f5ade7a2278a79a7 |
| ArkLib.Interaction.Oracle.Security.StateRestoration | 63df21e0ed1135f771e7c26e7c69a1bc53e96d5c391c923b58a5dba54057e70a |
| ArkLib.Interaction.Oracle.Security.StateRestorationBudget | 3ed9356728b3a5915a40995e5fff7de10279ccca4364a9fc387f619dfd618d11 |
| ArkLib.Interaction.Oracle.Security.StateRestorationRandomized | 01a72e2880ed62d1d3651541bf04cbb45a92f4426e4266cd28f424e34aa271ff |
| ArkLib.Interaction.Oracle.Security.StateRestorationStopped | a4926c1e185adb683c9e536b0e8a2db2307c8aa77552a87ec159a51ec4d2f23d |
| ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget | 5bd91b535a579152292ede55427b5e1ee943c2948221da32ff5346af20194e1f |
| ArkLib.Interaction.Oracle.Security.Knowledge | 803dbe0bc24e46178b9384d9a0fc5ed87c90b6f4e24971f2bcc46fb5e39cd22b |
| ArkLib.Interaction.Oracle.Protocol | a08255b21d59e1a6925a341c5de55bb613f746c7237a3d8066bf140815813eca |
| ArkLib.Interaction.Oracle.TypeTree | 84c4cc573a5e4e06b7e8d9c643e6292a38d5b6620f7bdfebaa64d22963a765d7 |
| ArkLib.Interaction.Oracle.TypeTree.Decoration | 8debe5e16dd3aacc5d4190579e4b54c10d98d778be5e22640031b8e0832450b1 |
| VCVio.CryptoFoundations.RoundByRound | 8b82b250af7e4c81c2b945518b1202a756003591aa4cb83bee5b448b2f0f55e0 |
| VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun | 8eaacb6ca6cbde5c9597230cbf33fc8490f8458a1d85ed32628f426cfe05d0ca |
| VCVio.OracleComp.Constructions.SampleableType.Basic | 09d7e9ef3fe9cf7db1cb5fa0c418a7a2bd87f354183c661f7cc73a446d32b0b1 |

Main import identities: `EncodedSecurityEvent` imports `EncodedSecurity`, `EncodedFibreCoupling`, and `RandomOracleCost`. `EncodedSecurity` imports `EncodedCompletion` and `EncodedFibreCost`. `EncodedCompletion` imports `EncodedFibre`. `RandomOracleCost` imports the VCVio `LoggedRun` module. The relevant native-event chain reaches `StateRestorationStoppedBudget`/`Stopped` and `Knowledge`. This is a source identity record; no lockfile, compiled environment, or complete transitive axiom check was done.

## Key, answer, codec, and random-oracle semantics

All primary declarations are in `Interaction.Oracle.Security.StateRestoration`. Fix implicit `Input Salt C D W : Type` and a finite list `rounds : List Round`. Let `K = Key Input Salt rounds`, `N = oracleSpec Input Salt rounds`, `H = K →ₒ C`, and `E = D →ₒ C`.

A round supplies its message type, oracle interface, decidable message equality, finite message type, finite nonempty challenge type, and certified uniform challenge sampler. `K` is recursively `Empty` at no rounds and `(Input × current.Message × Salt) ⊕ (current.Message × Salt × tailKey)` otherwise. A key specifies the selected input and message/salt prefix; its answer type `k.Challenge` is the challenge type at its selected round. The native oracle returns that dependent answer. Message/salt prefixes in keys do not contain preceding challenges. Inputs, salts, and external key type `D` need not be finite.

`common : CommonChallenge Input Salt C rounds` supplies exactly a bijection `e_k : k.Challenge ≃ C` for every native key. `codec : StrictCodec K D` supplies `encode : K → D`, `decode : D → Option K`, and both laws:

1. `decode (encode k) = some k` for every `k`.
2. `decode d = some k → encode k = d` for every `d,k`.

Thus encode is injective, decoding recognizes exactly its image, and there are no alternative decoded aliases. Off-image means `decode d = none`. No concrete string representation, prefix-free scheme, cryptographic hash function, or probability of key collisions is provided by these parameters.

`SampleableType C` contains a sampling computation and a theorem that its distribution is uniform on the whole type; the library derives finiteness and nonemptiness. Native fibre samplers are the round-supplied certified uniform instances, and may have different implementations from the sampler of `C`. `common.simulateNative` converts each common hash query at `k` into the native hash query at `k` followed by `e_k`, forwarding uniform randomness unchanged.

`codec.routeProgram P off` is a common-native oracle program with returned value `((a, externalLog), finalOffCache)`. Uniform queries are forwarded. On an image query `d=encode k`, it queries `H` at `k`, returns that common answer, logs `(d,answer)` externally, and leaves off-cache unchanged. On an off-image query, it checks the off-cache: a hit returns the stored `C` answer, a miss samples fresh uniform `C` and stores it. Both kinds append the external query entry. Off-image queries produce no `H` hash query, but their answers and adaptive effects on later choices are retained. Off-cache entries at image points, if supplied, are ignored. Reduction theorems start the off-cache empty.

`randomOracleLoggedRun` lazily samples and caches each hash oracle answer; repeated hash queries reuse the same cached answer. Every hash query, including a hit, is appended to an ordered log. Uniform choices and internal sampler coins are absent from that hash log. A run returns `((a,hashLog),finalHashCache)`. Its initial cache is empty in every main distribution/security assertion here. Denotation `𝒟[...]` and probability notation use actual ProbComp measure semantics, with discrete reply types; all displayed result measures use the powerset measurable space. ProbComp is the total inductive free computation over uniform queries `n : Nat` returning `Fin (n+1)`, not a model with arbitrary divergence or primitive failure.

## The actual execution

`Messages Salt rounds` is the recursively nested tuple of one message and salt for each round (`PUnit` for no rounds). An external adversary is any total program

`external : OracleComp (unifSpec + E) (Option (Input × Messages Salt rounds × W))`.

It can choose arbitrary `D` keys adaptively using previous common answers and uniform choices. Its entire message/salt list, selected input, and `W` value are returned at the end of its phase. The completion phase then uses those fixed messages/salts; it does not invoke the adversary again to choose a new message after each completion challenge.

`GuardSchedule Input Salt rounds` is `PUnit` at no rounds and, at each round, a Boolean predicate `Input → Message → Salt → Bool` paired with a function `Message → Salt → Challenge → nextGuardSchedule`. Hence later guards can depend on earlier challenges via their selected schedule. No correctness or nontriviality law for guards is assumed.

`stoppedComplete rounds guards z messages` first checks the current guard, **before** requesting that round's challenge. A false guard returns `none` immediately. A true guard queries the native key at that prefix, chooses the next guard schedule using message, salt, and the challenge, and continues down the fixed message/salt tuple. If all rounds succeed it returns `some path`, where path contains the messages and native challenge values. A later abort returns `none` but leaves preceding queries in the log/cache. Empty-round completion returns `some PUnit.unit`.

`encodedCompletionQueries common codec k` requests `E` at `encode k` and applies `e_k.symm` to the answer. `encodedExternalCompletionAfter` on `none` returns `none`; on `some (z,messages,w)` it executes stoppedComplete using precisely those external encoded queries and maps a successful path to `some (z,path,w)`. No fresh salt, input, terminal witness, or seed is sampled by this completion wrapper.

Write `X = encodedExternalStoppedExecution rounds common codec guards external`. Its literal body is

`external >>= encodedExternalCompletionAfter rounds common codec guards`.

In the lazy external-oracle run, the same `D` cache is handed from the adversary to completion. Completion therefore reuses any prior adversary query at an encoded completion key. Its queries are image queries only; off-image queries can occur in the adversary phase and affect its returned selection.

`B = encodedNativeAdversary common codec external` is

`(fun result => result.1.1) <$> common.simulateNative (codec.routeProgram external empty)`.

It retains only the adversary's selected `Option` value and erases the returned external log and off-cache. Its executed native hash queries are the decoded image queries; off-image answers are generated by private uniform sampling and off-cache state inside its phase.

`nativeStoppedExecution rounds guards B` is `B >>= nativeStoppedCompletionAfter rounds guards`, where native completion uses direct native queries. The source-logged native version

`J = randomizedStoppedRestoredExecutionWithAdversaryLog rounds guards B`

first runs `B.withQueryLog`, recording the adversary's source query log including its uniform and native-hash queries, then completes and retains that source log alongside the selected result. Under outer `randomOracleLoggedRun`, the joint value is `(((result,sourceAdversaryLog),jointNativeHashLog),finalNativeCache)`. The source log stops at the adversary phase; the outer hash log includes adversary and completion queries.

## Exact event transport statements

`encodedExternalStopped_evalDist_result_eq_native` has implicit types `Input Salt C D W : Type`, instances `[DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]`, then explicit parameters `rounds`, `common`, `codec`, `guards`, and **every** external adversary of the above type. With powerset measurable space on `Result = Option (Input × protocolPath × W)`, it states

`𝒟[(fun joint => joint.1.1) <$> randomOracleLoggedRun X empty]`

`= 𝒟[(fun joint => joint.1.1.1) <$> randomOracleLoggedRun J empty]`.

This equates the distributions of the actual selected result, including `none`, input, completed path, and `W`. It does not equate full external and native joint logs/caches in this theorem. External logs contain off-image keys; native hash logs omit those queries. Both initial oracle caches and the reduction's initial off-cache are empty.

`encodedExternalStopped_prEvent_eq_native` has those same typeclasses and explicit parameters followed by **any** `event : Result → Prop`. It states exactly

`Pr[joint ← randomOracleLoggedRun X empty; event joint.1.1]`

`= Pr[joint ← randomOracleLoggedRun J empty; event joint.1.1.1]`.

There is no decidability or measurable-event assumption in its signature. It applies to all predicates on the selected result, including predicates counting `none`. It cannot directly compare arbitrary predicates on full logs or final caches. These two statements assert equality of distributions/probabilities, not equality of external and native program syntax or pointwise identity under the same random tape.

## Extractor and security hypotheses expanded

`KnowledgeState` consists of an arbitrary witness type and predicate `holds`. `RoundExtractor tree state` is a recursively supplied family: for every message or public move, it gives an after-state, a function from after-witnesses to before-witnesses, and an extractor for the remaining tree. At a terminal node it is `PUnit`. `terminalState path` follows the after-states along the completed path. `extractWitness path` composes the supplied witness maps backwards, returning the terminal witness unchanged at a terminal node.

These are deterministic mathematical functions. No query access, randomness, seed, computational efficiency, algorithm construction, or running-time bound for the extractor is asserted. Salt values are adversary-selected tuple components; no entropy, independence, uniqueness, or resampling rule for salts is assumed. The parameter `W` is merely the external returned value used as input to a terminal-witness function; the code does not define it as a random seed.

All three knowledge-soundness theorems below require the following supplied data/hypotheses after their execution parameters:

- `state : Input → KnowledgeState` and `extractor : ∀ z, RoundExtractor (protocol rounds).tree (state z)`.
- `Z : Set Input`.
- `preserving : ∀ z ∈ Z, extractor z.IsProverPreserving protocol.roles`. Literally at every oracle message edge, for every after-witness satisfying the after-state, its mapped before-witness satisfies the before-state; this property recurses for **all** messages and subsequent moves. For general public sender edges there is the same preservation condition; the present protocol has receiver public challenge edges and oracle message edges. There is no preservation condition imposed at receiver challenge edges.
- `bounded : ∀ z ∈ Z, IsLocallyBounded (extractor z) protocol.roles (roundErrorSchedule rounds errors)`. Here `errors : Fin rounds.length → ENNReal`. The schedule assigns uniform native challenge sampling and error `errors j` to each round, independent of the message, then recurses for all messages/challenges. At each receiver challenge edge the local bad event is `∃ afterWitness, ¬ before.holds (map afterWitness) ∧ after.holds afterWitness`. Its uniform challenge probability must be **≤** that round's error, at every recursively selected state. Thus the local bound concerns existence of any bad after-witness, not just a sampled or returned witness. These hypotheses cover all paths for each `z ∈ Z`, even unreachable or guard-rejected paths.
- `Rin : ∀ z, (state z).Witness → Prop` and `Rout : ∀ z path, W → Prop`.
- `terminalWitness : ∀ z path, W → (extractor z.terminalState path).Witness`, an ordinary function, not a required equivalence, injection, surjection, sampler, or computed certificate.
- `inputLaw : ∀ z u, state z.holds u ↔ Rin z u`.
- `outputLaw : ∀ z path w, Rout z path w → terminalState.holds (terminalWitness z path w)`. Only this implication is required, not its converse. Input/output laws are global for **all** `z`, paths, and witness values, even outside `Z` and outside execution support; preservation and local bounds are restricted to `z ∈ Z`.

There is no existential conclusion constructing any of this data. The theorem is conditional on already supplied state, extractor, terminalWitness, and laws.

Define the resulting input witness `I(z,p,w) = (extractor z).extractWitness p (terminalWitness z p w)`. The literal event `badStoppedRelation ... Z result` is `False` for `none`, and for `some (z,p,w)` is exactly

`z ∈ Z ∧ Rout z p w ∧ ¬ Rin z I(z,p,w)`.

It concerns failure of this particular supplied extraction map, not the nonexistence of any input witness satisfying `Rin`. No separate actual verifier, accepted-claim object, or arbitrary oracle terminal-verification program appears in the execution. Acceptance within the event is expressed by `Rout` and the successful stopped completion.

## Exact security inequalities and budget scope

`keyError errors k` selects the error for the round of `k`; it recurses through right keys by advancing the `Fin` index. Write `εmax = Finset.univ.sup errors` and `εsum = ∑ j, errors j`. All arithmetic is `ENNReal`, including its usual infinite values and `0 * ∞ = 0` convention.

`freshKeysOfLog` is the finite set of distinct keys appearing in the hash log. `freshQueryCharge weight log` sums weight over that set once per key. `expectedFreshQueryCharge P weight` integrates this charge over `randomOracleLoggedRun P` with default empty cache. It does not count uniform/internal sampling queries or repeated hash queries more than once; no cache hits are separately charged. The integral is nonnegative and extended-valued with no integrability hypothesis.

`codec.encodedWeight (keyError errors) d` is `0` if `decode d = none` and `keyError errors k` if `decode d = some k`.

`encodedExternalStopped_knowledge_soundness_sharp` has implicit `Input Salt C D W : Type`; its only explicit typeclasses are `[DecidableEq D] [SampleableType C]`. It quantifies explicitly, in order, over `rounds`, `common`, `codec`, `guards`, `errors`, `external`, and then all security data/hypotheses in the preceding section, in the listed order. The source writes unannotated `KnowledgeState` here, rather than explicitly naming `KnowledgeState.{w}`; elaborator-generated universe binders were not independently inspected. Its conclusion is precisely

`Pr[joint ← randomOracleLoggedRun X empty; badStoppedRelation ... joint.1.1]`

`≤ expectedFreshQueryCharge X (codec.encodedWeight (keyError errors))`.

The charged program is the **whole actual external adversary followed by encoded stopped completion**, so its distinct-key set includes queries before and during completion. An adversary/completion overlap at one image key is charged once. Off-image keys are uncharged, but their responses can affect the adversary and event. No fixed query budget `Q` is assumed; the RHS is an expectation of the actual distinct queried image keys, weighted by round. No clipping at one is present. The proof opens `classical` to provide native equality decisions internally; `[DecidableEq Input]` and `[DecidableEq Salt]` are not extra hypotheses in this exported theorem.

`encodedExternalStopped_knowledge_soundness_adversaryCount` has exactly the same source parameters, hypotheses, typeclasses, unannotated KnowledgeState usage, and event. Its conclusion is

`Pr[joint ← randomOracleLoggedRun X empty; badStoppedRelation ... joint.1.1]`

`≤ εmax * expectedFreshQueryCharge external (fun _ => 1) + εsum`.

Here the cost program is **external alone**, with empty initial external cache: all its distinct `D` hash keys are counted, including off-image keys. Completion is accounted for by the sum of all round errors, even if guards stop early or completion repeats adversary keys. This theorem supplies a probability bound, not an equality of costs. It also has no fixed or worst-case adversary query bound parameter.

`encodedNativeReduction_knowledge_soundness` in `EncodedSecurity` has an independently polymorphic witness universe `w` (`state : Input → KnowledgeState.{w}`) and explicit instances `[DecidableEq Input] [DecidableEq Salt] [DecidableEq D] [SampleableType C]`. It quantifies over `rounds`, `common`, `codec`, `external`, `guards`, `errors`, then the same security data/hypotheses. It states

`Pr[joint ← randomOracleLoggedRun J empty; badStoppedRelation ... joint.1.1.1]`

`≤ εmax * expectedAdversaryFreshKeys rounds B + εsum`.

This theorem's event is on the native source-logged restored execution of the derived native adversary, rather than directly on the external run. `expectedAdversaryFreshKeys` is the expectation of the number of distinct **native hash** keys in the adversary phase alone; its definition runs `B.withQueryLog` with an empty native cache and uses the outer native hash log. Private off-image sampling coins do not contribute to that count. The native theorem itself does not assume a bound by the external count; the later external-count theorem obtains one via the inspected cost transport.

## Remaining exported statements in the three main modules

The following are identities of **OracleComp programs**, rather than merely denotation identities, unless specified otherwise. General implicit output types in the helper statements are `A B : Type`.

In `EncodedCompletion`:

- `StrictCodec.routeProgram_map`: for any map `f : A → B`, external program, and arbitrary initial off-cache, routing a mapped result equals routing first and mapping only its output; external log and off-cache coordinates are retained. Requires `[DecidableEq D] [SampleableType C]`.
- `encodedCompletionQuery_route`: for any key and off-cache, routing its encoded completion query equals a common query at that key, returning the inverse-converted native answer, logging the singleton encoded external key/common answer, and leaving off-cache unchanged. Same two classes.
- `encodeCompletionLog_nil` and `encodeCompletionLog_append`: encoding a native log by `(k,u) ↦ (encode k,e_k u)` preserves empty and append, for arbitrary logs, without execution assumptions or typeclasses.
- `encodedCompletion_routeProgram`: for any native-only program `P : OracleComp N A` and off-cache, routing `simulateQ encodedCompletionQueries P` equals running `P.withQueryLog` through commonCompletionQueries, then returning `((output, encodedNativeLog), originalOffCache)`. Same two classes. The log on the right is the executed native query sequence with key and answer conversion; all its queries are image queries externally.
- `commonCompletionQuery_native`: for every key, simulating its commonCompletionQueries query natively cancels `e_k.symm` with `e_k` and equals the direct restoration query. No sampler/equality classes.
- `commonCompletion_native`: this cancellation extends to every native-only program `P`; the result equals `simulateQ restorationQueries P`, with no additional hypotheses.
- `commonCompletion_native_eraseLog`: running `P.withQueryLog` through common completion and native simulation, then projecting its output, equals direct restoration simulation of `P`. No additional hypotheses.
- `randomizedStoppedExecution_eraseSourceLog`: for every rounds/guards/native adversary, erasing the source log from the source-logged stopped native execution equals nativeStoppedExecution. No equality/sampler classes beyond those inherited by definitions.
- `encodedRoute_nativeValue_bind`: for every external `program`, continuation `next : A → OracleComp (unifSpec + E) B`, and off-cache, projecting the value of their routed, natively simulated bind equals running the first routed/simulated phase and then routing/simulating the selected continuation with first's resulting off-cache before value projection. Requires the same two classes; no reachability hypothesis.
- `encodedExternalCompletion_route_value`: for every selected `Option` and every off-cache, projecting the output of routed/simulated encoded completion equals nativeStoppedCompletionAfter on that selection. Same two classes. In particular the value is independent of off-cache because completion queries only image points; this does not claim output log/cache equality.
- `encodedExternalStopped_route_nativeValue`: for every external adversary, projecting the value of routed/simulated whole stopped external execution starting from empty off-cache equals nativeStoppedExecution of the derived native adversary. Same two classes. This structural equality is later run under native random-oracle semantics and used to establish external event-law transport.

In `EncodedSecurity`:

- `expectedAdversaryFreshKeys_eq_expectedFreshQueryCharge`: with decidable equality on Input and Salt, for every rounds and every native randomized adversary, its expectedAdversaryFreshKeys equals `expectedFreshQueryCharge adversary (fun _ => 1)`. This is an equality of ENNReal expectations; source logging does not alter the outer hash-key count.
- `CommonChallenge.ofRoundEquivs`: constructs common fibres from **supplied** `equivs : ∀ round, round ∈ rounds → round.Challenge ≃ C`. At a key in a round it selects that round's equivalence. It needs no sampler or equality class. This sufficient assumption is stronger than per-existing-key equivalences when a round has no existing keys.
- `encodedNativeAdversary_expectedKeys_eq_route`: with all four equality/sampler classes used by native security, for every rounds/common/codec/external, native adversary's expected distinct keys equals the expected unit charge of `common.simulateNative (codec.routeProgram external empty)`. Erasing returned routing log/off-cache does not change executed native hash queries.

The imported `OracleComp.randomOracleLoggedRun_mapResult` from `RandomOracleCost` is polymorphic in `D A B : Type` and reply family `R : D → Type`, requires decidable equality on D and certified samplers for every reply, and quantifies over any program, any `f : A → B`, and any initial hash cache. It asserts program equality: mapping the program output changes only the output coordinate in the logged run, retaining log/final cache. `OracleComp.expectedFreshQueryCharge_map` requires the same classes and arbitrary program/map/weight, and states equality of expected weighted distinct-key costs before/after output mapping, with default empty cache. Neither assumes injectivity, measurable `f`, or preservation of output values; cost ignores that coordinate.

## Scope, limitations, and vacuity

The execution/event transport permits arbitrary adaptive total external queries, including repeated and off-image keys. It assumes a fixed codec and fixed per-key answer bijections, so it does not describe a key encoder or answer encoding changing during a run. The statistical claims use uniform lazy random-oracle answers; they are not claims about a particular implemented cryptographic hash. No bound on decoder running time, sampler coin count, total query count, or extractor running time is given.

The security event is unconditional and has non-strict bound `≤`. It excludes all `none` outcomes rather than conditioning on successful completion. The cost expectations still include their logs: adversary queries remain charged if the adversary returns none, and earlier completion queries remain charged if a later guard aborts. There is no division by completion probability. Result-law transport includes none outcomes even though badStoppedRelation ignores them.

Theorems require global local challenge bounds for all states and moves of inputs in Z; they do not infer such bounds from guards or execution support. Input/output laws alone do not establish preserving or bounded. Conversely no preserving/bounded condition is needed outside Z. No protocol transcript validity, relation computation, or oracle-interface evaluation is automatically supplied by the generic Rout predicate and guard schedule.

There are several permitted trivial cases: Z empty, Rout everywhere false, external always returning none, or guards preventing every nonempty-round completion make the event impossible. Terminal witness types may be empty, and maps to them can force W or reachable selections to be empty; the theorem only applies when the supplied total functions actually exist. With no rounds, the error supremum and sum are zero, keys are empty, and extraction is the identity at the initial state, so inputLaw/outputLaw make the bad event impossible. `CommonChallenge` is vacuous over an empty key space, although `SampleableType C` still requires finite nonempty C. When keys exist, common fibres require every existing native fibre to be equivalent to the same C; unequal accessible cardinalities preclude such a parameter. StrictCodec likewise cannot be supplied if the native key set cannot inject into D.

Errors may exceed one or be infinite; no bound restricts them to probabilities. A right-hand side ≥1 yields only a trivial probability inequality, and an infinite right-hand side is permitted. Empty external/native caches are essential to the displayed main formulas; there is no main theorem here for arbitrary correlated initial external/native cache states. The helper definitions retain arbitrary caches where explicitly quantified, and earlier fibre/codec identities are stronger, but that does not insert a nonempty-cache parameter into these event/security conclusions.

Source inspection resolves all custom predicates and computations needed for the literal read-back. Large import dependencies were read selectively for relevant definitions. No build or axiom check was performed; conclusions describe the supplied source under its intended successful elaboration, not an independent Lean verification.

**READBACK COMPLETE**
