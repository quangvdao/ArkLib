# Blind code-only statement read-back: encoded fibres

Status: **READBACK COMPLETE**

This is an independent mathematical translation of comment-stripped Lean code. The inputs were the supplied blind protocol and modules read exclusively with `python3 /tmp/arklib-third-run-20261004/blind/read-encoded-fibre-module.py MODULE`. No author prose, intended contract, other reports, git history, source comments, edits to Lean, builds, or delegation were used. This document gives no fidelity verdict and does not certify elaboration, proof checking, or axioms. The initially missing snapshot paths were corrected by the parent before successful source reads.

## Source identities

The reader identifies ArkLib inputs as `encoded-fibre-checked-0855:ArkLib/...`. VCVio and PolyFun inputs came from `/Users/quangdao/Documents/Lean/.third-run-deps-20261004/{VCVio,PolyFun}/...`. SHA256 values below are those returned by the reader for source inputs, not hashes of this report.

| Module | SHA256 | Inspection scope |
|---|---|---|
| ArkLib.Interaction.Oracle.Security.EncodedFibreCoupling | bcfcaf14a7bae64ef084058125e95afbc99d0e2e8396c46477d437e1d4a5bdfb | Complete main module |
| ArkLib.Interaction.Oracle.Security.EncodedFibreCost | c9cf648fa7a33d86f874766f8c5ceaa40a9034c447936db393fb9fc0b95a7ed0 | Complete main module |
| ArkLib.Interaction.Oracle.Security.EncodedFibre | 63bbebb61d4afe46be7f04592a48dda6add5e16f164b02bbf07dfa6b85947a6f | Complete defining dependency |
| ArkLib.Interaction.Oracle.Security.EncodedWeighted | 07c21afbe908d9086142e65b15744cb2419adbf87e1da5b9f5ade7a2278a79a7 | Complete dependency |
| ArkLib.Interaction.Oracle.Security.EncodedLog | cb7573546c31e47e35a7302f18fad03f895c89d9c23ee6feb92424ca218b0d36 | Complete dependency |
| ArkLib.Interaction.Oracle.Security.EncodedReduction | 5c6bc83bb71d713907b26a585152b2eca2ff5d20a1fbc8b1c9c66d83d762e2de | Complete dependency |
| ArkLib.Interaction.Oracle.Security.EncodedCodec | 89dee413727f50ce3956c3ff8de15366fce224a6814119ce331ae11a7145bafb | Complete dependency/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget | 5bd91b535a579152292ede55427b5e1ee943c2948221da32ff5346af20194e1f | Import trace; broad reader output |
| ArkLib.Interaction.Oracle.Security.StateRestorationStopped | a4926c1e185adb683c9e536b0e8a2db2307c8aa77552a87ec159a51ec4d2f23d | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationRandomizedKnowledge | 3a8ba39e8e686e91edb6a17e36014c79f1d2547214004c26bc83f022f6a98587 | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationRandomized | 01a72e2880ed62d1d3651541bf04cbb45a92f4426e4266cd28f424e34aa271ff | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationBudget | 3ed9356728b3a5915a40995e5fff7de10279ccca4364a9fc387f619dfd618d11 | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationOracle | 4071a02710153a7cfcf59c97e84f4a1d283abf2bb35518ca0b76201c3c3f21c8 | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationGame | 0e6d2b7e7a60ae5b696faa97147c818c4dcbb47741e8373f54bc8193fe90bcda | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestorationReplay | ff7361e968a6d3b4d85a0b8013f9b8c53911d4538c15d9b71387e781112c1860 | Header/import trace |
| ArkLib.Interaction.Oracle.Security.StateRestoration | 63df21e0ed1135f771e7c26e7c69a1bc53e96d5c391c923b58a5dba54057e70a | Relevant Round, Key, Challenge, Table, oracleSpec definitions/instances |
| VCVio.OracleComp.Constructions.SampleableType.NativeMeasure | 5ac619e19a68c8bc9c6a0fb53cb8e85a3c6be2a7ef056ec7533e65ac25e04d5b | Complete defining dependency |
| VCVio.OracleComp.Constructions.SampleableType.Basic | 09d7e9ef3fe9cf7db1cb5fa0c418a7a2bd87f354183c661f7cc73a446d32b0b1 | Complete sampler interface and instances |
| VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun | 8eaacb6ca6cbde5c9597230cbf33fc8490f8458a1d85ed32628f426cfe05d0ca | Complete log/cost definitions |
| VCVio.OracleComp.QueryTracking.RandomOracle.Simulation | 8b1b7afb0255710be0c6d56552f5614642d0d719572d97fe061e0f750d76b0dd | Relevant forwarding/import definitions |
| VCVio.OracleComp.QueryTracking.RandomOracle.Basic | 59cda869ab9dc306b115caebefe8b803f9f5eff7c9ab2f52eb61925c3130be94 | Complete random-oracle step definition |
| VCVio.OracleComp.QueryTracking.Structures | 27272773baa1f5441479b9297e8fa3afab8b39f421b8e98a4432709ab3bdfa08 | Relevant cache, update, log definitions |
| VCVio.OracleComp.ProbComp.Basic | 365c2392c311efbcd756682dceea08307a66647d688f4228f985b55194392f6e | Complete ProbComp definition dependency |
| VCVio.OracleComp.OracleComp | 0524a502a8134694c6f6870d9601e4a416c7626f38ec7a66370b6483e78b14f6 | Relevant FreeM representation and induction |
| VCVio.OracleComp.SimSemantics.SimulateQ | 736b9b7f2c4d3e0f84d320fb4d3d911d7a78533a4d2b1b4de972c766604de5ba | Relevant simulateQ definition/laws |
| VCVio.OracleComp.EvalDist.Measure | d27a321916074ed464b3b2ef814aa4fca8b90dd01dd901d7357047e330d00619 | Relevant measure/import definitions |
| VCVio.OracleComp.EvalDist.MeasureSpec | 2bf465e2f15d7c8b0d69beee43c1e038529a9322b4411fb6aa4d013628b386ff | Uniform measure spec including unifSpec |
| VCVio.EvalDist.PFunctorMeasure.Core | ea13feff96270112fa3f5a525a78624cf7405c8165054c2bef77c16f281fb371 | Denotation and selected EvalDist instances |
| PolyFun.PFunctor.Free.Basic | 01d9ae11a502dd1d12fc0055c7e3fd60d26b96d2a649de6d8dff011c9f2e39b3 | Relevant FreeM representation |

`EncodedFibreCoupling` publicly imports `EncodedFibre`. `EncodedFibreCost` publicly imports `EncodedFibreCoupling` and `EncodedWeighted`. `EncodedFibre` publicly imports `EncodedWeighted` and `SampleableType.NativeMeasure`. The import chain through `EncodedWeighted`, `EncodedLog`, `EncodedReduction`, and `EncodedCodec` reaches `StateRestoration` via the StateRestoration modules listed above. This is a source-hash record, not an independently verified lockfile or compiled-environment record.

## Definitions needed to read the statements

All principal declarations are in `Interaction.Oracle.Security.StateRestoration`; the following shorthand is local to this report.

Fix implicit parameters `Input Salt C : Type` and `rounds : List Round`. A `Round` contains types `Message` and `Challenge`, an `OracleInterface Message`, a decidable equality and finiteness witness for `Message`, and finiteness, nonemptiness, and a `SampleableType` instance for `Challenge`. These fields become instances. Round message types are allowed to be empty.

Let `K = Key Input Salt rounds`. Its literal recursive definition is:

- For no rounds, `K = Empty`.
- For `round :: tail`, `K = (Input × round.Message × Salt) ⊕ (round.Message × Salt × Key Input Salt tail)`.

A left key identifies the current round with input, message, and salt. A right key includes an earlier message/salt and a later key recursively. Its challenge type `F(k) = k.Challenge` is the current round's challenge for a left key, or the later key's challenge for a right key. Thus keys contain message/salt prefixes and the input carried by the selected nested key; they contain no challenge prefix. `oracleSpec Input Salt rounds = OracleSpec.ofFn Key.Challenge`, so a native query at `k` returns a value in `F(k)`. Round fields induce `Finite F(k)`, `Nonempty F(k)`, and `SampleableType F(k)` for every key. Decidable equality on `Input` and `Salt` induces decidable equality on `K` using the round message equalities.

A `CommonChallenge Input Salt C rounds` has exactly one field:

`fibre : ∀ k : K, F(k) ≃ C`.

Write this supplied bijection as `e_k`. It is fixed before the program and cache are quantified; it may depend arbitrarily on `k`. There is no coherence condition between different keys. It is not a merely surjective map or a proof of equal cardinality: the caller supplies the actual equivalences.

Let `N` be the native oracle and `H = K →ₒ C` the constant-answer oracle. A cache for either oracle is a total dependent function assigning an optional answer to every key. It is not restricted to finite support, reachability, or consistency with a previously sampled table. Empty cache assigns `none` everywhere. `cacheQuery k u` updates the single key to `some u` and leaves every other key unchanged.

For native cache `c`, define `E(c)(k) = Option.map e_k (c(k))`. Consequently `none` remains `none`, `some u` becomes `some (e_k u)`, and all unqueried preexisting entries are included. For a native log `L = [(k_i,u_i)]`, define `Elog(L) = [(k_i,e_{k_i}(u_i))]`, retaining order and repetitions. Logs are lists of dependent key/answer pairs. `encodeJoint ((a,L),c) = ((a,Elog(L)),E(c))`; its output coordinate `a : A` is left unchanged. This operation does not recursively transform native data embedded inside an arbitrary output type `A`.

`simulateNative P` replaces every common oracle query at `k` with one native oracle query at the same key followed by `e_k`, and forwards every uniform query unchanged. More precisely the available oracle queries are `inl n`, returning `Fin (n+1)`, and `inr k`, returning a hash/challenge answer. `simulateQ` interprets the entire free computation using these replacements, including continuations dependent on earlier answers.

Write `R_N(Q,c)` and `R_H(P,d)` for `randomOracleLoggedRun` on the respective oracle. These return probabilistic computations with joint result `((output, hashLog), finalCache)`. Each hash query checks its cache: a hit deterministically returns the cached answer and the same cache; a miss samples uniformly from its answer type and stores the result. Both hits and misses append one key/answer pair to the hash log. Repeated hash queries are logged repeatedly. Uniform queries are forwarded as fresh random choices, append no hash log entry, and do not change the hash cache. Uniform choices inside an answer sampler likewise do not appear in this hash log.

`ProbComp A = OracleComp unifSpec A`. Its measure semantics interprets a uniform query `n` as the uniform probability measure on `Fin (n+1)`, a pure return as a Dirac measure, and a query continuation by measure bind. The displayed `𝒟[...]` is this measure denotation. The theorems explicitly choose `MeasurableSpace := ⊤` on their joint result types: every subset is measurable. They do not ask the caller for a topology, measurable output function, countability of `Input`, or countability/finiteness of the cache space.

`SampleableType C` is a class containing a `selectElem : ProbComp C` AND a proof that, for every measurable structure with measurable singletons, its denotation is `uniformOn Set.univ`. Its library instances prove that a sampleable type is finite and nonempty. This is a uniform-law certificate, not an unchecked algorithm named a sampler. The native fibres use their existing round sampler instances, not instances constructed by inverse transport from the supplied sampler of `C`.

## Main full-joint probability statement

`CommonChallenge.evalDist_randomOracleLoggedRun_simulateNative` quantifies, in order, over implicit `Input Salt C : Type`, implicit `rounds : List Round`, a supplied `common : CommonChallenge Input Salt C rounds`, instances `[DecidableEq Input] [DecidableEq Salt] [SampleableType C]`, an implicit output type `A : Type`, **every** program

`P : OracleComp (unifSpec + (K →ₒ C)) A`,

and **every** native cache `c : N.QueryCache`. Its entire conclusion is

`𝒟[encodeJoint <$> R_N(simulateNative P,c)] = 𝒟[R_H(P,E(c))]`,

with the powerset measurable space on `((A × QueryLog H) × H.QueryCache)`.

There are no other explicit predicates, event hypotheses, query bounds, restrictions on initial cache contents, or restrictions on the program's choice of keys. The common-side initial cache is precisely the pointwise conversion of the native cache; it is not separately and independently chosen. Via the inspected cache equivalence, every common cache also has a native preimage, although the theorem is stated with the native cache as its argument.

The equality concerns the entire joint distribution, including correlations among the unchanged output, the complete converted hash log, and the complete converted final cache. Thus any event on that triple has exactly equal probability, and any nonnegative observable on that triple has exactly equal integral after conversion. This implication uses measure equality; the main statement itself does not name an event or a probability bound.

This is an equality of **denotations**, not an equality of probabilistic computation syntax, sampled random coin tapes, or a pointwise execution identity under a preselected common random tape. The theorem does not construct an explicit coupling object or relate sampler running times. Existing native and common uniform samplers can have different implementations or numbers of internal random choices while having the required laws.

## Other exported statements in EncodedFibreCoupling

The structural statements require `common`, with implicit `Input Salt C` and `rounds`, but require no sampler instances unless indicated below.

- `toCommonCache_apply`: for every native cache `c` and key `k`, `E(c)(k) = Option.map e_k (c(k))`.
- `toCommonCache_empty`: `E(empty) = empty`.
- `toCommonCache_update`: with decidable equality on `Input` and `Salt`, for every cache `c`, key `k`, and native answer `u : F(k)`, `E(c.cacheQuery k u) = E(c).cacheQuery k (e_k u)`. There is no miss hypothesis; this also holds for replacement of an existing answer.
- `toCommonLog_nil`, `toCommonLog_append`, `toCommonLog_single`: respectively empty maps to empty; conversion commutes with list append for all two logs; and `[(k,u)]` maps to `[(k,e_k u)]`.
- `simulateNative_uniformQuery`: for every `n : Nat`, simulation of the single common uniform query equals the single native uniform query as **OracleComp programs**, returning `Fin (n+1)`.
- `simulateNative_hashQuery`: for every key `k`, simulation of the single common hash query equals `e_k <$> nativeHashQuery(k)` as **OracleComp programs**. This is a replacement identity, not equality with common-side uniform sampling syntax.
- `evalDist_randomOracle_step`: with `[DecidableEq Input] [DecidableEq Salt] [SampleableType C]`, for every `k` and native `c`, the law of `(e_k(answer), E(finalCache))` from the native lazy-oracle step at `k` and `c` equals the law of the common lazy-oracle step at `k` and `E(c)`. Result measurable space is the powerset of `C × H.QueryCache`. Both cache hits and misses are included.
- `evalDist_logged_hashQuery`: with the same instances, for every key and native initial cache, the full converted joint law for the simulated single hash query equals the common single-query joint law. The output here is `C`; the converted log is the singleton containing that same common answer.
- `evalDist_logged_uniformQuery`: with the same instances, for every `n` and native initial cache, the full converted joint law for the simulated single uniform query equals the common single-query law. The output here is `Fin (n+1)`, the log is empty, and the initial cache is retained after conversion.
- `encodeJoint_append`: for arbitrary implicit output types `A B`, arbitrary joint triples `first : ((A × logN) × cacheN)` and `second : ((B × logN) × cacheN)`, conversion of the triple made from second's output, first's log followed by second's log, and second's cache equals second's output with the two converted logs appended and second's converted cache. No consistency or execution hypothesis on the two triples is present.

`evalDist_logged_bind` has the same three typeclass requirements and supplied `common`, implicit types `A B`, and four independently supplied programs/continuations:

`nativeFirst : OracleComp (unifSpec + N) A`, `commonFirst : OracleComp (unifSpec + H) A`,

`nativeNext : A → OracleComp (unifSpec + N) B`, `commonNext : A → OracleComp (unifSpec + H) B`.

It assumes `firstLaw`: **for every native initial cache**, the converted full joint law of nativeFirst equals the full joint law of commonFirst started from the converted cache. It separately assumes `nextLaw`: **for every `a : A` and every native initial cache**, the converted full joint law of `nativeNext a` equals the full joint law of `commonNext a` started from the converted cache. These laws are quantified over all caches and all `a`, not only reachable caches or supported intermediate values. They use the respective powerset joint spaces. Given any native initial cache, its conclusion is the same full joint law equality for `nativeFirst >>= nativeNext` versus `commonFirst >>= commonNext`, with logs concatenated in execution order and the first final cache handed to the second run. Neither law assumes the pairs of programs are syntactically simulations of each other. The stronger all-values/all-caches hypotheses imply the sequential result.

The module's `evalDist_bind_transport` is private. It is a measure-level compositional helper: given prefix-law equality after an arbitrary encoding and continuation-law equality at every native prefix value, it concludes equality of the bound final distributions. It is not an additional exported security assumption.

For completeness, the defining dependency's `CommonChallenge.evalDist_fibre_uniform` requires supplied `common`, `[SampleableType C]`, and any key `k`, and asserts `𝒟[e_k <$> uniformSample F(k)] = 𝒟[uniformSample C]` with powerset measurable space on `C`. Its native sampler is the round-induced instance. The proof rewrites both denotations to uniform measures and uses bijectivity.

## Cost statements

`freshKeysOfLog L` is literally `(L.map Sigma.fst).toFinset`: all distinct keys occurring anywhere in the log. It does not subtract a preexisting cache domain, select misses using a cache observation, or preserve multiplicity. `freshQueryCharge w L = ∑ k ∈ freshKeysOfLog L, w(k)`. Here `w : K → ENNReal` has values in the extended nonnegative reals and may take `∞`.

`expectedFreshQueryCharge Q w` is the nonnegative Lebesgue integral of `freshQueryCharge w` over the hash-log coordinate of `randomOracleLoggedRun Q`, **with its default empty initial cache**. Its result is `ENNReal`; no finiteness or integrability hypothesis is imposed. For this default empty cache, a distinct logged key is a key first encountered during that run, and subsequent repeated queries incur no additional charge.

`CommonChallenge.freshKeys_toCommonLog` has implicit `Input Salt C`, `rounds`, the two decidable-equality instances, supplied `common`, and **every native log** `L`. It states

`freshKeysOfLog (Elog(L)) = freshKeysOfLog L`.

No sampling, execution, log consistency, or support assumption is needed. This is equality of finite sets of the same keys, because only answers are converted.

`CommonChallenge.expectedFreshQueryCharge_simulateNative` has implicit `Input Salt C A : Type`, implicit `rounds`, `[DecidableEq Input] [DecidableEq Salt] [SampleableType C]`, supplied `common`, **every** program `P : OracleComp (unifSpec + H) A`, and **every** fixed function `w : K → ENNReal`. It states exactly

`expectedFreshQueryCharge (simulateNative P) w = expectedFreshQueryCharge P w`.

Equivalently, starting both executions from empty hash caches, the expected sum of `w(k)` over distinct logged hash keys is equal. The weight is fixed before the execution, may depend on the complete key, and does not depend on answers, logs, or run outcomes. No bound is claimed on its common value; equality can be `∞ = ∞`. Uniform queries and the number of internal sampling operations incur zero charge in this definition. The theorem does not state preservation of total hash-query count, total random-choice count, running time, or arbitrary dynamically chosen weights, although other observables of the converted hash log can be transported using the full-joint law. The expected-cost theorem has no nonempty-cache parameter; the separate pointwise log-set identity holds for arbitrary logs.

## Adaptivity, failure, and boundary cases

The program quantifier ranges over the inductive free oracle-computation type, with pure returns and query nodes whose continuations depend on the received answer. The statement includes keys, later uniform-query sizes, output values, and stopping decisions chosen adaptively from previous answers. Neither adaptivity nor repeated keys need an additional hypothesis. It does not require the program to follow the protocol rounds, choose a valid protocol transcript, or satisfy a guard schedule. The round list supplies the native key/answer family; execution is an arbitrary program over that family.

These are total FreeM computations with nonempty finite reply types, not arbitrary partial algorithms or an infinite interaction. There is no primitive failure constructor in the quantified `OracleComp ... A`. An `Option B` output can be chosen as `A` and can return `none` as ordinary data; that outcome and its log/cache remain in the probability measure and are not conditioned away. There is no exceptional-state restoration theorem, no rejection-conditioning assumption, and no failure-probability inequality in these two main modules. The native/common lazy steps always return either a preexisting answer or a certified uniform sample. The inspected discrete FreeM measure semantics gives total mass one for these resulting ProbComp computations.

No `Finite Input`, `Finite Salt`, `Nonempty Input`, `Nonempty Salt`, or inhabited-round-message hypothesis appears. Consequently the key space can be infinite or empty. Arbitrary initial caches can contain infinitely many preexisting entries. The result uses lazy per-key sampling, not a `SampleableType` instance for an entire table over all keys.

The supplied `common` hypothesis can be uninhabited: if two accessible native fibres have different finite cardinalities, they cannot both be equivalent to the same `C`. The theorem is then a conditional statement with no such `common` to instantiate. Whenever the key space is nonempty, its fibres are finite and nonempty and the supplied equivalences force `C` to have that same cardinality for every existing key. The `[SampleableType C]` hypothesis separately excludes empty and infinite `C`, including when there are no keys.

With `rounds = []`, the key type is `Empty`, all hash logs are empty, and all caches have the unique empty-key function. `CommonChallenge` then places no fibre constraint on `C`; nevertheless the probability/cost theorem still requires its sampleability. Other causes of an empty key space include empty `Input`, empty `Salt`, or message-type emptiness eliminating all key constructors. The main law reduces to forwarded uniform randomness and unchanged output in such cases, and the expected distinct-hash-key charge is zero. A pure program likewise has empty log and zero cost for every weight, while the probability result retains and converts its arbitrary initial cache. For a uniform query with `n = 0`, `Fin 1` makes the choice deterministic; the helper theorem includes that boundary. No strict versus non-strict event boundary occurs in the main statements: they are equalities, not threshold events.

## Verification limits

All mathematical definitions essential to this translation were inspected through the permitted reader; only relevant portions of large semantic/import dependencies were selected. Some broad imported StateRestoration bodies were incidental to finding definitions and do not supply hypotheses to these main theorems. No compiled declaration signatures, environment axiom listing, build, or Lean elaboration check was performed because the assigned task prohibited builds. The displayed binders and instances therefore describe the supplied source statements, subject to their successful elaboration in the parent-checked environment. No unresolved semantic definition needed by the main probability or cost statement remains in this read-back.

**READBACK COMPLETE**
