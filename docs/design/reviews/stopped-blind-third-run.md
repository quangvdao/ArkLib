# Blind read-back of revised Lean statements

This is a code-only reading of the comment-stripped modules pinned by `read-revised-module.py` to ArkLib revision `927ae390a`. I compared those outputs only with the earlier reader's pinned code output (`849d526164a4c0c50d31aea9ef59ddeae842eca0`). I did not inspect a contract, paper, design document, PR prose, author commentary, unstripped source, or another review.

## Source identity and imports

| Module | Revised source SHA-256 |
| --- | --- |
| `ArkLib.Interaction.Oracle.Security.StateRestorationStopped` | `a4926c1e185adb683c9e536b0e8a2db2307c8aa77552a87ec159a51ec4d2f23d` |
| `ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget` | `5bd91b535a579152292ede55427b5e1ee943c2948221da32ff5346af20194e1f` |
| `ArkLib.Interaction.Oracle.Security.StateRestorationStoppedFinite` | `8470a375cd0361aedb8cc8d491bbb54f2257ec2dc9b6f8ef64291de84931d17c` |
| `ArkLib.Interaction.Oracle.Security.StateRestorationRandomizedKnowledge` | `3a8ba39e8e686e91edb6a17e36014c79f1d2547214004c26bc83f022f6a98587` |
| `ArkLib.Interaction.Oracle.Security.StateRestorationRandomized` | `01a72e2880ed62d1d3651541bf04cbb45a92f4426e4266cd28f424e34aa271ff` |
| `ArkLib.Interaction.Oracle.Security.StateRestorationBudget` | `3ed9356728b3a5915a40995e5fff7de10279ccca4364a9fc387f619dfd618d11` |
| `ArkLib.Interaction.Oracle.Security.StateRestoration` | `63df21e0ed1135f771e7c26e7c69a1bc53e96d5c391c923b58a5dba54057e70a` |
| `ArkLib.Interaction.Oracle.Security.Knowledge` | `803dbe0bc24e46178b9384d9a0fc5ed87c90b6f4e24971f2bcc46fb5e39cd22b` |
| `VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQuery` | `7914b36b08ab53edfd4bcf79c598f4e02cbc430457980271ec59425192350860` |
| `VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite` | `c9b848b60573d5bffcb73e754410c299b4ef3a2082dfbfbe18d75a772ee3a4e9` |
| `VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun` | `8eaacb6ca6cbde5c9597230cbf33fc8490f8458a1d85ed32628f426cfe05d0ca` |

`StateRestorationStoppedFinite` directly imports `StateRestorationStoppedBudget`, which imports `StateRestorationStopped`, which imports `StateRestorationRandomizedKnowledge`. The relevant VCVio dependencies are from the pinned private dependency copy described in the packet as VCVio `6bf6c91`; the reader reports their file hashes above.

## Quantified objects and winning event

`Input`, `Salt`, and `W` are arbitrary types; the state witness type is in universe `w`. A `Round` supplies a finite, decidable-equality message type and a finite, nonempty, sampleable challenge type. A list `rounds` fixes the protocol and a dependent hash key type. `RoundErrors rounds` is a function from the finite round index to `ENNReal`, without a finiteness or probability-range requirement. Security theorems require `[DecidableEq Input]` and `[DecidableEq Salt]`, but not finite input or salt types unless explicitly stated in the finite module. An adversary is an arbitrary oracle program using uniform and hash queries that returns either `none` or `some (z,messages,witness)`.

The stopped completion checks each Boolean guard before its corresponding hash query. Its next guard schedule depends on the challenge sampled for the current key. It produces a full path only if all guards pass; on adversary `none` or a failed guard, the selected result is `none`. The joint random-oracle run begins with an empty cache and returns `(selected result, attached adversary query log, joint hash-query log, final cache)`. The security event reads only the selected result. For `none`, `badStoppedRelation` is false. For `some (z,path,witness)`, it is exactly

`z ∈ Z ∧ Rout z path witness ∧ ¬ Rin z ((extractor z).extractWitness path (terminalWitness z path witness))`.

The extractor maps the supplied terminal-state witness backwards along the path to a witness in `state z`. The event does not itself test a log, count, guard predicate, or cache. The attached adversary log contains uniform and hash entries, with `.snd` filtering the hash entries. The joint hash log records keys and answers, including repeated queries.

The revised relation-facing theorems quantify a *function* `terminalWitness z path : W → (terminalState (extractor z) path).Witness` for **every** input and path. They assume `(state z).holds inputWitness ↔ Rin z inputWitness` for all inputs and input witnesses, and `Rout z path witness → (terminalState ...).holds (terminalWitness z path witness)` for all inputs, paths, and `W` witnesses. They do not require a reverse implication from terminal `holds` to `Rout`. The extractor remains assumed prover preserving and locally bounded for every `z ∈ Z`; local boundedness uses a uniform challenge at each receiver node and the corresponding round error over all possible branches, not merely guard-passing ones. These assumptions need not be satisfiable for arbitrary chosen states, relations, and maps; the theorems are conditional.

## Stopped probability and costs

`randomizedStopped_badRelation_le_expectedFreshCharge` says that the probability of the event on the stopped joint run is at most the expectation of `freshQueryCharge (keyError errors)` over that run. `freshQueryCharge` sums a key's round error once per *distinct* hash key in the entire joint log, regardless of repeated entries. The theorem does not assume a query limit.

`randomizedStopped_knowledge_soundness_actualAdversary` gives two inequalities. Write `εmax = Finset.univ.sup errors`, `q = expectedAdversaryFreshKeys rounds adversary`, and `v = expectedStoppedVerifierRoundCost rounds guards errors adversary`. Then the result is

`Pr[badStoppedRelation on stopped joint run] ≤ εmax * q + v`

and

`εmax * q + v ≤ εmax * q + ∑ j : Fin rounds.length, errors j`.

Here `q` is the expected cardinality of distinct hash keys in the adversary's own `withQueryLog` run from the empty cache; uniform queries do not enter this count. In the stopped joint run, `v` sums round errors over the suffix of the joint hash-query *list* after dropping as many entries as the attached adversary log has hash entries, and then takes its expectation. Thus repeated verifier queries can be counted repeatedly in `v`; the construction can stop before all rounds and charge fewer entries. `q` is independent of the guards. The first term uses the maximum round error for each distinct adversary hash key; the second uses each actual stopped-completion query's round error. The bound is in `ENNReal`, so infinite values can make it numerically uninformative.

The new `randomizedStopped_knowledge_soundness_queryBound` has the same relation and extractor assumptions and additionally quantifies `Q : ℕ` with `actualQueryBound`: for **every supported outcome** of `randomOracleLoggedRun adversary.withQueryLog ∅`, the cardinality of `freshKeysOfLog phase.1.2` is at most `Q`. This counts distinct adversary hash keys, without bounding uniform queries, repeated hash-query entries, or verifier queries. Its conclusion is `Pr[badStoppedRelation on stopped joint run] ≤ Q * εmax + ∑ j, errors j`. There is no strict inequality or additive constant. It follows by replacing `q` with its supportwise upper bound `Q` and `v` with the sum of all nominal round errors.

`guardPrefixAtKey_update` and its underlying definition are unchanged in the code comparison. It still says replacing a table answer at one key leaves the pair of (strict-prefix guard conjunction, guard at that key) unchanged, for every key and table, without a reachability assumption. The guard at a nested key may be evaluated even when an earlier guard has failed; the first Boolean records the failed prefix.

## New finite-table declarations

`StateRestorationStoppedFinite` adds `finiteTableSampler`: from `[Finite Input]` and `[Finite Salt]`, it constructs a dependent full-table `SampleableType` using finite keys and each round's finite challenge type. The equality theorems themselves explicitly require `[Finite Input]`, `[Finite Salt]`, `[DecidableEq Input]`, `[DecidableEq Salt]`, and `[SampleableType (Table Input Salt rounds)]`. The sampler is a supplied typeclass in these statements; the local `finiteTableSampler` definition is a way to construct one.

`evalDist_randomizedStopped_joint_eq_eager` identifies the *entire joint output distribution* of the lazy random-oracle stopped program with the distribution obtained by sampling a full table first and executing the same stopped program through `fixedTableLoggedRun` against that table. `evalDist_randomizedRestored_joint_eq_eager` makes the analogous assertion for the **unstopped** `randomizedRestoredExecutionWithAdversaryLog`, which runs `complete` after an adversary selection. Both start with empty caches and use the top measurable space on the joint result. These are distribution equalities, not pathwise equalities for a particular sampled table.

`eagerRestored_knowledge_soundness` uses the **unstopped** full restoration program in the second equality, without a guard schedule parameter. It samples a full table and runs `fixedTableLoggedRun` on `randomizedRestoredExecutionWithAdversaryLog`. With the same preserving, local-bound, relation-law, and terminal-witness-function assumptions, it bounds the `badStoppedRelation` event of that eager joint result by `εmax * expectedAdversaryFreshKeys rounds adversary + ∑ j, errors j`. The event predicate is reusable on the full restoration result because it consumes only `Option (z,path,witness)`; its name does not insert any guard into this theorem. The stopped eager distribution equality is separate; this module states no stopped eager knowledge-soundness theorem.

## Changes from the earlier pinned code

The normalized comment-stripped diff shows that the stopped relation and its soundness theorems replaced the all-path equivalence `W ≃ terminalWitnessType` with an all-path function `W → terminalWitnessType`. It also replaced the two-way terminal-holds/`Rout` law with the one-way law `Rout → terminal holds`. The event's extracted witness remains the function image followed by `extractWitness`; the old `extractInputWitness` helper was unfolded there. The input law remains two-way, and the guard, extractor, local-bound, and stopped cost definitions were unchanged in the inspected diff. The bounded-`Q` theorem and the entire finite-table module are new at revision `927ae390a` relative to the prior pinned reader output.

This report reads source definitions and statement text; it is not an independent Lean elaboration or axiom check. I found no unresolved ambiguity about which program the finite soundness theorem samples, what the event tests, or which queries the three displayed budgets count.

READBACK COMPLETE
