# Review of guarded restoration design note

Reviewed `/Users/quangdao/Documents/Lean/ArkLib-second-night/docs/design/guarded-restoration-open-questions.md` against the cited Lean definitions on 2026-10-03. This is an ordinary read-only design-note review, not a new proof or build result.

**Verdict: accurate overall; no blocking overclaim or prematurely closed design choice.** The note distinguishes proved results, candidate adapter obligations, and open choices. Its proposed adapter is expressly a restricted possibility, and its quantitative stopped-completion bound is expressly unproved.

Evidence for the proved-facts section:

- `Round` fixes a message type/interface and a challenge type with `Finite`, `Nonempty`, and `SampleableType`; the latter certifies uniform output measure (`StateRestoration.lean:36–53`, pinned `VCVio/OracleComp/Constructions/SampleableType/Basic.lean:49–57`). `Round.Message` has `Finite` but no `Nonempty`, so the note's warning about generic default messages is correct (`StateRestoration.lean:36–44`).
- Keys retain input plus preceding message/salt choices, not challenge replies. `keyExtractor` reads strict ancestor replies through the table, and `keyExtractor_update` makes its result invariant under replacement of the target reply (`StateRestoration.lean:55–74, 134–154`).
- Sumcheck's `claimState` is `checksPassed ∧ closedRelation` with `Unit` witness; recursive certificate construction accumulates each sum check, and the local bound is proved for arbitrary authored prefixes, including `checksPassed = False` (`StateRestorationCertificate.lean:49–75, 100–139`).
- `paddedStatement` returns `none` on the first failed sum check, and `replay_execute_eq` equates the *returned closed output* of `Native.execute` under replayed selected messages and coins with padded evaluation (`StateRestorationEvaluation.lean:27–37, 87–121`). It proves no equality of final caches or logs. The native branch is `none` on rejection, and samples a field challenge only after a passing check (`Protocol.lean:40–47, 109–120`). Uniform sampling from `Option F` would be a different law.
- The randomized completion runs after the adversary in one oracle computation, and the handoff theorem retains the exact cache and ordered source log (`StateRestorationRandomized.lean:190–222, 264–278`). The Sumcheck game replays that completed path and proves an output marginal and false-acceptance bound with a joint fresh-key charge (`StateRestorationSoundness.lean:158–172, 200–230, 256–279`). Its source adversary selects a full message sequence before completion, as the note says; it does not model arbitrary online next-message choices.

Two nonblocking wording improvements:

1. In the open-choice table's first row, “Rejected executions have different random-oracle logs and caches” is too categorical. Depending on whether padding queries are cache hits, final caches may coincide. “Rejected executions **can** have different random-oracle logs and caches” is exact. Source: the full `complete` queries one key per round (`StateRestoration.lean:229–237`) while the existing cache may already contain those keys (`StateRestorationRandomized.lean:264–278`).
2. “The current Sumcheck proofs discharge specialized versions of several obligations” should name which ones, lest a reader count candidate **prefix effect agreement** among them. `replay_execute_eq` is output equality, while the existing `complete` only queries challenge keys and `Native.execute` also evaluates message-oracle values before choosing a branch (`StateRestoration.lean:229–237`; `Protocol.lean:109–120`; `StateRestorationEvaluation.lean:110–121`). A new instrumented padded executor would be needed to formulate same-effects prefix agreement. Suggested sentence: “They establish persistent rejection, all-prefix local bounds, own-cell invariance, joint query accounting, and native output replay; prefix effect agreement for a generic guard remains open.”

Neither point changes the note's design boundary. The table correctly leaves the primary experiment, phase handoff, effectful tests, rejected-path extension, challenge transport, substantive witnesses, and machine cost unresolved. The candidate `J_pad` inequality tracks the existing expected fresh-key theorem (`StateRestorationRandomizedKnowledge.lean:326–352`); replacing its charge by a stopped run's charge is correctly described as requiring another argument.

Root disposition: both wording improvements were applied before publication. The note now
says rejected runs can differ in cache/log state and names the established owner and Sumcheck
obligations separately from the still-open prefix effect correspondence.
