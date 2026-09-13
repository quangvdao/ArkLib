# Varying-order Taylor traversal checkpoint

This checkpoint extends the fixed-order Taylor constructor with an executable separant scan and
dependent dispatch at each stage's actual active order. Positive stages call the existing checked
Taylor constructor at their smaller arity. Order zero is represented by a separate endpoint and
does not pass through the positive-order `0 < r < k <= p` guard.

`SemanticTraversal` proves that literal stored partial derivatives are the semantic separants.
Under `IsBelowCharacteristic`, `highestConcreteActive?` agrees with `highestActiveJet`, every
emitted derivative strictly decreases `jetDegreeMeasure`, and the initial measure supplies
canonical sufficient fuel. Consequently every bounded solution of a nonzero input equation
reaches an actual emitted stage where the stage equation vanishes and the selected separant is
nonzero. The caller supplies neither fuel nor a chosen regular stage.

`VaryingOrder` retains top, lower-positive and zero stages. Its dependent `EquationProducer` and
`ComponentProducer` preserve the smaller arity selected by each stage. `prefixEquation` is the
executable ambient-to-prefix adapter; `EquationProducer.ExactOn` records its exact semantic
representation on the enumerated stages. `constructSource?` returns zero endpoints directly and
uses the fixed-order constructor only for positive sources. Membership, stage provenance,
representation and positive-constructor success theorems follow the actual returned entries.

`ComponentAdapter` supplies the noncircular boundary for Personal 1's raw component producer.
Its validity record contains component nonzeroness and degree, sample and center capacity,
divisibility and obstruction conditions. It converts those local facts to the existing one-chart
`Constructible` contract without assuming global chart coverage.

`FirstOrderPipeline` is the checked downstream consumer. It derives nonvanishing of the actual
reduced denominator at regular solutions from the constructor's cleared global identity, rather
than requiring literal equality with an unreduced separant power. It then calls the real
first-order norm candidate generator and batched tower agreement recovery. The current exactness
theorem is conditional on candidate-family coverage and is an integration lemma, not a public
decoder completion theorem.

The central compiled runtime exercises a singular top stage descending to a regular lower stage,
dependent top/lower positive construction, and the separate zero endpoint. The principal proof
axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining producer boundary

Public first-order exactness still requires Personal 1's concrete raw component producer and its
normal-form, squarefree, position-count and fiber-degree contracts. The collected Personal 1
first-order API also still states a literal denominator-power premise; it must be repaired to
accept quotient/evaluation equality or the regular-point nonvanishing theorem proved here. Until
that reviewed producer is available, `HiddenDerivativeDecoder.symbolicDecode` remains unavailable.

General positive-order exactness additionally depends on Personal 1's G09 agreeing-membership and
energy result and Personal 3's completed G08 Rojas producer. The dedicated supplied-field
zeroth-order decoder remains complete and separate from these positive-order obligations.
