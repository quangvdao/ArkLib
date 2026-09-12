# Fixed-order Taylor chart coverage checkpoint

This positive-order checkpoint follows the completed public zeroth-order decoder and preserves
the accepted one-chart constructor. Its worker source is
`cb384a40685238543fcfcbafb782d9bc8efb8b07`; the coordinator renamed its coverage predicate to
state the fixed-order boundary precisely and registered the runtime centrally.

## Executable family

`enumerateStages` follows literal highest-active-jet derivatives from an original stored equation.
`assembleSources` combines its fixed top-active stages with scheduled centers and produced
components. `constructFamily` retains every successful verified one-chart construction together
with its exact stage, active jet, center, equation and component provenance.

`constructFamily_agreement_at_regular` applies the accepted global regular-locus agreement identity
to every returned entry. `ChartEntry.covers_solution` proves that a covered solution lies on the
returned chart's equation and regular denominator locus and that every represented coefficient is
the corresponding centered Taylor coefficient. `constructFromEquation_candidate_coverage`
packages this for the actual equation-to-family execution.

The last theorem assumes `ComponentProducer.CoversTopActiveSolutions`. For every solution of the
root differential equation, that predicate supplies an actual enumerated stage whose active jet
is still `Fin.last r`, a scheduled center, a produced component, the one-chart `Constructible`
conditions, and the component/separant solution facts. The theorem also retains the positive-order
guard `0 < r < k <= p`, `Bjet < p`, and the per-source weighted-degree bounds.

## Runtime evidence

The compiled test discovers concrete stages, observes a failed component before a success, and
constructs distinct charts at centers zero and one with their provenance and ramified fibers
checked. A separate `Y_2^2` fixture follows the zero-jet solution from a singular stage zero to a
regular top-active derivative stage one and constructs exactly the later chart.

## Remaining positive-order producer boundary

This is fixed-order conditional coverage, not all-chart completion. `sourcesAtStage` intentionally
drops a stage after its active jet falls below `Fin.last r`. General coverage therefore needs a
varying-order or prefix adapter, a concrete-to-semantic separant-chain and sufficient-fuel bridge,
and the actual component/factor producer with divisibility, center, obstruction and capacity
proofs. After those producers exist, public composition still must run candidate generation,
agreement filtering, duplicate removal and exact recovery. No current theorem claims those steps.
