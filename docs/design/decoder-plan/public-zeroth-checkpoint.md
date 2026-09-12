# Public supplied-field zeroth-order checkpoint

This checkpoint composes the accepted normalization and supplied-field producers into an
executable decoder over a supplied polynomial-basis field. It targets paper revision
`b1be8b89069542faacac40a7e92068857b43e97a` and starts from accepted core
`b626a599817381cfb84155f8b74d9cf6ff0c18a4`.

## Executed interface and theorem

`ZerothOrderDecoder.PublicDecoder.run?` takes the field characteristic and irreducible modulus,
an injective evaluation domain, received symbols, message degree, agreement threshold and
interpolation parameters. It asks callers only for data. `Valid` records the parameter,
interpolation-dimension and field-cardinality conditions.

The implementation executes frequency decoding for dimension one and exact subset enumeration
for bounded inputs. The large branch constructs the ordinary interpolant, runs certified
normalization with the supplied field's inverse Frobenius, derives the obstruction capacity,
selects base or quadratic centers, and recovers messages through characteristic-free ordinary
Newton lifting. `run?_exists_exact` proves unconditional success and `ExactOutput` for every
valid input. The large branch is not routed through the positive-order `k <= p` guard.

`SuppliedTransport.run?` is the checked boundary between normalized ordinary equations and the
three center representations. It maps the equation and obstruction through the selected base,
odd-quadratic or binary-quadratic field and maps recovered coefficients back to the supplied base
field. Its exactness proof excludes the insufficient-center case using the derived `q^2`
capacity bound.

## Verification boundary

The focused cache-disabled build and central compiled runtime include the public decoder and
transport suites. Runtime checks cover the frequency, empty, bounded and large branches; nonempty
F4 recovery with `n > p` and `k > p`; F8 and F9 near-capacity recovery; and direct transport over
base, odd-quadratic and binary-quadratic centers. Deterministic valid F11 and F16 inputs also drive
the full public interpolation, normalization and recovery path through `.oddQuadratic` and
`.binaryQuadratic`, with nonempty outputs. The F4-to-F16 transport case separately exercises
binary extension recovery without a small-characteristic fallback.

Independent implementation and integration reviews found no correctness defect. The exact final
tree is accepted only after its combined cache-disabled validation and axiom gate passes.

## Separate positive-order status

The one-chart Taylor constructor remains accepted. All-chart coverage is a later positive-order
milestone. The current coverage checkpoint scans actual separant stages and packages charts, but
its strongest theorem still assumes a component producer that covers every regular solution.
Neither this zeroth-order checkpoint nor that conditional cover proves the complete public
positive-order decoder.
