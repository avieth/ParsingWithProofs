### Parsing with proofs

StringParser.idr : a demonstration of a monadic/applicative string parser whose
values are guaranteed to only consume their input, never to increase its size.

examples/Formula.idr : usage of the StringParser to parse boolean formulas.

examples/Deserialization.idr : usage of the StringParser to parse abbreviations
of Canadian provinces, complete with a proof that it is left-inverse to a
serializer.
