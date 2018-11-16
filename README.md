
### glue

This repository contains a bunch of experiments with giving various (dependent)
models of type theory in internal languages of other models.


### TODOs, issues

- Global sections functor does not seem to be a weak morphism, because it fails Π.
- Canonicity model does not seem to fall out straightforwardly from the glued Π definition.
  In normalization, Π interpretation is just the PSh logical predicate for
  function space (I think), but in canonicity we have an additional component
  in Π besides log. pred., which actually gives us the canonical element.
- In normalization, existence of normal elements fall out from quoting; can we
  reformulate canonicity with quoting, so that we may reuse the generic glued
  interpretation for canonicity?

- Currently, glued model looks just like a Set logical predicate model over an
  arbitrary F weak morphism.

- Π[] in canonicity model holds just by equational reasoning in the syntax.
