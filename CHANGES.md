Changes from 1.1 to 1.2
=======================

Notation:

- Combining the `.. <- ..; ..` (`M.bind`) notation and Coq's support for patterns (as in
  `let '(existT _ x P) = .. in ..`) now works without adding an additional
  apostrophe `'`. For example, `'(existT _ x P) <- some_function(); ..` is now
  legal. Previously, one had to write `''(existT _ x P) <- some_function(); ..`.
  This old syntax is no longer available.


Vernacular:

- `Mtac Do` now accepts its argument without parentheses.
- `Mtac Do` now typechecks its argument and only executes code of type `M _`.
