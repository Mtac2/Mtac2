Changes from 1.2 to 1.3
=======================

- Bugfixes and performance improvements.

Changes from 1.1 to 1.2
=======================

Primitives:

- Added the `existing_instance` primitive that mirrors Coq's `Existing Instance`
  vernacular. Together with `declare`, `existing_instance` can be used to
  declare type class instances.


Debugging:

- `Set_Debug_Exceptions` now enables backtraces for uncaught exceptions. The
  traces show definitions and some internal events encountered on the way to the
  uncaught exception.


Notation:

- Combining the `.. <- ..; ..` (`M.bind`) notation and Coq's support for patterns (as in
  `let '(existT _ x P) = .. in ..`) now works without adding an additional
  apostrophe `'`. For example, `'(existT _ x P) <- some_function(); ..` is now
  legal. Previously, one had to write `''(existT _ x P) <- some_function(); ..`.
  This old syntax is no longer available.


Vernacular:

- `Mtac Do` now accepts its argument without parentheses.
- `Mtac Do` now typechecks its argument and only executes code of type `M _`.
