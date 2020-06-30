Changes from 1.1 to 1.2
=======================

Primitives:

- Added the `replace_evar_type` primitive. Given evar `e : A` and a reducible
  proof `prf : A =m= B`, `replace_evar_type e prf` changes the type of `e` to
  `B`, returning `e : B` without any changes to the term. This can be very
  useful when instantiating goal evars whose type needs to be changed to a
  convertible type before instantiation (which will unify the type of the evar
  with the type with the solution) can succeed efficiently.

Notation:

- Combining the `.. <- ..; ..` (`M.bind`) notation and Coq's support for patterns (as in
  `let '(existT _ x P) = .. in ..`) now works without adding an additional
  apostrophe `'`. For example, `'(existT _ x P) <- some_function(); ..` is now
  legal. Previously, one had to write `''(existT _ x P) <- some_function(); ..`.
  This old syntax is no longer available.


Vernacular:

- `Mtac Do` now accepts its argument without parentheses.
