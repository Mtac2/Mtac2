Require Import Strings.String.

Inductive name := TheName (n: string) | FreshFrom {A} (b: A) | Generate.