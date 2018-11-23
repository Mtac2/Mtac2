Require Import Strings.String.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** [TheName s] introduces a name strictly (there can't be another one with the same name in the context).
    [FreshFrom x] uses [get_binder_name x] to generate a name, and then ensures it's fresh.
                  If [get_binder_name] fails, it generates a new name (Never fails).
    [FreshFromStr s] takes string s and generates a fresh name.
    [Generate] Generates a fresh name.
*)
Inductive name := TheName (n: string) | FreshFrom {A} (b: A) | FreshFromStr (n: string) | Generate.