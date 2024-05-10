(** * Prelude

  It gets imported and exported by all other files of [nola] *)

From iris.prelude Require Export prelude.

(** Nola notation scope *)
Declare Scope nola_scope.
Delimit Scope nola_scope with nola.
Open Scope nola_scope.
