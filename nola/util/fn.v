(** * Utility for functions *)

From nola Require Export prelude.

(** Map from [Empty_set] *)
Definition nullary {A} (e : Empty_set) : A := match e with end.
Arguments nullary {_} _ /.

(** Map from [unit] *)
Definition unary {A} (a : A) (_ : unit) : A := a.
Arguments unary {_} _ _ /.

(** Map from [bool] *)
Definition binary {A} (a a' : A) (b : bool) : A := if b then a else a'.
Arguments binary {_} _ _ _ /.
