(** * Utility on functions *)

From nola Require Export prelude.

(** Map from [Empty_set] *)
Notation nullary := (λ e : Empty_set, match e with end).

(** Map from [unit] etc. *)
Notation unary a := (λ _, a).

(** Map from [bool] *)
Notation binary a a' := (λ b : bool, if b then a else a').
