(** * Utility on functions *)

From nola Require Export prelude.

Implicit Type A : Type.

(** Function from [Empty_set] *)
Definition of_Empty_set {A} (e : Empty_set) : A := match e with end.

(** Function from [bool] *)
Definition of_bool {A} (a a' : A) (b : bool) : A := if b then a else a'.

(** Function from [option] *)
Definition of_option {I A} (a : A) (f : I → A) (o : option I) :=
  match o with None => a | Some i => f i end.
