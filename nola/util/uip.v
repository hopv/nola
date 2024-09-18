(** * UIP over any type *)

From nola Require Export prelude.
(** Import the axiom [eq_rect_eq] *)
Require Import Coq.Logic.Eqdep.

(** UIP over any type *)
#[export] Instance all_eq_pi {A : Type} {a a' : A} : ProofIrrel (a = a').
Proof. move=> ??. apply UIP. Qed.
