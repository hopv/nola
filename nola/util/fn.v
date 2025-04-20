(** * On functions *)

From nola Require Export prelude.
From iris.algebra Require Import ofe.

Implicit Type SI : sidx.

Section fn.
  Context {SI}.

  (** Discreteness on [discrete_fun] by the discreteness of the codomain *)
  #[export] Instance discrete_fun_discrete_by_lookup {A} {F : A → ofe}
    {f : discrete_fun F} `{!∀ a, Discrete (f a)} :
    Discrete f.
  Proof. move=> ???. exact: discrete_0. Qed.
End fn.
