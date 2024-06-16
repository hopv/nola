(** * Utility on [list] *)

From nola Require Export prelude.
From iris.bi Require Import bi.

(** ** On [[∗ list]] *)
Section big_sepL.
  Context {PROP : bi} {A : Type}.

  #[export] Instance big_sepL_flip_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (flip (⊢))) ==> (=) ==>
      flip (⊢)) (big_opL (@bi_sep PROP) (A:=A)).
  Proof. solve_proper. Qed.
End big_sepL.
