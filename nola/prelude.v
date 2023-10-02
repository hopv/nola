(** * Prelude

  It gets imported and exported by all other files of [nola] *)

From iris.prelude Require Export prelude.

(** Nola notation scope *)
Declare Scope nola_scope.
Delimit Scope nola_scope with nola.
Open Scope nola_scope.

(** Make [(=)] a subrelation of [==>] *)
#[export] Instance eq_subrel_respect
  `{subR : subrelation (A:=A) R (=)} `{subR' : subrelation (A:=B) (=) R'} :
  subrelation (=) (R ==> R')%signature.
Proof. move=> f _ <- a _ /subR<-. by apply subR'. Qed.
