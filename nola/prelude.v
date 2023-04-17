(** * Prelude *)

From iris.prelude Require Export prelude.

(** Admit Streicher's Axiom K *)
From Coq Require Export Program.Equality.

(** Admit functional extensionality *)
From Coq Require Export FunctionalExtensionality.

(** ** Nola notation scope *)
Declare Scope nola_scope.
Delimit Scope nola_scope with nola.
Open Scope nola_scope.

(** ** Utility for functional extensionality *)

Ltac fun_ext := apply functional_extensionality.
Ltac fun_ext_dep := apply functional_extensionality_dep.

(** ** Subrelation *)

Arguments subrelation {A} (R R')%signature.

#[export] Instance eq_subrel_respect {A B}
  `{subR : subrelation A R (=)} `{subR' : subrelation B (=) R'} :
  subrelation (=) (R ==> R').
Proof. move=> f _ <- a _ /subR<-. by apply subR'. Qed.

#[export] Instance pointwise_subrel_eq {A B} `{subR : subrelation B R (=)} :
  subrelation (pointwise_relation A R) (=).
Proof. move=> f g Rfg. fun_ext=> a. by apply subR. Qed.
