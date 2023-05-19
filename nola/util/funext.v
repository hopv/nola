(** * Utility for functional extensionality *)

From nola Require Export prelude.
From Coq Require Export FunctionalExtensionality.

(** ** Apply functional extensionality, without introducing a name *)
Ltac funext :=
  apply functional_extensionality || apply functional_extensionality_dep.

(** ** Make [(=)] a subrelation of [==>] *)
#[export] Instance eq_subrel_respect {A B}
  `{subR : subrelation A R (=)} `{subR' : subrelation B (=) R'} :
  subrelation (=) (R ==> R')%signature.
Proof. move=> f _ <- a _ /subR<-. by apply subR'. Qed.

(** ** Make [pointwise_relation] a subrelation of [(=)],
  using functional extensionality *)
#[export] Instance pointwise_subrel_eq {A B} `{subR : subrelation B R (=)} :
  subrelation (pointwise_relation A R) (=).
Proof. move=> f g Rfg. funext=> a. by apply subR. Qed.
