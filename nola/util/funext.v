(** * Utility for functional extensionality *)

From nola Require Export prelude.
From Coq Require Export FunctionalExtensionality.
From stdpp Require Import well_founded.

(** ** Apply functional extensionality, without introducing a name *)
Ltac funext :=
  apply functional_extensionality || apply functional_extensionality_dep.

(** ** On [subrelation] *)

(** Make [(=)] a subrelation of [==>] *)
#[export] Instance eq_subrel_respect
  `{subR : subrelation A R (=)} `{subR' : subrelation B (=) R'} :
  subrelation (=) (R ==> R')%signature.
Proof. move=> f _ <- a _ /subR<-. by apply subR'. Qed.

(** Make [pointwise_relation] a subrelation of [(=)],
  using functional extensionality *)
#[export] Instance pointwise_subrel_eq `{subR : subrelation B R (=)} {A} :
  subrelation (pointwise_relation A R) (=).
Proof. move=> f g Rfg. funext=> a. by apply subR. Qed.

(** [Acc] is proof-irrelevant, assuming functional extensionality *)
#[export] Instance Acc_pi {A R} {a : A} : ProofIrrel (Acc R a).
Proof.
  move=> x. move: a x. fix FIX 2=> ?[?][?]. f_equal. do 2 funext=> ?. apply FIX.
Qed.
