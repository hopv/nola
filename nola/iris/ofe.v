(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Import ofe cmra.
From iris.bi Require Import bi.

Implicit Type PROP : bi.

Module OfeNotation.
  Notation "F $o x" := (oFunctor_apply F x) (at level 20, right associativity).
  Notation "F $r x" := (rFunctor_apply F x) (at level 20, right associativity).
End OfeNotation.

(** [▷] on [later PROP] *)
Definition laterl {PROP} (P : later PROP) : PROP := ▷ later_car P.
Arguments laterl {_} _ /.

(** [laterl] is non-expansive if [▷] is contractive *)
#[export] Instance laterl_ne `{!BiLaterContractive PROP} :
  NonExpansive (@laterl PROP).
Proof. move=> ?[?][?]?/=. by apply later_contractive. Qed.
