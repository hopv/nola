(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Import ofe cmra.
From iris.bi Require Import bi.
From iris.base_logic Require Import iprop.

Implicit Type PROP : bi.

Notation oiapp F Σ := (oFunctor_apply F (iProp Σ)).
Notation riapp F Σ := (rFunctor_apply F (iProp Σ)).
Module OfeNotation.
  Notation "F $o Σ" := (oiapp F Σ) (at level 20, right associativity).
  Notation "F $r Σ" := (riapp F Σ) (at level 20, right associativity).
End OfeNotation.

(** [▷] on [later PROP] *)
Definition laterl {PROP} (P : later PROP) : PROP := ▷ later_car P.
Arguments laterl {_} _ /.

(** [laterl] is non-expansive if [▷] is contractive *)
#[export] Instance laterl_ne `{!BiLaterContractive PROP} :
  NonExpansive (@laterl PROP).
Proof. move=> ?[?][?]?/=. by apply later_contractive. Qed.
