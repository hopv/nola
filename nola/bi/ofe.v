(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Import ofe cmra.
From iris.bi Require Import bi.
From iris.base_logic.lib Require Import iprop.

Implicit Type PROP : bi.

(** ** [laterl]: [▷] on [later PROP] *)
Definition laterl {PROP} (P : later PROP) : PROP := ▷ later_car P.
Arguments laterl {_} _ /.

(** [laterl] is non-expansive if [▷] is contractive *)
#[export] Instance laterl_ne `{!BiLaterContractive PROP} :
  NonExpansive (@laterl PROP).
Proof. move=> ?[?][?]?/=. by apply later_contractive. Qed.

(** ** Notation for functor application over [iProp Σ] *)
Notation iProp_oapp F Σ := (oFunctor_apply F (iProp Σ)).
Notation iProp_rapp F Σ := (rFunctor_apply F (iProp Σ)).
Module iPropAppNotation.
  Notation "F $oi Σ" := (iProp_oapp F Σ) (at level 20, right associativity).
  Notation "F $ri Σ" := (iProp_rapp F Σ) (at level 20, right associativity).
End iPropAppNotation.
