(** * Utility on OFEs *)

From nola Require Export prelude.
From iris.algebra Require Import ofe cmra.
From iris.base_logic.lib Require Import iprop.

(** ** Notation for functor application over [iProp Σ] *)
Notation iProp_oapp F Σ := (oFunctor_apply F (iProp Σ)).
Notation iProp_rapp F Σ := (rFunctor_apply F (iProp Σ)).
Module iPropAppNotation.
  Notation "F $oi Σ" := (iProp_oapp F Σ) (at level 20, right associativity).
  Notation "F $ri Σ" := (iProp_rapp F Σ) (at level 20, right associativity).
End iPropAppNotation.
