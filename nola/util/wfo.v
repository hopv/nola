(** * Equip types with a well-founded order *)

From nola Require Import prelude.
From stdpp Require Export well_founded.
Import EqNotations.

(** ** [wfo]: Type with a well-founded order *)

Structure wfo := Wfo {
  (** Underlying type *)
  wfo_car :> Type;
  (** Strict order *)
  wfo_lt : wfo_car → wfo_car → Prop;
  (** [wfo_lt] is well-founded *)
  wfo_lt_wf : wf wfo_lt;
}.

Arguments wfo_car : simpl never.
Arguments wfo_lt {A} _ _ : simpl never, rename.
Arguments wfo_lt_wf {A} : simpl never, rename.
Infix "≺" := wfo_lt (at level 70, no associativity) : nola_scope.

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity) : nola_scope.

(** [≺] is irreflexive *)
Lemma wfo_lt_irrefl {A : wfo} (a : A) : ¬ a ≺ a.
Proof.
  move=> aa. move: (wfo_lt_wf a). fix FIX 1. move=> Acca. apply FIX.
  apply (Acc_inv Acca aa).
Qed.

(** ** Equip [nat] with [lt] *)

Lemma lt_wf : wf lt.
Proof. apply well_founded_ltof. Qed.

Canonical nat_wfo := Wfo nat lt lt_wf.

(** ** Equip [sigT] with the lexicographic order *)

Section sigT_wfo.
  Context {A : wfo} (F : A → wfo).

  (** Lexicographic strict and reflexive order for [sigT] *)
  Definition sigT_lt (p q : sigT F) : Prop :=
    projT1 p ≺ projT1 q  ∨
    ∃ eq : projT1 p = projT1 q, rew eq in projT2 p ≺ projT2 q.

  (** Lemma for [sigT_lt_wf] *)
  Lemma sigT_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b , Acc sigT_lt (existT a' b)) :
    ∀ b , Acc wfo_lt b → Acc sigT_lt (existT a b).
  Proof.
    fix FIX 2. move=> b Accb. apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (IH _ a'a).
    - move=> [?+]. subst. simpl_eq=> b'b. apply (FIX _ (Acc_inv Accb b'b)).
  Qed.

  (** [sigT_lt] is well-founded *)
  Lemma sigT_lt_wf : wf sigT_lt.
  Proof.
    move=> [a b]. move: a (wfo_lt_wf a) b. fix FIX 2. move=> a Acca b.
    apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (FIX _ (Acc_inv Acca a'a)).
    - move=> [?+]. subst. simpl_eq=> b'b.
      apply sigT_lt_wf_pre; [|exact (wfo_lt_wf b')].
      clear dependent b b'=> a' a'a b. apply (FIX _ (Acc_inv Acca a'a)).
  Qed.

  Canonical sigT_wfo := Wfo (sigT F) sigT_lt sigT_lt_wf.
End sigT_wfo.
