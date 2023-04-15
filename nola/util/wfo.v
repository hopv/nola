(** * Equip types with a well-founded order *)

From nola Require Import prelude.
From stdpp Require Export well_founded.

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
