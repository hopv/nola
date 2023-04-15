(** * Equip types with a well-founded order *)

From nola Require Import prelude.
From stdpp Require Export well_founded.

(** ** [wfo]: Type with a well-founded order *)

Structure wfo := Wfo {
  wfo_car :> Type;
  (** Strict order *)
  wfo_lt : wfo_car → wfo_car → Prop;
  (** Reflexive order *)
  wfo_le : wfo_car → wfo_car → Prop;
  (** [wfo_le] is the reflexive closure of [wfo_lt] *)
  wfo_le_lteq : ∀a b , wfo_le a b ↔ wfo_lt a b ∨ a = b;
  (** [wfo_lt] is transitive *)
  wfo_lt_trans : ∀a b c , wfo_lt a b → wfo_lt b c → wfo_lt a c;
  (** [wfo_lt] is well-founded *)
  wfo_lt_wf : wf wfo_lt;
}.

Arguments wfo_car : simpl never.
Arguments wfo_lt {A} _ _ : simpl never, rename.
Arguments wfo_le {A} _ _ : simpl never, rename.
Arguments wfo_le_lteq {A _ _} : simpl never, rename.
Arguments wfo_lt_trans {A _ _ _} _ _ : simpl never, rename.
Arguments wfo_lt_wf {A} : simpl never, rename.
Infix "≺" := wfo_lt (at level 70, no associativity) : nola_scope.
Infix "≼" := wfo_le (at level 70, no associativity) : nola_scope.

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity) : nola_scope.

(** Inverse of [≼] *)
Definition wfo_ge {A : wfo} (a b : A) := b ≼ a.
Infix "≽" := wfo_ge (at level 70, no associativity) : nola_scope.

(** ** Facts about [wfo] *)
Section wfo_facts.
  Context {A : wfo}.
  Implicit Type a b c : A.

  (** [≼] is reflexive *)
  Lemma wfo_le_refl a : a ≼ a.
  Proof. apply wfo_le_lteq. by right. Qed.

  (** Turn [≺] into [≼] *)
  Lemma wfo_lt_le a b : a ≺ b → a ≼ b.
  Proof. move=> ab. apply wfo_le_lteq. by left. Qed.

  (** [≼] is transitive *)
  Lemma wfo_le_trans a b c : a ≼ b → b ≼ c → a ≼ c.
  Proof.
    move=> /wfo_le_lteq[ab|<-] /wfo_le_lteq[bc|<-]; apply wfo_le_lteq;
    [left|by left|by left|by right]. exact (wfo_lt_trans ab bc).
  Qed.

  (** [≺] is irreflexive *)
  Lemma wfo_lt_irrefl a : ¬ a ≺ a.
  Proof.
    move=> aa. move: (wfo_lt_wf a). fix FIX 1. move=> Acca. apply FIX.
    apply (Acc_inv Acca aa).
  Qed.
End wfo_facts.

(** ** Equip [nat] with [lt] *)

Section nat_wfo.
  Lemma lt_wf : wf lt.
  Proof. apply well_founded_ltof. Qed.

  Canonical nat_wfo := Wfo nat lt le Nat.lt_eq_cases Nat.lt_trans lt_wf.
End nat_wfo.
