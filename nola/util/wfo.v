(** * Equip types with a well-founded order *)

From nola Require Import prelude.
From stdpp Require Export well_founded.
From stdpp Require Import relations.

(** ** [wfo]: Type with a well-founded order *)

Structure wfo := Wfo {
  wfo_car :> Type;
  wfo_lt : wfo_car -> wfo_car -> Prop;
  (** [wfo_lt] is transitive *)
  wfo_lt_trans : ∀a b c , wfo_lt a b → wfo_lt b c → wfo_lt a c;
  (** [wfo_lt] is well-founded *)
  wfo_lt_wf : wf wfo_lt;
}.

Arguments wfo_car : simpl never.
Arguments wfo_lt {_} _ _ : simpl never, rename.
Arguments wfo_lt_trans {_ _ _ _} _ _ : simpl never.
Arguments wfo_lt_wf {_} : simpl never.
Infix "≺" := wfo_lt (at level 70, no associativity).

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity).

(** Reflexive closure of [≺] *)
Definition wfo_le {A : wfo} (a b : A) := a ≺ b ∨ a = b.
Infix "≼" := wfo_le (at level 70, no associativity).

(** Inverse of [≼] *)
Definition wfo_ge {A : wfo} (a b : A) := b ≼ a.
Infix "≽" := wfo_ge (at level 70, no associativity).

(** ** Facts about [wfo] *)
Section wfo_facts.
  Context {A : wfo}.
  Implicit Type a b c : A.

  (** [≼] is transitive *)
  Lemma wfo_le_trans a b c : a ≼ b → b ≼ c → a ≼ c.
  Proof.
    move=> [ab|<-] [bc|<-]; [left|by left|by left|by right].
    exact (wfo_lt_trans ab bc).
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

  Canonical nat_wfo := Wfo nat lt Nat.lt_trans lt_wf.
End nat_wfo.

(** ** Equip [sigT] with the lexicographic order *)

Section sigT_wfo.
  Context {A : wfo} (F : A → wfo).

  (** Lexicographic well-founded relation for [sigT] *)
  Definition sigT_lt (p q : sigT F) : Prop :=
    p .^1 ≺ q .^1  ∨  ∃ eq : p .^1 = q .^1, rew eq in p .^2 ≺ q .^2.

  (** [sigT_lt] is transitive *)
  Lemma sigT_lt_trans p q r : sigT_lt p q → sigT_lt q r → sigT_lt p r.
  Proof.
    move: p q r=> [p1 p2][q1 q2][r1 r2]. move=> [/=p1q1|[/=?+]][/=q1r1|[/=?+]];
    [left; exact (wfo_lt_trans p1q1 q1r1)| | |]; subst; simpl_eq;
    [move=> _; by left|move=> _; by left|]. move=> p2q2 q2r2. right.
    exists eq_refl. simpl_eq. exact (wfo_lt_trans p2q2 q2r2).
  Qed.

  (** Lemma for [sigT_lt_wf] *)
  Lemma sigT_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b , Acc sigT_lt (a' ,^ b)) :
    ∀ b , Acc wfo_lt b → Acc sigT_lt (a ,^ b).
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

  Canonical sigT_wfo := Wfo (sigT F) sigT_lt sigT_lt_trans sigT_lt_wf.
End sigT_wfo.
