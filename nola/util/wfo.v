(** * Equip types with a well-founded order *)

From nola Require Import prelude.
From stdpp Require Export well_founded.
From stdpp Require Import relations.

(** ** [wfo]: Type with a well-founded order *)

Structure wfo := Wfo {
  wfo_car :> Type;
  (** Strict order *)
  wfo_lt : wfo_car -> wfo_car -> Prop;
  (** Reflexive order *)
  wfo_le : wfo_car -> wfo_car -> Prop;
  (** [wfo_le] is the reflexive closure of [wfo_lt] *)
  wfo_le_lteq : ∀a b , wfo_le a b ↔ wfo_lt a b ∨ a = b;
  (** [wfo_lt] is transitive *)
  wfo_lt_trans : ∀a b c , wfo_lt a b → wfo_lt b c → wfo_lt a c;
  (** [wfo_lt] is well-founded *)
  wfo_lt_wf : wf wfo_lt;
}.

Arguments wfo_car : simpl never.
Arguments wfo_lt {_} _ _ : simpl never, rename.
Arguments wfo_le {_} _ _ : simpl never, rename.
Arguments wfo_le_lteq {_ _ _} : simpl never.
Arguments wfo_lt_trans {_ _ _ _} _ _ : simpl never.
Arguments wfo_lt_wf {_} : simpl never.
Infix "≺" := wfo_lt (at level 70, no associativity).
Infix "≼" := wfo_le (at level 70, no associativity).

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity).

(** Inverse of [≼] *)
Definition wfo_ge {A : wfo} (a b : A) := b ≼ a.
Infix "≽" := wfo_ge (at level 70, no associativity).

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

(** ** Equip [sigT] with the lexicographic order *)

Section sigT_wfo.
  Context {A : wfo} (F : A → wfo).

  (** Lexicographic strict and reflexive order for [sigT] *)
  Definition sigT_lt (p q : sigT F) : Prop :=
    p .^1 ≺ q .^1  ∨  ∃ eq : p .^1 = q .^1, rew eq in p .^2 ≺ q .^2.
  Definition sigT_le (p q : sigT F) : Prop :=
    p .^1 ≺ q .^1  ∨  ∃ eq : p .^1 = q .^1, rew eq in p .^2 ≼ q .^2.

  (** [sigT_le] is reflexive *)
  Lemma sigT_le_refl p : sigT_le p p.
  Proof. right=>/=. exists eq_refl=>/=. apply wfo_le_refl. Qed.

  (** [sigT_lt] implies [sigT_le] *)
  Lemma sigT_lt_le p q : sigT_lt p q → sigT_le p q.
  Proof.
    move: p q=> [p1 p2][q1 q2]. move=> [/=p1q1|[/=?+]]; [by left|]. subst.
    simpl_eq=> p2q2. right. exists eq_refl=>/=. by apply wfo_lt_le.
  Qed.

  (** [sigT_le] is the reflexive closure of [sigT_lt] *)
  Lemma sigT_le_lteq p q : sigT_le p q ↔ sigT_lt p q ∨ p = q.
  Proof.
    split.
    - move: p q=> [p1 p2][q1 q2]. move=> [/=p1q1|[/=?+]]; [left; by left|].
      subst. simpl_eq=> /wfo_le_lteq[p2q2|<-]; [|by right]. left. right.
      by exists eq_refl.
    - move=> [|<-]; [apply sigT_lt_le|apply sigT_le_refl].
  Qed.

  (** [sigT_lt] is transitive *)
  Lemma sigT_lt_trans p q r : sigT_lt p q → sigT_lt q r → sigT_lt p r.
  Proof.
    move: p q r=> [p1 p2][q1 q2][r1 r2]. move=> [/=p1q1|[/=?+]][/=q1r1|[/=?+]];
    [left; exact (wfo_lt_trans p1q1 q1r1)| | |]; subst; simpl_eq;
    [move=> _; by left|move=> _; by left|]. move=> p2q2 q2r2. right.
    exists eq_refl=>/=. exact (wfo_lt_trans p2q2 q2r2).
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

  Canonical sigT_wfo :=
    Wfo (sigT F) sigT_lt sigT_le sigT_le_lteq sigT_lt_trans sigT_lt_wf.
End sigT_wfo.
