(** * Equip types with a well-founded order *)

From nola Require Import prelude util.pred util.rel.
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
Notation "(≺)" := wfo_lt (only parsing) : nola_scope.

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity) : nola_scope.
Notation "(≻)" := wfo_gt (only parsing) : nola_scope.

(** [≺] is irreflexive *)
#[export] Instance wfo_lt_irrefl {A : wfo} : Irreflexive A.(wfo_lt).
Proof. apply wf_irrefl, wfo_lt_wf. Qed.

(** [≺] is asymmetric *)
#[export] Instance wfo_lt_asymm {A : wfo} : Asymmetric A.(wfo_lt).
Proof. apply wf_asymm, wfo_lt_wf. Qed.

(** ** Make [nat] [wfo] *)

Lemma lt_wf : wf lt.
Proof. apply well_founded_ltof. Qed.

Canonical nat_wfo := Wfo nat lt lt_wf.

(** ** Make [fin n] [wfo] *)

Definition fin_lt {n} (i j : fin n) := i < j.

Lemma fin_lt_wf {n} : wf (@fin_lt n).
Proof. apply well_founded_ltof. Qed.

Canonical fin_wfo n := Wfo (fin n) fin_lt fin_lt_wf.

(** ** [wsum]: Indexed sum of [wfo]s *)

Section wsum.
  Context {A : wfo} {F : A → wfo}.

  (** [wsum]: Indexed sum of [wfo]s *)
  Record wsum : Type := Wsum {
    wsum_idx : A;
    wsum_val : F wsum_idx;
  }.

  (** Strict order for [wsum] *)
  Definition wsum_lt (v w : wsum) : Prop :=
    v.(wsum_idx) ≺ w.(wsum_idx)  ∨
    ∃ eq : v.(wsum_idx) = w.(wsum_idx),
      rew[F] eq in v.(wsum_val) ≺ w.(wsum_val).

  (** [wsum_lt] is well-founded *)

  Local Lemma wsum_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b, Acc wsum_lt (Wsum a' b)) b :
    Acc wsum_lt (Wsum a b).
  Proof.
    elim: {b}(wfo_lt_wf b)=> b _ IH'. apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (IH _ a'a).
    - move=> [?+]. subst=>/=. by apply IH'.
  Qed.

  Lemma wsum_lt_wf : wf wsum_lt.
  Proof.
    move=> [a +]. elim: {a}(wfo_lt_wf a)=> a _ IH b.
    apply Acc_intro=> [[a' b']] [?|]/=; [by apply IH|]=> [[? _]]. subst.
    by apply wsum_lt_wf_pre.
  Qed.

  (** [wsum] forms [wfo] *)
  Canonical wsum_wfo := Wfo wsum wsum_lt wsum_lt_wf.
End wsum.

Arguments wsum {A} F.

(** ** [≼*]: Simulation between [wfo]s *)

(** [≼*]: Simulation between [wfo]s *)
Definition wfo_sim {A B : wfo} (a : A) (b : B) : Prop := sim (≻) (≻) a b.
Infix "≼*" := wfo_sim (at level 70, no associativity) : nola_scope.

(** [≺*]: [≼*] composed with [≺] *)
Definition wfo_sim_lt {A B : wfo} (a : A) (b : B) : Prop :=
  ∃ b', a ≼* b' ∧ b' ≺ b.
Infix "≺*" := wfo_sim_lt (at level 70, no associativity) : nola_scope.

(** Turn [≺] into [≺*] *)
Lemma wfo_lt_to_sim_lt {A : wfo} (a b : A) : a ≺ b → a ≺* b.
Proof. move=> ab. exists a. split; [by apply sim_refl|done]. Qed.

(** Compose [≼*] and [≺*] *)
Lemma wfo_sim_sim_lt_trans {A B C : wfo} (a : A) (b : B) (c : C) :
  a ≼* b → b ≺* c → a ≺* c.
Proof.
  move=> asb [c' [bsc' c'c]]. exists c'. split; [|done]. by eapply sim_trans.
Qed.

(** Compose [≺*] and [≼*] *)
Lemma wfo_sim_lt_sim_trans {A B C : wfo} (a : A) (b : B) (c : C) :
  a ≺* b → b ≼* c → a ≺* c.
Proof.
  move=> [b' [asb' b'b]] /sim_unfold bsc.
  move: {bsc}(bsc b' b'b)=> [c' [c'c b'sc']]. exists c'. split; [|done].
  by eapply sim_trans.
Qed.

(** Turn [≼*] into [≺*] assuming transitivity of the target *)
Lemma wfo_sim_to_sim_lt {A B : wfo} `{Transitive _ B.(wfo_lt)} (a : A) (b : B) :
  a ≺* b → a ≼* b.
Proof.
  move=> [b' [/sim_unfold asb' b'b]]. apply sim_fold=> a' a'a.
  move: {asb'}(asb' a' a'a)=> [b'' [b''b' a'sb'']]. exists b''. split; [|done].
  unfold wfo_gt. by etrans.
Qed.

(** ** [anywfo]: Direct sum of all [wfo]s
  Note that [anywfo] itself can't belong to [wfo]
  due to the universe hierarchy *)

Record anywfo := Anywfo { anywfo_wfo : wfo; anywfo_val : anywfo_wfo }.

(** [≼*!]: Reflexive order over [anywfo]s *)
Definition anywfo_le (a b : anywfo) : Prop := a.(anywfo_val) ≼* b.(anywfo_val).
Infix "≼*!" := anywfo_le (at level 70, no associativity) : nola_scope.
Notation "(≼*!)" := anywfo_le (only parsing) : nola_scope.

(** [≺*!]: Strict order over [anywfo]s *)
Definition anywfo_lt (a b : anywfo) : Prop := a.(anywfo_val) ≺* b.(anywfo_val).
Infix "≺*!" := anywfo_lt (at level 70, no associativity) : nola_scope.
Notation "(≺*!)" := anywfo_lt (only parsing) : nola_scope.

(** [≼*!] is reflexive *)
#[export] Instance anywfo_le_refl : Reflexive anywfo_le.
Proof. move=> a. apply sim_refl. Qed.

(** [≼*!] is transitive *)
#[export] Instance anywfo_le_trans : Transitive anywfo_le.
Proof. move=> a b c. apply sim_trans. Qed.

(** [≼*!] is a preorder *)
#[export] Instance anywfo_le_preorder : PreOrder anywfo_le.
Proof. split; apply _. Qed.

(** [≺*!] is well-founded *)

Local Lemma anywfo_lt_wf_pre {A B : wfo} (a : A) (b : B) :
  b ≼* a → Acc (≺*!) (Anywfo B b).
Proof.
  move: B b. elim: {a}(wfo_lt_wf a)=> a _ IH B b /sim_unfold bsa.
  apply Acc_intro=> [[C c] [/=b' [csb' b'b]]].
  move: {bsa}(bsa b' b'b)=> [a' [a'a b'sa']]. eapply IH; [done|].
  by eapply sim_trans.
Qed.

Lemma anywfo_lt_wf : wf (≺*!).
Proof. move=> [A a]. eapply anywfo_lt_wf_pre, sim_refl. Qed.

(** [≺*] is irreflexive *)
#[export] Instance wfo_sim_lt_irrefl {A : wfo} : Irreflexive (@wfo_sim_lt A A).
Proof. move=> a. exact (wf_irrefl anywfo_lt_wf (Anywfo A a)). Qed.

(** [≺*] is asymmetric *)
Lemma wfo_sim_lt_asymm {A B : wfo} (a : A) (b : B) : a ≺* b → ¬ b ≺* a.
Proof. exact (wf_asymm anywfo_lt_wf (Anywfo A a) (Anywfo B b)). Qed.
