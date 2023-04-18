(** * [wft]: Type with a well-founded relation *)

From nola Require Import prelude util.pred util.rel.
Import EqNotations.

(** ** [wft]: Type with a well-founded relation *)

Structure wft := Wft {
  (** Underlying type *)
  wft_car :> Type;
  (** Registered relation
    Transitivity is not required *)
  wft_lt : wft_car → wft_car → Prop;
  (** [wft_lt] is well-founded *)
  wft_lt_wf : wf wft_lt;
}.

Arguments wft_car : simpl never.
Arguments wft_lt {A} _ _ : simpl never, rename.
Arguments wft_lt_wf {A} : simpl never, rename.
Infix "≺" := wft_lt (at level 70, no associativity) : nola_scope.
Notation "(≺)" := wft_lt (only parsing) : nola_scope.

(** Inverse of [≺] *)
Definition wft_gt {A : wft} (a b : A) := b ≺ a.
Infix "≻" := wft_gt (at level 70, no associativity) : nola_scope.
Notation "(≻)" := wft_gt (only parsing) : nola_scope.

(** [≺] is irreflexive *)
#[export] Instance wft_lt_irrefl {A : wft} : Irreflexive A.(wft_lt).
Proof. apply wf_irrefl, wft_lt_wf. Qed.

(** [≺] is asymmetric *)
#[export] Instance wft_lt_asymm {A : wft} : Asymmetric A.(wft_lt).
Proof. apply wf_asymm, wft_lt_wf. Qed.

(** ** Make [nat] [wft] *)

Lemma lt_wf : wf lt.
Proof. apply well_founded_ltof. Qed.

Canonical nat_wft := Wft nat lt lt_wf.

(** ** Make [fin n] [wft] *)

Definition fin_lt {n} (i j : fin n) := i < j.

Lemma fin_lt_wf {n} : wf (@fin_lt n).
Proof. apply well_founded_ltof. Qed.

Canonical fin_wft n := Wft (fin n) fin_lt fin_lt_wf.

(** ** [wfsum]: Indexed sum of [wft]s *)

Section wfsum.
  Context {A : wft} {F : A → wft}.

  (** [wfsum]: Indexed sum of [wft]s *)
  Record wfsum : Type := Wfsum {
    wfsum_idx : A;
    wfsum_val : F wfsum_idx;
  }.

  (** Relation for [wfsum] *)
  Definition wfsum_lt (v w : wfsum) : Prop :=
    v.(wfsum_idx) ≺ w.(wfsum_idx)  ∨
    ∃ eq : v.(wfsum_idx) = w.(wfsum_idx),
      rew[F] eq in v.(wfsum_val) ≺ w.(wfsum_val).

  (** [wfsum_lt] is well-founded *)

  Local Lemma wfsum_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b, Acc wfsum_lt (Wfsum a' b)) b :
    Acc wfsum_lt (Wfsum a b).
  Proof.
    elim: {b}(wft_lt_wf b)=> b _ IH'. apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (IH _ a'a).
    - move=> [?+]. subst=>/=. by apply IH'.
  Qed.

  Lemma wfsum_lt_wf : wf wfsum_lt.
  Proof.
    move=> [a +]. elim: {a}(wft_lt_wf a)=> a _ IH b.
    apply Acc_intro=> [[a' b']] [?|]/=; [by apply IH|]=> [[? _]]. subst.
    by apply wfsum_lt_wf_pre.
  Qed.

  (** [wfsum] forms [wft] *)
  Canonical wfsum_wft := Wft wfsum wfsum_lt wfsum_lt_wf.
End wfsum.

Arguments wfsum {A} F.

(** ** [≼*]: Simulation between [wft]s *)

(** [≼*]: Simulation between [wft]s *)
Definition wft_sim {A B : wft} (a : A) (b : B) : Prop := sim (≻) (≻) a b.
Infix "≼*" := wft_sim (at level 70, no associativity) : nola_scope.

(** [≺*]: [≼*] composed with [≺] *)
Definition wft_sim_lt {A B : wft} (a : A) (b : B) : Prop :=
  ∃ b', a ≼* b' ∧ b' ≺ b.
Infix "≺*" := wft_sim_lt (at level 70, no associativity) : nola_scope.

(** Turn [≺] into [≺*] *)
Lemma wft_lt_to_sim_lt {A : wft} (a b : A) : a ≺ b → a ≺* b.
Proof. move=> ab. exists a. split; [by apply sim_refl|done]. Qed.

(** Compose [≼*] and [≺*] *)
Lemma wft_sim_sim_lt_trans {A B C : wft} (a : A) (b : B) (c : C) :
  a ≼* b → b ≺* c → a ≺* c.
Proof.
  move=> asb [c' [bsc' c'c]]. exists c'. split; [|done]. by eapply sim_trans.
Qed.

(** Compose [≺*] and [≼*] *)
Lemma wft_sim_lt_sim_trans {A B C : wft} (a : A) (b : B) (c : C) :
  a ≺* b → b ≼* c → a ≺* c.
Proof.
  move=> [b' [asb' b'b]] /sim_unfold bsc.
  move: {bsc}(bsc b' b'b)=> [c' [c'c b'sc']]. exists c'. split; [|done].
  by eapply sim_trans.
Qed.

(** Turn [≼*] into [≺*] assuming transitivity of the target *)
Lemma wft_sim_to_sim_lt {A B : wft} `{Transitive _ B.(wft_lt)} (a : A) (b : B) :
  a ≺* b → a ≼* b.
Proof.
  move=> [b' [/sim_unfold asb' b'b]]. apply sim_fold=> a' a'a.
  move: {asb'}(asb' a' a'a)=> [b'' [b''b' a'sb'']]. exists b''. split; [|done].
  unfold wft_gt. by etrans.
Qed.

(** ** [anywft]: Direct sum of all [wft]s
  Note that [anywft] itself can't belong to [wft]
  due to the universe hierarchy *)

Record anywft := Anywft { anywft_wft : wft; anywft_val : anywft_wft }.

(** [≼*!]: [≼*] over [anywft]s *)
Definition anywft_le (a b : anywft) : Prop := a.(anywft_val) ≼* b.(anywft_val).
Infix "≼*!" := anywft_le (at level 70, no associativity) : nola_scope.
Notation "(≼*!)" := anywft_le (only parsing) : nola_scope.

(** [≺*!]: [≺*] over [anywft]s *)
Definition anywft_lt (a b : anywft) : Prop := a.(anywft_val) ≺* b.(anywft_val).
Infix "≺*!" := anywft_lt (at level 70, no associativity) : nola_scope.
Notation "(≺*!)" := anywft_lt (only parsing) : nola_scope.

(** [≼*!] is reflexive *)
#[export] Instance anywft_le_refl : Reflexive anywft_le.
Proof. move=> a. apply sim_refl. Qed.

(** [≼*!] is transitive *)
#[export] Instance anywft_le_trans : Transitive anywft_le.
Proof. move=> a b c. apply sim_trans. Qed.

(** [≼*!] is a preorder *)
#[export] Instance anywft_le_preorder : PreOrder anywft_le.
Proof. split; apply _. Qed.

(** [≺*!] is well-founded *)

Local Lemma anywft_lt_wf_pre {A B : wft} (a : A) (b : B) :
  b ≼* a → Acc (≺*!) (Anywft B b).
Proof.
  move: B b. elim: {a}(wft_lt_wf a)=> a _ IH B b /sim_unfold bsa.
  apply Acc_intro=> [[C c] [/=b' [csb' b'b]]].
  move: {bsa}(bsa b' b'b)=> [a' [a'a b'sa']]. eapply IH; [done|].
  by eapply sim_trans.
Qed.

Lemma anywft_lt_wf : wf (≺*!).
Proof. move=> [A a]. eapply anywft_lt_wf_pre, sim_refl. Qed.

(** [≺*] is irreflexive *)
#[export] Instance wft_sim_lt_irrefl {A : wft} : Irreflexive (@wft_sim_lt A A).
Proof. move=> a. exact (wf_irrefl anywft_lt_wf (Anywft A a)). Qed.

(** [≺*] is asymmetric *)
Lemma wft_sim_lt_asymm {A B : wft} (a : A) (b : B) : a ≺* b → ¬ b ≺* a.
Proof. exact (wf_asymm anywft_lt_wf (Anywft A a) (Anywft B b)). Qed.
