(** * Equip types with a well-founded order *)

From nola Require Import prelude util.pred.
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
Notation "(≺)" := wfo_lt (only parsing) : nola_scope.

(** Inverse of [≺] *)
Definition wfo_gt {A : wfo} (a b : A) := b ≺ a.
Infix "≻" := wfo_gt (at level 70, no associativity) : nola_scope.
Notation "(≻)" := wfo_gt (only parsing) : nola_scope.

(** [≺] is irreflexive *)
#[export] Instance wfo_lt_irrefl {A : wfo} : Irreflexive A.(wfo_lt).
Proof.
  move=> a aa. move: (wfo_lt_wf a). fix FIX 1. move=> Acca. apply FIX.
  apply (Acc_inv Acca aa).
Qed.

(** [≺] is asymmetric *)
#[export] Instance wfo_lt_asymm {A : wfo} : Asymmetric A.(wfo_lt).
Proof.
  move=> a b. move: a (wfo_lt_wf a) b. fix FIX 2. move=> a Acca b ab ba.
  by apply (FIX b (Acc_inv Acca ba) a).
Qed.

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

  (** Lemma for [wsum_lt_wf] *)
  Lemma wsum_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b , Acc wsum_lt (Wsum a' b)) :
    ∀ b , Acc wfo_lt b → Acc wsum_lt (Wsum a b).
  Proof.
    fix FIX 2. move=> b Accb. apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (IH _ a'a).
    - move=> [?+]. subst. simpl_eq=> b'b. apply (FIX _ (Acc_inv Accb b'b)).
  Qed.

  (** [wsum_lt] is well-founded *)
  Lemma wsum_lt_wf : wf wsum_lt.
  Proof.
    move=> [a b]. move: a (wfo_lt_wf a) b. fix FIX 2. move=> a Acca b.
    apply Acc_intro=> [[a' b']] [|]/=.
    - move=> a'a. apply (FIX _ (Acc_inv Acca a'a)).
    - move=> [?+]. subst. simpl_eq=> b'b.
      apply wsum_lt_wf_pre; [|exact (wfo_lt_wf b')].
      clear dependent b b'=> a' a'a b. apply (FIX _ (Acc_inv Acca a'a)).
  Qed.

  Canonical wsum_wfo := Wfo (wsum) wsum_lt wsum_lt_wf.
End wsum.

Arguments wsum {A} F.

(** ** [≼*]: Simulation between [wfo]s *)

(** Generator for [wfo_sim] *)
Definition wfo_sim_gen {A B : wfo} (self : A * B → Prop) (ab : A * B) :=
  let '(a, b) := ab in ∀ a', a' ≺ a → ∃ b', b' ≺ b ∧ self (a', b').

(** [wfo_sim_gen] is monotone *)
#[export] Instance wfo_sim_gen_mono A B : Mono1 (@wfo_sim_gen A B).
Proof.
  move=> φ ψ φψ [a b]/= W a' a'a. move: (W a' a'a)=> [b' [b'b /φψ ψa'b']].
  by exists b'.
Qed.

(** [≼*]: Simulation between [wfo]s *)
Definition wfo_sim {A B : wfo} (a : A) (b : B) : Prop := nu wfo_sim_gen (a, b).
Infix "≼*" := wfo_sim (at level 70, no associativity) : nola_scope.

(** Fold [≼*] *)
Lemma wfo_sim_fold {A B : wfo} (a : A) (b : B) :
  (∀ a', a' ≺ a → ∃ b', b' ≺ b ∧ a' ≼* b') → a ≼* b.
Proof. move=> ?. by apply nu_fold. Qed.

(** Unfold [≼*] *)
Lemma wfo_sim_unfold {A B : wfo} (a : A) (b : B) :
  a ≼* b → ∀ a', a' ≺ a → ∃ b', b' ≺ b ∧ a' ≼* b'.
Proof. move=> asb. by apply nu_unfold in asb. Qed.

(** Prove [≼*] by coinduction *)
Lemma wfo_sim_coind {A B : wfo} (φ : A → B → Prop) :
  (∀ a b, φ a b → (∀ a', a' ≺ a → ∃ b', b' ≺ b ∧ φ a' b')) →
  ∀ a b, φ a b → a ≼* b.
Proof.
  move=> CH a b φab. apply (nu_coind (uncurry φ)); [|done]. clear a b φab.
  move=> [a b]/= φab. by apply CH.
Qed.

(** Get [≼*] out of a monotone function *)
Lemma wfo_sim_fun {A B : wfo} (f : A → B) :
  (∀ a a', a' ≺ a → f a' ≺ f a) → ∀ a, a ≼* f a.
Proof.
  move=> fmono a. apply (wfo_sim_coind (λ a b, b = f a)); [|done]. clear a.
  move=> a _ -> a' a'a. exists (f a'). split; [by apply fmono|done].
Qed.

(** [≼*] is reflexive *)
#[export] Instance wfo_sim_refl {A : wfo} : Reflexive (@wfo_sim A A).
Proof. move=> a. by apply (wfo_sim_fun id). Qed.

(** [≼*] is transitive *)
Lemma wfo_sim_trans {A B C : wfo} (a : A) (b : B) (c : C) :
  a ≼* b → b ≼* c → a ≼* c.
Proof.
  move=> ab bc.
  apply (wfo_sim_coind (λ a c, ∃ (b : B), a ≼* b ∧ b ≼* c)); [|by exists b].
  clear. move=> a c [b [/wfo_sim_unfold ab /wfo_sim_unfold bc]] a' a'a.
  move: {ab}(ab a' a'a)=> [b' [b'b a'sb']].
  move: {bc}(bc b' b'b)=> [c' [c'c b'sc']].
  exists c'. split; [done|]. by exists b'.
Qed.

(** [≺*]: [≼*] composed with [≺] *)
Definition wfo_sim_lt {A B : wfo} (a : A) (b : B) : Prop :=
  ∃ b', a ≼* b' ∧ b' ≺ b.
Infix "≺*" := wfo_sim_lt (at level 70, no associativity) : nola_scope.

(** Turn [≺] into [≺*] *)
Lemma wfo_lt_to_sim_lt {A : wfo} (a b : A) : a ≺ b → a ≺* b.
Proof. move=> ab. exists a. split; [by apply wfo_sim_refl|done]. Qed.

(** Compose [≼*] and [≺*] *)
Lemma wfo_sim_sim_lt_trans {A B C : wfo} (a : A) (b : B) (c : C) :
  a ≼* b → b ≺* c → a ≺* c.
Proof.
  move=> asb [c' [bsc' c'c]]. exists c'. split; [|done].
  by eapply wfo_sim_trans.
Qed.

(** Compose [≺*] and [≼*] *)
Lemma wfo_sim_lt_sim_trans {A B C : wfo} (a : A) (b : B) (c : C) :
  a ≺* b → b ≼* c → a ≺* c.
Proof.
  move=> [b' [asb' b'b]] /wfo_sim_unfold bsc.
  move: {bsc}(bsc b' b'b)=> [c' [c'c b'sc']]. exists c'. split; [|done].
  by eapply wfo_sim_trans.
Qed.

(** Turn [≼*] into [≺*] assuming transitivity of the target *)
Lemma wfo_sim_to_sim_lt {A B : wfo} `{Transitive _ B.(wfo_lt)}
  (a : A) (b : B) : a ≺* b → a ≼* b.
Proof.
  move=> [b' [/wfo_sim_unfold asb' b'b]]. apply wfo_sim_fold=> a' a'a.
  move: {asb'}(asb' a' a'a)=> [b'' [b''b' a'sb'']]. exists b''. split; [|done].
  by etrans.
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
Proof. move=> a. apply wfo_sim_refl. Qed.

(** [≼*!] is transitive *)
#[export] Instance anywfo_le_trans : Transitive anywfo_le.
Proof. move=> a b c. apply wfo_sim_trans. Qed.

(** [≼*!] is a preorder *)
#[export] Instance anywfo_le_preorder : PreOrder anywfo_le.
Proof. split; apply _. Qed.

(** [≺*!] is well-founded *)

Lemma anywfo_lt_wf_pre {A : wfo} (a : A) :
  Acc (≺) a → ∀{B : wfo} (b : B) , b ≼* a → Acc (≺*!) (Anywfo B b).
Proof.
  move: a. fix FIX 2=> a Acca B b /wfo_sim_unfold bsa. apply Acc_intro.
  move=> [C c] [/=b' [csb' b'b]]. move: {bsa}(bsa b' b'b)=> [a' [a'a b'sa']].
  eapply FIX; [exact (Acc_inv Acca a' a'a)|]. by eapply wfo_sim_trans.
Qed.

Lemma anywfo_lt_wf : wf (≺*!).
Proof.
  move=> [A a]. eapply anywfo_lt_wf_pre; [apply wfo_lt_wf|apply wfo_sim_refl].
Qed.
