(** * Utility for binary relations *)

From nola Require Export prelude.
From nola.util Require Import pred.

(** ** Transitive closure *)

Section tc_facts.
  Context {A : Type}.
  Implicit Type R : A → A → Prop.

  (** [tc']: [tc] defined backward *)
  Definition tc' R : A → A → Prop := flip (tc (flip R)).
  Arguments tc' R a b /.

  (** [tc] is equivalent to [tc'] *)

  Local Lemma tc'_to_tc {R a b} : tc' R a b → tc R a b.
  Proof.
    elim {a b}=>/=; [move=> >; by apply tc_once|]=> c b a Rbc _ tcRab.
    by eapply tc_r.
  Qed.

  Lemma tc_tc' {R a b} : tc R a b ↔ tc' R a b.
  Proof. split; apply tc'_to_tc. Qed.

  (** Decompose [tc] from the left *)
  Lemma tc_inv_l {R a b} : tc R a b → R a b ∨ ∃ c, R a c ∧ tc R c b.
  Proof.
    case {a b}; [by left|]=> a c b Rac tcRcb. right. by exists c.
  Qed.

  (** Decompose [tc] from the right *)
  Lemma tc_inv_r {R a b} : tc R a b → R a b ∨ ∃ c, tc R a c ∧ R c b.
  Proof.
    case/tc_tc' {a b}; [by left|]=>/= b c a Rcb /tc_tc'/= tcRac. right.
    by exists c.
  Qed.
End tc_facts.

(** ** Facts about well-founded relations *)
Section wf_facts.
  (** Take any well-founded relation [R] *)
  Context {A : Type} {R : A → A → Prop} (wfR : wf R).

  (** [R] is irreflexive *)
  Lemma wf_irrefl : Irreflexive R.
  Proof. move=> a. elim: {a}(wfR a)=> a _ IH aa. exact (IH _ aa aa). Qed.

  (** [R] is asymmetric *)
  Lemma wf_asymm : Asymmetric R.
  Proof.
    move=> a. elim: {a}(wfR a)=> a _ IH b ab ba. exact (IH b ba a ba ab).
  Qed.

  (** [tc R] is well-founded *)
  Lemma tc_wf : wf (tc R).
  Proof.
    move=> a. elim: {a}(wfR a)=> a _ IH. apply Acc_intro=> b /tc_inv_r.
    case; [by apply IH|]=> [[c [tcRbc /IH Accc]]]. exact (Acc_inv Accc tcRbc).
  Qed.
End wf_facts.

(** ** [sim]: Simulation *)

(** Generator for [sim] *)
Definition sim_gen {A B} (R : A → A → Prop) (R' : B → B → Prop)
  (self : A * B → Prop) :=
  λ '(a, b), ∀ a', R a a' → ∃ b', R' b b' ∧ self (a', b').

(** [sim_gen] is monotone *)
#[export] Instance sim_gen_mono A B R R' : Mono1 (@sim_gen A B R R').
Proof.
  move=> φ ψ φψ [a b]/= W a' aa'. move: (W a' aa')=> [b' [bb' /φψ ψa'b']].
  by exists b'.
Qed.

(** [sim]: Simulation *)
Definition sim {A B} (R : A → A → Prop) (R' : B → B → Prop) (a : A) (b : B)
  : Prop := nu (sim_gen R R') (a, b).

Section sim_facts.
  Context {A B : Type} {R : A → A → Prop} {R' : B → B → Prop}.

  (** Fold [sim] *)
  Lemma sim_fold {a b} :
    (∀ a', R a a' → ∃ b', R' b b' ∧ sim R R' a' b') → sim R R' a b.
  Proof. move=> ?. by apply nu_fold. Qed.

  (** Unfold [sim] *)
  Lemma sim_unfold {a b} :
    sim R R' a b → ∀ a', R a a' → ∃ b', R' b b' ∧ sim R R' a' b'.
  Proof. move=> sab. by apply nu_unfold in sab. Qed.

  (** Prove [sim] by coinduction *)
  Lemma sim_coind (φ : A → B → Prop) :
    (∀ a b, φ a b → (∀ a', R a a' → ∃ b', R' b b' ∧ φ a' b')) →
    ∀ a b, φ a b → sim R R' a b.
  Proof.
    move=> CH a b φab. apply (nu_coind (uncurry φ)); [|done].
    move{a b φab}=> [a b]/= φab. by apply CH.
  Qed.

  (** Get [sim] out of a monotone function *)
  Lemma sim_fun (f : A → B) :
    (∀ a a', R a a' → R' (f a) (f a')) → ∀ a, sim R R' a (f a).
  Proof.
    move=> fmono a. apply (sim_coind (λ a b, b = f a)); [|done].
    move{a}=> a _ -> a' aa'. exists (f a'). split; [by apply fmono|done].
  Qed.
End sim_facts.

(** [sim] is reflexive *)
#[export] Instance sim_refl {A} (R : A → A → Prop) : Reflexive (sim R R).
Proof. move=> a. by apply (sim_fun id). Qed.

(** [sim] is transitive *)
Lemma sim_trans {A B C}
  (R : A → A → Prop) (R' : B → B → Prop) (R'' : C → C → Prop) a b c :
  sim R R' a b → sim R' R'' b c → sim R R'' a c.
Proof.
  move=> sab sbc.
  apply (sim_coind (λ a c, ∃ b, sim R R' a b ∧ sim R' R'' b c)); [|by exists b].
  clear=> a c [b [/sim_unfold sab /sim_unfold sbc]] a' aa'.
  move: {sab}(sab a' aa')=> [b' [bb' sa'b']].
  move: {sbc}(sbc b' bb')=> [c' [cc' sb'c']].
  exists c'. split; [done|]. by exists b'.
Qed.
