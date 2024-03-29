(** * Utility for binary relations *)

From nola Require Export prelude.
Require Import Coq.Logic.Eqdep_dec.

(** ** Equality **)

Lemma eq_dec_refl `{!EqDecision A} {a : A} (eq : a = a) : eq = eq_refl.
Proof. apply proof_irrel. Qed.

(** ** On transitive closure *)

Section tc.
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
End tc.

(** ** On well-founded relations *)
Section wf.
  (** Take any well-founded relation [R] *)
  Context {A : Type} {R : A → A → Prop} (wfR : well_founded R).

  (** [R] is irreflexive *)
  Lemma wf_irrefl : Irreflexive R.
  Proof. move=> a. elim: {a}(wfR a)=> a _ IH aa. exact (IH _ aa aa). Qed.

  (** [R] is asymmetric *)
  Lemma wf_asymm : Asymmetric R.
  Proof.
    move=> a. elim: {a}(wfR a)=> a _ IH b ab ba. exact (IH b ba a ba ab).
  Qed.

  (** [tc R] is well-founded *)
  Lemma tc_wf : well_founded (tc R).
  Proof.
    move=> a. elim: {a}(wfR a)=> a _ IH. apply Acc_intro=> b /tc_inv_r.
    case; [by apply IH|]=> [[c [tcRbc /IH Accc]]]. exact (Acc_inv Accc tcRbc).
  Qed.
End wf.

(** Empty relation is well-founded *)
Lemma false_wf {A} : well_founded (λ _ _ : A, False).
Proof. move=> a. by apply Acc_intro. Qed.
