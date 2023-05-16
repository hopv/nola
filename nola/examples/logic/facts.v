(** * Facts *)

From nola.examples.logic Require Export deriv.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.

(** ** Bi laws *)
Section bi.
  Context `{!nevalG Σ, !nderivy Σ δ}.

  (** [δ] is reflexive *)
  Lemma n_refl {d i P} : δ d i (P, P).
  Proof. by apply n_bysem. Qed.

  (** [δ] is transitive *)
  Lemma n_trans {d i P Q R} : δ d i (P, Q) → δ d i (Q, R) → δ d i (P, R).
  Proof.
    move=> H H'. apply n_bysem=> ??. by move: H H'=> /nin_sem-> /nin_sem->.
  Qed.

  (** Laws for [⌜_⌝] *)
  Lemma n_pure_intro {d i} {φ : Prop} {P} : φ → δ d i (P, ⌜φ⌝)%n.
  Proof. move=> ?. apply n_bysem=>/= >. by apply bi.pure_intro. Qed.
  Lemma n_pure_elim {d i} {φ : Prop} {P} :
    (φ → δ d i (True, P)%n) → δ d i (⌜φ⌝, P)%n.
  Proof.
    move=> H. apply n_bysem=>/= >. apply (bi.pure_elim φ); [done|]=> x.
    move: (H x)=> /nin_sem/= <-. apply bi.True_intro.
  Qed.

  (** Laws for [∧] *)
  Lemma n_and_elim_l {d i P Q} : δ d i (P ∧ Q, P)%n.
  Proof. apply n_bysem=>/= >. by apply bi.and_elim_l. Qed.
  Lemma n_and_elim_r {d i P Q} : δ d i (P ∧ Q, Q)%n.
  Proof. apply n_bysem=>/= >. by apply bi.and_elim_r. Qed.
  Lemma n_and_intro {d i P Q R} :
    δ d i (P, Q) → δ d i (P, R)%n → δ d i (P, Q ∧ R)%n.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.and_intro; apply nin_sem.
  Qed.

  (** Laws for [∨] *)
  Lemma n_or_intro_l {d i P Q} : δ d i (P, P ∨ Q)%n.
  Proof. apply n_bysem=>/= >. by apply bi.or_intro_l. Qed.
  Lemma n_or_intro_r {d i P Q} : δ d i (Q, P ∨ Q)%n.
  Proof. apply n_bysem=>/= >. by apply bi.or_intro_r. Qed.
  Lemma n_or_elim {d i P Q R} :
    δ d i (P, R)%n → δ d i (Q, R)%n → δ d i (P ∨ Q, R)%n.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.or_elim; apply nin_sem.
  Qed.

  (** Laws for [→] *)
  Lemma n_impl_intro_r {d i P Q R} : δ d i (P ∧ Q, R)%n → δ d i (P, Q → R)%n.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.impl_intro_r. by apply nin_sem in H.
  Qed.
  Lemma n_impl_elim_l' {d i P Q R} : δ d i (P, Q → R)%n → δ d i (P ∧ Q, R)%n.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.impl_elim_l'. by apply nin_sem in H.
  Qed.

  (** Laws for [∀] *)
  Lemma n_forall_intro {d i P A Ψ} :
    (∀ a : A, δ d i (P, Ψ a)%n) → δ d i (P, ∀' Ψ)%n.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.forall_intro=> ?. by apply nin_sem.
  Qed.
  Lemma n_forall_elim {d i A Φ} {a : A} : δ d i (∀' Φ, Φ a)%n.
  Proof.
    apply n_bysem=>/= >. apply (bi.forall_elim (Ψ := λ _, neval _ _)).
  Qed.

  (** Laws for [∃] *)
  Lemma n_exist_intro {d i A Φ} {a : A} : δ d i (Φ a, ∃' Φ)%n.
  Proof.
    apply n_bysem=>/= >. apply (bi.exist_intro (Ψ := λ a, neval _ (Φ a))).
  Qed.
  Lemma n_exist_elim {d i A Φ Q} :
    (∀ a : A, δ d i (Φ a, Q)%n) → δ d i (∃' Φ, Q)%n.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.exist_elim=> ?. by apply nin_sem.
  Qed.

  (** Laws for [∗] *)
  Lemma n_sep_mono {d i P Q P' Q'} :
    δ d i (P, Q) → δ d i (P', Q') → δ d i (P ∗ P', Q ∗ Q')%n.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.sep_mono; apply nin_sem.
  Qed.
  Lemma n_True_sep_1 {d i P} : δ d i (P, True ∗ P)%n.
  Proof. apply n_bysem=>/= >. apply uPred_primitive.True_sep_1. Qed.
  Lemma n_True_sep_2 {d i P} : δ d i (True ∗ P, P)%n.
  Proof. apply n_bysem=>/= >. apply uPred_primitive.True_sep_2. Qed.
  Lemma n_sep_comm' {d i P Q} : δ d i (P ∗ Q, Q ∗ P)%n.
  Proof. apply n_bysem=>/= >. apply bi.sep_comm'. Qed.
  Lemma n_sep_assoc' {d i P Q R} : δ d i ((P ∗ Q) ∗ R, P ∗ (Q ∗ R))%n.
  Proof. apply n_bysem=>/= >. apply bi.sep_assoc'. Qed.

  (** Laws for [-∗] *)
  Lemma n_wand_intro_r {d i P Q R} : δ d i (P ∗ Q, R)%n → δ d i (P, Q -∗ R)%n.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.wand_intro_r.
    by apply nin_sem in H.
  Qed.
  Lemma n_wand_elim_l' {d i P Q R} : δ d i (P, Q -∗ R)%n → δ d i (P ∗ Q, R)%n.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.wand_elim_l'.
    by apply nin_sem in H.
  Qed.

  (** Laws for [□] *)
  Lemma n_persistently_mono {d i P Q} : δ d i (P, Q) → δ d i (□ P, □ Q)%n.
  Proof. move=> ?. apply n_bysem=>/= >. f_equiv. by apply nin_sem. Qed.
  Lemma n_persistently_elim {d i P} : δ d i (□ P, P)%n.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_persistently_idemp_2 {d i P} : δ d i (□ P, □ □ P)%n.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_persistently_forall_2 {d i A Φ} : δ d i (∀ a : A, □ Φ a, □ ∀' Φ)%n.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#" (?). Qed.
  Lemma n_persistently_exist_1 {d i A Φ} : δ d i (□ ∃' Φ, ∃ a : A, □ Φ a)%n.
  Proof. apply n_bysem=>/= >. iDestruct 1 as (a) "#?". by iExists a. Qed.
  Lemma n_persistently_and_sep_l_1 {d i P Q} : δ d i (□ P ∧ Q, □ P ∗ Q)%n.
  Proof. apply n_bysem=>/= >. iIntros "[#? ?]". by iSplit. Qed.

  (** Laws for [■] *)
  Lemma n_plainly_mono {d i P Q} : δ d i (P, Q) → δ d i (■ P, ■ Q)%n.
  Proof. move=> ?. apply n_bysem=>/= >. f_equiv. by apply nin_sem. Qed.
  Lemma n_plainly_elim_persistently {d i P} : δ d i (■ P, □ P)%n.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_plainly_idemp_2 {d i P} : δ d i (■ P, ■ ■ P)%n.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#". Qed.
  Lemma n_plainly_forall_2 {d i A Φ} : δ d i (∀ a : A, ■ Φ a, ■ ∀' Φ)%n.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#" (?). Qed.
  Lemma n_plainly_exist_1 {d i A Φ} : δ d i (■ ∃' Φ, ∃ a : A, ■ Φ a)%n.
  Proof. apply n_bysem=>/= >. iDestruct 1 as (a) "#?". by iExists a. Qed.
  Lemma n_persistently_impl_plainly {d i P Q} :
    δ d i (■ P → □ Q, □ (■ P → Q))%n.
  Proof. apply n_bysem=>/= >. iIntros "#H !# #H'". iApply ("H" with "H'"). Qed.
  Lemma n_plainly_impl_plainly {d i P Q} :
    δ d i (■ P → ■ Q, ■ (■ P → Q))%n.
  Proof. apply n_bysem=>/= >. iIntros "#H !# #H'". iApply ("H" with "H'"). Qed.

  (** Laws for [|==>] *)
  Lemma n_bupd_mono {d i P Q} : δ d i (P, Q) → δ d i (|==> P, |==> Q)%n.
  Proof. move=> ?. apply n_bysem=>/= >. apply bupd_mono. by apply nin_sem. Qed.
  Lemma n_bupd_intro {d i P} : δ d i (P, |==> P)%n.
  Proof. apply n_bysem=>/= >. apply bupd_intro. Qed.
  Lemma n_bupd_trans {d i P} : δ d i (|==> |==> P, |==> P)%n.
  Proof. apply n_bysem=>/= >. apply bupd_trans. Qed.
  Lemma n_bupd_frame_r {d i P Q} : δ d i ((|==> P) ∗ Q, |==> P ∗ Q)%n.
  Proof. apply n_bysem=>/= >. apply bupd_frame_r. Qed.
  Lemma n_bupd_plainly {d i P} : δ d i (|==> ■ P, ■ P)%n.
  Proof. apply n_bysem=>/= >. by iIntros ">?". Qed.

  (** Laws for [|={_,_}=>] *)
  Lemma n_fupd_mask_subseteq {d i E E' P} :
    E' ⊆ E → δ d i (P, |={E,E'}=> |={E',E}=> True)%n.
  Proof.
    move=> ?. apply n_bysem=>/= >. iIntros "_". by iMod fupd_mask_subseteq.
  Qed.
  Lemma n_except_0_fupd {d i E E' P} :
    δ d i (◇ (|={E,E'}=> P), |={E,E'}=> P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite neval_fp_neval/=. by iDestruct 1 as "[>?|?]".
  Qed.
  Lemma n_fupd_mono {d i E E' P Q} :
    δ d i (P, Q) → δ d i (|={E,E'}=> P, |={E,E'}=> Q)%n.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply fupd_mono. by apply nin_sem.
  Qed.
  Lemma n_fupd_trans {d i E E' E'' P} :
    δ d i (|={E,E'}=> |={E',E''}=> P, |={E,E''}=> P)%n.
  Proof. apply n_bysem=>/= >. apply fupd_trans. Qed.
  Lemma n_fupd_mask_frame_r' {d i E E' Ef P} :
    E ## Ef → δ d i (|={E,E'}=> ⌜E' ## Ef⌝ → P, |={E ∪ Ef,E' ∪ Ef}=> P)%n.
  Proof. move=> ?. apply n_bysem=>/= >. by apply fupd_mask_frame_r'. Qed.
  Lemma n_fupd_frame_r {d i E E' P Q} :
    δ d i ((|={E,E'}=> P) ∗ Q, |={E,E'}=> P ∗ Q)%n.
  Proof. apply n_bysem=>/= >. apply fupd_frame_r. Qed.

  (** Laws for [▷] *)
  Lemma n_later_mono {d i P Q} : δ d i (P, Q) → δ d i (▷{nil} P, ▷{nil} Q)%n.
  Proof.
    move=> ?. apply n_bysem=>/= >. f_equiv. rewrite !neval_fp_neval.
    by apply nin_sem.
  Qed.
  Lemma n_later_intro {d i P} : δ d i (P, ▷{nil} P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite neval_fp_neval. apply bi.later_intro.
  Qed.
  Lemma n_later_forall_2 {d i A Φ} : δ d i (∀ a : A, ▷ Φ a, ▷ ∀' Φ)%n.
  Proof.
    apply n_bysem=>/= >. setoid_rewrite neval_fp_neval.
    apply bi.later_forall_2.
  Qed.
  Lemma n_later_exist_false {d i A Φ} :
    δ d i (▷ ∃ a : A, Φ a, ▷ False ∨ (∃ a, ▷ Φ a))%n.
  Proof.
    apply n_bysem=>/= >. setoid_rewrite neval_fp_neval=>/=.
    apply bi.later_exist_false.
  Qed.
  Lemma n_later_sep_1 {d i P Q} : δ d i (▷ (P ∗ Q), ▷ P ∗ ▷ Q)%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. apply bi.later_sep_1.
  Qed.
  Lemma n_later_sep_2 {d i P Q} : δ d i (▷ P ∗ ▷ Q, ▷ (P ∗ Q))%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. apply bi.later_sep_2.
  Qed.
  Lemma n_later_false_em {d i P} : δ d i (▷ P, ▷ False ∨ (▷ False → P))%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. apply bi.later_false_em.
  Qed.
  Lemma n_later_persistently_1 {d i P} : δ d i (▷ □ P, □ ▷ P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. iIntros "#? !#". by iNext.
  Qed.
  Lemma n_later_persistently_2 {d i P} : δ d i (□ ▷ P, ▷ □ P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. iIntros. by iNext.
  Qed.
  Lemma n_later_plainly_1 {d i P} : δ d i (▷ ■ P, ■ ▷ P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. iIntros "#? !#". by iNext.
  Qed.
  Lemma n_later_plainly_2 {d i P} : δ d i (■ ▷ P, ▷ ■ P)%n.
  Proof.
    apply n_bysem=>/= >. rewrite !neval_fp_neval=>/=. iIntros. by iNext.
  Qed.
End bi.
