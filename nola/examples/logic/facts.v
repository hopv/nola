(** * Facts *)

From nola.examples.logic Require Export deriv.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.
Import EqNotations.

(** ** Bi laws *)
Section bi.
  Context `{!nintpG Σ, !nderivy Σ δ}.

  (** [δ] is reflexive *)
  Lemma n_refl {d i P} : P ⊢{δ d, i} P.
  Proof. by apply n_bysem. Qed.

  (** [δ] is transitive *)
  Lemma n_trans {d i P Q R} : P ⊢{δ d, i} Q → Q ⊢{δ d, i} R → P ⊢{δ d, i} R.
  Proof.
    move=> H H'. apply n_bysem=> >. by move: H H'=> /nin_sem-> /nin_sem->.
  Qed.

  (** Laws for [⌜_⌝] *)
  Lemma n_pure_intro {d i} {φ : Prop} {P} : φ → P ⊢{δ d, i} ⌜φ⌝.
  Proof. move=> ?. apply n_bysem=>/= >. by apply bi.pure_intro. Qed.
  Lemma n_pure_elim {d i} {φ : Prop} {P} :
    (φ → True ⊢{δ d, i} P) → ⌜φ⌝ ⊢{δ d, i} P.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.pure_elim'=> x.
    move: (H x)=> /nin_sem/= <-. apply bi.True_intro.
  Qed.

  (** Laws for [∧] *)
  Lemma n_and_elim_l {d i P Q} : P ∧ Q ⊢{δ d, i} P.
  Proof. apply n_bysem=>/= >. by apply bi.and_elim_l. Qed.
  Lemma n_and_elim_r {d i P Q} : P ∧ Q ⊢{δ d, i} Q.
  Proof. apply n_bysem=>/= >. by apply bi.and_elim_r. Qed.
  Lemma n_and_intro {d i P Q R} :
    P ⊢{δ d, i} Q → P ⊢{δ d, i} R → P ⊢{δ d, i} Q ∧ R.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.and_intro; apply nin_sem.
  Qed.

  (** Laws for [∨] *)
  Lemma n_or_intro_l {d i P Q} : P ⊢{δ d, i} P ∨ Q.
  Proof. apply n_bysem=>/= >. by apply bi.or_intro_l. Qed.
  Lemma n_or_intro_r {d i P Q} : Q ⊢{δ d, i} P ∨ Q.
  Proof. apply n_bysem=>/= >. by apply bi.or_intro_r. Qed.
  Lemma n_or_elim {d i P Q R} :
    P ⊢{δ d, i} R → Q ⊢{δ d, i} R → P ∨ Q ⊢{δ d, i} R.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.or_elim; apply nin_sem.
  Qed.

  (** Laws for [→] *)
  Lemma n_impl_intro_r {d i P Q R} : P ∧ Q ⊢{δ d, i} R → P ⊢{δ d, i} (Q → R).
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.impl_intro_r. by apply nin_sem in H.
  Qed.
  Lemma n_impl_elim_l' {d i P Q R} : P ⊢{δ d, i} (Q → R) → P ∧ Q ⊢{δ d, i} R.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.impl_elim_l'. by apply nin_sem in H.
  Qed.

  (** Laws for [∀] *)
  Lemma n_forall_intro {d i P A Ψ} :
    (∀ a : A, P ⊢{δ d, i} Ψ a) → P ⊢{δ d, i} ∀' Ψ.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.forall_intro=> ?. by apply nin_sem.
  Qed.
  Lemma n_forall_elim {d i A Φ} {a : A} : ∀' Φ ⊢{δ d, i} Φ a.
  Proof.
    apply n_bysem=>/= >. apply (bi.forall_elim (Ψ := λ _, _)).
  Qed.

  (** Laws for [∃] *)
  Lemma n_exist_intro {d i A Φ} {a : A} : Φ a ⊢{δ d, i} ∃' Φ.
  Proof.
    apply n_bysem=>/= >. apply (bi.exist_intro (Ψ := λ a, ⟦ Φ a ⟧(_))).
  Qed.
  Lemma n_exist_elim {d i A Φ Q} :
    (∀ a : A, Φ a ⊢{δ d, i} Q) → (∃' Φ) ⊢{δ d, i} Q.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.exist_elim=> ?. by apply nin_sem.
  Qed.

  (** Laws for [∗] *)
  Lemma n_sep_mono {d i P Q P' Q'} :
    P ⊢{δ d, i} Q → P' ⊢{δ d, i} Q' → P ∗ P' ⊢{δ d, i} Q ∗ Q'.
  Proof.
    move=> ??. apply n_bysem=>/= >. by apply bi.sep_mono; apply nin_sem.
  Qed.
  Lemma n_True_sep_1 {d i P} : P ⊢{δ d, i} True ∗ P.
  Proof. apply n_bysem=>/= >. apply uPred_primitive.True_sep_1. Qed.
  Lemma n_True_sep_2 {d i P} : True ∗ P ⊢{δ d, i} P.
  Proof. apply n_bysem=>/= >. apply uPred_primitive.True_sep_2. Qed.
  Lemma n_sep_comm' {d i P Q} : P ∗ Q ⊢{δ d, i} Q ∗ P.
  Proof. apply n_bysem=>/= >. apply bi.sep_comm'. Qed.
  Lemma n_sep_assoc' {d i P Q R} : (P ∗ Q) ∗ R ⊢{δ d, i} P ∗ (Q ∗ R).
  Proof. apply n_bysem=>/= >. apply bi.sep_assoc'. Qed.

  (** Laws for [-∗] *)
  Lemma n_wand_intro_r {d i P Q R} : P ∗ Q ⊢{δ d, i} R → P ⊢{δ d, i} (Q -∗ R).
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.wand_intro_r. by apply nin_sem in H.
  Qed.
  Lemma n_wand_elim_l' {d i P Q R} : P ⊢{δ d, i} (Q -∗ R) → P ∗ Q ⊢{δ d, i} R.
  Proof.
    move=> H. apply n_bysem=>/= >. apply bi.wand_elim_l'. by apply nin_sem in H.
  Qed.

  (** Laws for [□] *)
  Lemma n_persistently_mono {d i P Q} : P ⊢{δ d, i} Q → □ P ⊢{δ d, i} □ Q.
  Proof. move=> ?. apply n_bysem=>/= >. f_equiv. by apply nin_sem. Qed.
  Lemma n_persistently_elim {d i P} : □ P ⊢{δ d, i} P.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_persistently_idemp_2 {d i P} : □ P ⊢{δ d, i} □ □ P.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_persistently_forall_2 {d i A Φ} : (∀ a : A, □ Φ a) ⊢{δ d, i} □ ∀' Φ.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#" (?). Qed.
  Lemma n_persistently_exist_1 {d i A Φ} : □ ∃' Φ ⊢{δ d, i} ∃ a : A, □ Φ a.
  Proof. apply n_bysem=>/= >. iDestruct 1 as (a) "#?". by iExists a. Qed.
  Lemma n_persistently_and_sep_l_1 {d i P Q} : □ P ∧ Q ⊢{δ d, i} □ P ∗ Q.
  Proof. apply n_bysem=>/= >. iIntros "[#? ?]". by iSplit. Qed.

  (** Laws for [■] *)
  Lemma n_plainly_mono {d i P Q} : P ⊢{δ d, i} Q → ■ P ⊢{δ d, i} ■ Q.
  Proof. move=> ?. apply n_bysem=>/= >. f_equiv. by apply nin_sem. Qed.
  Lemma n_plainly_elim_persistently {d i P} : ■ P ⊢{δ d, i} □ P.
  Proof. apply n_bysem=>/= >. by iIntros. Qed.
  Lemma n_plainly_idemp_2 {d i P} : ■ P ⊢{δ d, i} ■ ■ P.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#". Qed.
  Lemma n_plainly_forall_2 {d i A Φ} : (∀ a : A, ■ Φ a) ⊢{δ d, i} ■ ∀' Φ.
  Proof. apply n_bysem=>/= >. by iIntros "#? !#" (?). Qed.
  Lemma n_plainly_exist_1 {d i A Φ} : ■ ∃' Φ ⊢{δ d, i} ∃ a : A, ■ Φ a.
  Proof. apply n_bysem=>/= >. iDestruct 1 as (a) "#?". by iExists a. Qed.
  Lemma n_persistently_impl_plainly {d i P Q} :
    (■ P → □ Q) ⊢{δ d, i} □ (■ P → Q).
  Proof. apply n_bysem=>/= >. iIntros "#H !# #H'". iApply ("H" with "H'"). Qed.
  Lemma n_plainly_impl_plainly {d i P Q} : (■ P → ■ Q) ⊢{δ d, i} ■ (■ P → Q).
  Proof. apply n_bysem=>/= >. iIntros "#H !# #H'". iApply ("H" with "H'"). Qed.

  (** Laws for [|==>] *)
  Lemma n_bupd_mono {d i P Q} : P ⊢{δ d, i} Q → (|==> P) ⊢{δ d, i} |==> Q.
  Proof. move=> ?. apply n_bysem=>/= >. apply bupd_mono. by apply nin_sem. Qed.
  Lemma n_bupd_intro {d i P} : P ⊢{δ d, i} |==> P.
  Proof. apply n_bysem=>/= >. apply bupd_intro. Qed.
  Lemma n_bupd_trans {d i P} : (|==> |==> P) ⊢{δ d, i} |==> P.
  Proof. apply n_bysem=>/= >. apply bupd_trans. Qed.
  Lemma n_bupd_frame_r {d i P Q} : (|==> P) ∗ Q ⊢{δ d, i} |==> P ∗ Q.
  Proof. apply n_bysem=>/= >. apply bupd_frame_r. Qed.
  Lemma n_bupd_plainly {d i P} : (|==> ■ P) ⊢{δ d, i} ■ P.
  Proof. apply n_bysem=>/= >. by iIntros ">?". Qed.

  (** Laws for [|={_,_}=>] *)
  Lemma n_fupd_mask_subseteq {d i E E' P} :
    E' ⊆ E → P ⊢{δ d, i} |={E,E'}=> |={E',E}=> True.
  Proof.
    move=> ?. apply n_bysem=>/= >. iIntros "_". by iMod fupd_mask_subseteq.
  Qed.
  Lemma n_except_0_fupd {d i E E' P} :
    ◇ (|={E,E'}=> P) ⊢{δ d, i} |={E,E'}=> P.
  Proof.
    apply n_bysem=>/= >. rewrite nintp_fp_nintp/=. by iDestruct 1 as "[>?|?]".
  Qed.
  Lemma n_fupd_mono {d i E E' P Q} :
    P ⊢{δ d, i} Q → (|={E,E'}=> P) ⊢{δ d, i} |={E,E'}=> Q.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply fupd_mono. by apply nin_sem.
  Qed.
  Lemma n_fupd_trans {d i E E' E'' P} :
    (|={E,E'}=> |={E',E''}=> P) ⊢{δ d, i} |={E,E''}=> P.
  Proof. apply n_bysem=>/= >. apply fupd_trans. Qed.
  Lemma n_fupd_mask_frame_r' {d i E E' Ef P} :
    E ## Ef → (|={E,E'}=> ⌜E' ## Ef⌝ → P) ⊢{δ d, i} |={E ∪ Ef,E' ∪ Ef}=> P.
  Proof. move=> ?. apply n_bysem=>/= >. by apply fupd_mask_frame_r'. Qed.
  Lemma n_fupd_frame_r {d i E E' P Q} :
    (|={E,E'}=> P) ∗ Q ⊢{δ d, i} |={E,E'}=> P ∗ Q.
  Proof. apply n_bysem=>/= >. apply fupd_frame_r. Qed.

  (** Laws for [▷] *)
  Lemma n_later_mono {d i P Q} : P ⊢{δ d, i} Q → ▷{nil} P ⊢{δ d, i} ▷{nil} Q.
  Proof.
    move=> ?. apply n_bysem=>/= >. f_equiv. rewrite !nintp_fp_nintp.
    by apply nin_sem.
  Qed.
  Lemma n_later_intro {d i} {P : _ (;ᵞ)} : P ⊢{δ d, i} ▷{nil} P.
  Proof.
    apply n_bysem=>/= >. rewrite nintp_fp_nintp. apply bi.later_intro.
  Qed.
  Lemma n_later_forall_2 {d i A} {Φ : A → _ (;ᵞ)} :
    (∀ a, ▷{nil} Φ a) ⊢{δ d, i} ▷{nil} ∀' Φ.
  Proof.
    apply n_bysem=>/= >. setoid_rewrite nintp_fp_nintp=>/=.
    apply bi.later_forall_2.
  Qed.
  Lemma n_later_exist_except_0 {d i A} {Φ : A → _ (;ᵞ)} :
    ▷{nil} (∃ a, Φ a) ⊢{δ d, i} ◇ (∃ a, ▷{nil} Φ a).
  Proof.
    apply n_bysem=>/= >. setoid_rewrite nintp_fp_nintp=>/=.
    apply bi.later_exist_false.
  Qed.
  Lemma n_later_sep_1 {d i} {P Q : _ (;ᵞ)} :
    ▷{nil} (P ∗ Q) ⊢{δ d, i} ▷{nil} P ∗ ▷{nil} Q.
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. apply bi.later_sep_1.
  Qed.
  Lemma n_later_sep_2 {d i} {P Q : _ (;ᵞ)} :
    ▷{nil} P ∗ ▷{nil} Q ⊢{δ d, i} ▷{nil} (P ∗ Q).
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. apply bi.later_sep_2.
  Qed.
  Lemma n_later_false_em {d i} {P : _ (;ᵞ)} :
    ▷{nil} P ⊢{δ d, i} ◇ (▷ False → P).
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. apply bi.later_false_em.
  Qed.
  Lemma n_later_persistently_1 {d i} {P : _ (;ᵞ)} :
    ▷{nil} □ P ⊢{δ d, i} □ ▷{nil} P.
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. iIntros "#? !#". by iNext.
  Qed.
  Lemma n_later_persistently_2 {d i} {P : _ (;ᵞ)} :
    □ ▷{nil} P ⊢{δ d, i} ▷{nil} □ P.
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. iIntros. by iNext.
  Qed.
  Lemma n_later_plainly_1 {d i} {P : _ (;ᵞ)} : ▷{nil} ■ P ⊢{δ d, i} ■ ▷{nil} P.
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. iIntros "#? !#". by iNext.
  Qed.
  Lemma n_later_plainly_2 {d i} {P : _ (;ᵞ)} : ■ ▷{nil} P ⊢{δ d, i} ▷{nil} ■ P.
  Proof.
    apply n_bysem=>/= >. rewrite !nintp_fp_nintp/=. iIntros. by iNext.
  Qed.
  Lemma n_löb {d i P} : (▷{nil} P → P) ⊢{δ d, i} P.
  Proof. apply n_bysem=>/= >. rewrite nintp_fp_nintp/=. apply bi.löb. Qed.

  (** Laws for [∀:] *)
  Lemma n_n_forall_intro {d i V P Q} :
    (∀ Φ, P ⊢{δ d, i} nsubst Q Φ) → P ⊢{δ d, i} ∀: V, Q.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.forall_intro=> ?.
    rewrite rew_eq_hwf. by apply nin_sem.
  Qed.
  Lemma n_n_forall_elim {d i V P Φ} : (∀: V, P) ⊢{δ d, i} nsubst P Φ.
  Proof.
    apply n_bysem=>/= >. setoid_rewrite rew_eq_hwf.
    apply (bi.forall_elim (Ψ := λ _, _)).
  Qed.

  (** Laws for [∃:] *)
  Lemma n_n_exist_intro {d i V P Φ} : nsubst P Φ ⊢{δ d, i} ∃: V, P.
  Proof.
    apply n_bysem=>/= >. setoid_rewrite rew_eq_hwf.
    apply (bi.exist_intro (Ψ := λ Φ, ⟦ nsubst _ Φ ⟧(_))).
  Qed.
  Lemma n_n_exist_elim {d i V P Q} :
    (∀ Φ, nsubst P Φ ⊢{δ d, i} Q) → (∃: V, P) ⊢{δ d, i} Q.
  Proof.
    move=> ?. apply n_bysem=>/= >. apply bi.exist_elim=> ?.
    rewrite rew_eq_hwf. by apply nin_sem.
  Qed.
End bi.

(** ** Nola-specific laws *)
Section nola.
  Context `{!nintpG Σ, !nderivy Σ δ}.

  (** Laws for [rec:ˢ] *)
  Lemma n_recs_unfold {d i A Φ} {a : A} :
    rec:ˢ' Φ a ⊢{δ d, i} nlarge (nsubst (Φ a) (rec:ˢ' Φ)).
  Proof. apply n_bysem=>/= >. by rewrite rew_eq_hwf nintp_nlarge. Qed.
  Lemma n_recs_fold {d i A Φ} {a : A} :
    nlarge (nsubst (Φ a) (rec:ˢ' Φ)) ⊢{δ d, i} rec:ˢ' Φ a.
  Proof. apply n_bysem=>/= >. by rewrite nintp_nlarge rew_eq_hwf. Qed.

  (** Laws for [rec:ˡ] *)
  Lemma n_recl_unfold {d i A Φ} {a : A} :
    rec:ˡ' Φ a ⊢{δ d, i} nsubst (Φ a) (rec:ˡ' Φ).
  Proof. apply n_bysem=>/= >. by rewrite rew_eq_hwf. Qed.
  Lemma n_recl_fold {d i A Φ} {a : A} :
    nsubst (Φ a) (rec:ˡ' Φ) ⊢{δ d, i} rec:ˡ' Φ a.
  Proof. apply n_bysem=>/= >. by rewrite rew_eq_hwf. Qed.

  (** Laws for [!ᵘˢ] *)
  Lemma n_subus_unfold {d i P} : !ᵘˢ P ⊢{δ d, i} nlarge P.
  Proof. apply n_bysem=>/= >. by rewrite nintpS_nintp_nlarge. Qed.
  Lemma n_subus_fold {d i P} : nlarge P ⊢{δ d, i} !ᵘˢ P.
  Proof. apply n_bysem=>/= >. by rewrite nintpS_nintp_nlarge. Qed.

  (** Laws for [⊢] *)
  Lemma n_deriv_intro {d i j P Q R} :
    P ⊢{δ $∨ⁿᵈ d, j} Q → R ⊢{δ d, i} (P ⊢{j}{nil} Q).
  Proof. move=> ?. apply n_bysem=>/= >. by apply bi.pure_intro, nin_turn. Qed.
  Lemma n_deriv_elim_l_low {d i j} {P Q : _ (;ᵞ)} :
    j < i → (P ⊢{j}{nil} Q) ∧ P ⊢{δ d, i} Q.
  Proof.
    move=> ji. apply n_bysem=>/= δ' ?. apply bi.pure_elim_l=> PQ.
    by apply (nin_semlow ji).
  Qed.
  Lemma n_deriv_convert {d i j A f} {Φ Ψ : A → _ (;ᵞ)} {P Q : _ (;ᵞ)} :
    (∀ δ', nderivy Σ δ' → (∀ a, Φ a ⊢{δ' ⊥ⁿᵈ, f a} Ψ a) → P ⊢{δ' ⊥ⁿᵈ, j} Q) →
    (∀ a, Φ a ⊢{f a}{nil} Ψ a) ⊢{δ d, i} (P ⊢{j}{nil} Q).
  Proof.
    move=> H. apply n_bysem=>/= >. rewrite -bi.pure_forall.
    apply bi.pure_mono, H. split. apply _.
  Qed.
End nola.
