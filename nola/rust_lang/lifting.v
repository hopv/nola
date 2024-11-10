From iris.proofmode Require Import proofmode.
From nola.bi Require Export wpw.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From nola.rust_lang Require Export lang heap.
From nola.rust_lang Require Import tactics.
From iris.prelude Require Import options.
Import uPred ModwNotation WpwNotation.

Class lrustGS_gen hlc Σ : Type := LRustGS {
  lrustGS_invGS : invGS_gen hlc Σ;
  lrustGS_heapGS :: heapGS Σ;
}.

Global Instance lrustGS_iris'GS `{!lrustGS_gen hlc Σ}
  : iris'GS_gen hlc lrust_lang Σ := {
  iris'_invGS := lrustGS_invGS;
  state_interp' σ _ κs _ := heap_ctx σ;
  fork_post' _ := True%I;
  num_laters_per_step' _ := 0%nat;
  state_interp'_mono _ _ _ _ := fupd_intro _ _
}.

(** ** Helper instances
  TODO: Can we remove these? *)
Section instances.
  Context `{!lrustGS_gen hlc Σ}.
  Let iris := lrustGS_iris'GS.

  #[export] Instance wpw_nonval_is_fupdw {e s E W Φ} :
    IsFUpdW (to_val e = None) W E (WP[W] e @ s; E {{ Φ }}).
  Proof. exact _. Qed.
  #[export] Instance wpw_fupdw_is_fupdw {e s E W Φ} :
    IsFUpdW True W E (WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }})%I.
  Proof. exact _. Qed.

  #[export] Instance twpw_nonval_is_fupdw {e s E W Φ} :
    IsFUpdW (to_val e = None) W E (WP[W] e @ s; E [{ Φ }]).
  Proof. exact _. Qed.
  #[export] Instance twpw_fupdw_is_fupdw {e s E W Φ} :
    IsFUpdW True W E (WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }])%I.
  Proof. exact _. Qed.
End instances.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H;
    simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl
  : core.

Local Hint Constructors base_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) : Prop :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) : Prop :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) : Prop :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma twp_fork W E e :
  [[{ WP[W] e [{ _, True }] }]][W] Fork e @ E [[{ RET LitV LitPoison; True }]].
Proof.
  iIntros (?) "?HΦ". iApply twp_lift_atomic_base_step; [done|].
  iIntros (σ1 ns κs nt) "[$ Hσ] !>". iSplit; first by eauto.
  iIntros (?????) "!>". inv_base_step. iSplit; [done|]. iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_fork W E e :
  {{{ ▷ WP[W] e {{ _, True }} }}}[W] Fork e @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 κ ? κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_base_step. iFrame.
  iModIntro. by iApply "HΦ".
Qed.

(** Non-determinism *)
Lemma twp_ndnat W E :
  [[{ True }]][W] Ndnat @ E [[{ (n : nat), RET (LitV (LitInt n)); True }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (????) "[W ?] !>". iSplit.
  { iPureIntro. eexists _, _, _. apply (NdnatS 0). }
  iIntros (?????). inv_base_step. iModIntro. do 2 (iSplit=>//). iFrame.
  by iApply "HΦ".
Qed.
Lemma wp_ndnat W E :
  {{{ True }}}[W] Ndnat @ E {{{ (n : nat), RET (LitV (LitInt n)); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ"). iApply twp_ndnat; [done|].
  iIntros (n) "_ HΦ". by iApply "HΦ".
Qed.

(** Pure reductions *)
Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; do 3 eexists; econstructor; simpl;
  eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_base_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  eapply Forall_impl; [exact Hel|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)))
    (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit false)) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit false) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2))
    (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2))
    (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z  :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z))
    (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1
    (Case (Lit $ LitInt i) el) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

(** Heap *)
Lemma twp_alloc W E (n : Z) :
  0 < n →
  [[{ True }]][W] Alloc (Lit $ LitInt n) @ E
  [[{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗
    l ↦∗ repeat (LitV LitPoison) sz }]].
Proof.
  iIntros (? Φ) "_ HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ] !>"; iSplit; first by auto. iIntros (?????).
  inv_base_step. iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [done..|].
  iModIntro; do 2 (iSplit=> //). iFrame.
  iApply ("HΦ" $! _ (Z.to_nat n)). iFrame. iPureIntro. rewrite Z2Nat.id; lia.
Qed.
Lemma wp_alloc W E (n : Z) :
  0 < n →
  {{{ True }}}[W] Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗
    l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (??) "_ →Φ". iApply (twp_wp_step with "→Φ").
  iApply twp_alloc=>//. iIntros (??) "? →Φ". by iApply "→Φ".
Qed.

Lemma twp_free W E (n:Z) l vl :
  n = length vl →
  [[{ l ↦∗ vl ∗ †l…(length vl) }]][W]
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  [[{ RET LitV LitPoison; True }]].
Proof.
  iIntros (? Φ) "[Hmt Hf] HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iModIntro; iSplit; first by auto. iIntros (?????) "!>". inv_base_step.
  do 2 (iSplit=> //). iFrame. by iApply "HΦ".
Qed.
Lemma wp_free W E (n:Z) l vl :
  n = length vl →
  {{{ l ↦∗ vl ∗ †l…(length vl) }}}[W]
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_free with "H")=>//. iIntros "_ →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_read_sc W E l q v :
  [[{ l ↦{q} v }]][W] Read ScOrd (Lit $ LitLoc l) @ E
  [[{ RET v; l ↦{q} v }]].
Proof.
  iIntros (?) "Hv HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]". iDestruct (heap_read with "Hσ Hv") as %[m ?].
  iModIntro; iSplit; first by eauto. iIntros (?????) "!>". inv_base_step.
  do 2 (iSplit=> //). iFrame. by iApply "HΦ".
Qed.
Lemma wp_read_sc W E l q v :
  {{{ l ↦{q} v }}}[W] Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_sc with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_read_na W E l q v :
  [[{ l ↦{q} v }]][W] Read Na1Ord (Lit $ LitLoc l) @ E
  [[{ RET v; l ↦{q} v }]].
Proof.
  iIntros (Φ) "Hv HΦ". iApply twp_lift_base_step; auto.
  iIntros (????) "[$ Hσ]".
  iMod (heap_read_na with "Hσ Hv") as (m) "(% & Hσ & Hσclose)".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iIntros (?????). inv_base_step. iMod "Hclose" as "_". iModIntro. iFrame "Hσ".
  iSplit; [done|]. iSplit; [|done].
  iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]".
  iMod ("Hσclose" with "Hσ") as (n) "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto. iIntros (?????) "!>". inv_base_step.
  do 2 (iSplit=> //). iFrame "Hσ". by iApply "HΦ".
Qed.
Lemma wp_read_na W E l q v :
  {{{ l ↦{q} v }}}[W] Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (?) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_read_na with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_write_sc W E l e v v' :
  IntoVal e v →
  [[{ l ↦ v' }]][W] Write ScOrd (Lit $ LitLoc l) e @ E
  [[{ RET LitV LitPoison; l ↦ v }]].
Proof.
  iIntros (<- Φ) "Hv HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iMod (heap_write _ _ _  v with "Hσ Hv") as "[Hσ Hv]".
  iModIntro; iSplit; first by eauto. iIntros (?????) "!>". inv_base_step.
  do 2 (iSplit=> //). iFrame. by iApply "HΦ".
Qed.
Lemma wp_write_sc W E l e v v' :
  IntoVal e v →
  {{{ l ↦ v' }}}[W] Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_sc with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_write_na W E l e v v' :
  IntoVal e v →
  [[{ l ↦ v' }]][W] Write Na1Ord (Lit $ LitLoc l) e @ E
  [[{ RET LitV LitPoison; l ↦ v }]].
Proof.
  iIntros (<- Φ) "Hv HΦ". iApply twp_lift_base_step; auto.
  iIntros (????) "[$ Hσ]".
  iMod (heap_write_na with "Hσ Hv") as "(% & Hσ & Hσclose)".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto. iIntros (?????). inv_base_step.
  iMod "Hclose" as "_". iModIntro. iFrame "Hσ". do 2 (iSplit=> //).
  iApply twp_lift_atomic_base_step_no_fork; auto. iIntros (????) "[$ Hσ]".
  iMod ("Hσclose" with "Hσ") as "(% & Hσ & Hv)". iModIntro.
  iSplit; first by eauto. iIntros (?????) "!>". inv_base_step.
  do 2 (iSplit=> //). iFrame "Hσ". by iApply "HΦ".
Qed.
Lemma wp_write_na W E l e v v' :
  IntoVal e v →
  {{{ l ↦ v' }}}[W] Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_write_na with "H"). iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_cas_int_fail W E l q z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  [[{ l ↦{q} LitV (LitInt zl) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  [[{ RET LitV false; l ↦{q} LitV (LitInt zl) }]].
Proof.
  iIntros (<- ? Φ) "Hv HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]". iDestruct (heap_read with "Hσ Hv") as %[m ?].
  iModIntro; iSplit; first by eauto. iIntros (?????) "!>".
  inv_base_step; inv_lit. do 2 (iSplit=> //). iFrame. by iApply "HΦ".
Qed.
Lemma wp_cas_int_fail W E l q z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ l ↦{q} LitV (LitInt zl) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV false; l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (???) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_int_fail with "H")=>//. iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_cas_suc W E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  [[{ l ↦ LitV lit1 }]][W]
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  [[{ RET LitV true; l ↦ LitV lit2 }]].
Proof.
  iIntros (<- ? Φ) "Hv HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct lit1; by eauto). iIntros (?????).
  inv_base_step; [inv_lit|]. iMod (heap_write with "Hσ Hv") as "[$ Hv]".
  iModIntro. do 2 (iSplitR=> //). by iApply "HΦ".
Qed.
Lemma wp_cas_suc W E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ l ↦ LitV lit1 }}}[W]
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV true; l ↦ LitV lit2 }}}.
Proof.
  iIntros (???) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_suc with "H")=>//. iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_cas_int_suc W E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  [[{ l ↦ LitV (LitInt z1) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  [[{ RET LitV true; l ↦ LitV lit2 }]].
Proof. intros ?. by apply twp_cas_suc. Qed.
Lemma wp_cas_int_suc W E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ l ↦ LitV (LitInt z1) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV true; l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma twp_cas_loc_suc W E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  [[{ l ↦ LitV (LitLoc l1) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  [[{ RET LitV true; l ↦ LitV lit2 }]].
Proof. intros ?. by apply twp_cas_suc. Qed.
Lemma wp_cas_loc_suc W E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) →
  {{{ l ↦ LitV (LitLoc l1) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV true; l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma twp_cas_loc_fail W E l q q' q1 l1 v1' e2 lit2 l' vl' :
  IntoVal e2 (LitV lit2) → l1 ≠ l' →
  [[{ l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  [[{ RET LitV false;
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }]].
Proof.
  iIntros (<- ? Φ) "(Hl & Hl' & Hl1) HΦ".
  iApply twp_lift_atomic_base_step_no_fork; auto. iIntros (????) "[$ Hσ]".
  iDestruct (heap_read with "Hσ Hl") as %[nl ?].
  iDestruct (heap_read with "Hσ Hl'") as %[nl' ?].
  iDestruct (heap_read with "Hσ Hl1") as %[nl1 ?].
  iModIntro; iSplit; first by eauto. iIntros (?????). inv_base_step; inv_lit.
  iModIntro. do 2 (iSplit=> //). iFrame. iApply "HΦ". iFrame.
Qed.
Lemma wp_cas_loc_fail W E l q q' q1 l1 v1' e2 lit2 l' vl' :
  IntoVal e2 (LitV lit2) → l1 ≠ l' →
  {{{ l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV false;
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (???) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_loc_fail with "H")=>//. iIntros "? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_cas_loc_nondet W E l l1 e2 l2 ll :
  IntoVal e2 (LitV $ LitLoc l2) →
  [[{ l ↦ LitV (LitLoc ll) }]][W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  [[{ b, RET LitV (lit_of_bool b);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }]].
Proof.
  iIntros (<- Φ) "Hv HΦ". iApply twp_lift_atomic_base_step_no_fork; auto.
  iIntros (????) "[$ Hσ]". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct (decide (ll = l1)) as [->|]; by eauto).
  iIntros (?????). inv_base_step; last lia; do 2 (iSplitR=>//).
  - inv_lit. iFrame "Hσ". iApply "HΦ". auto.
  - iMod (heap_write with "Hσ Hv") as "[$ Hv]". iModIntro. by iApply "HΦ".
Qed.
Lemma wp_cas_loc_nondet W E l l1 e2 l2 ll :
  IntoVal e2 (LitV $ LitLoc l2) →
  {{{ l ↦ LitV (LitLoc ll) }}}[W]
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ b, RET LitV (lit_of_bool b);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (??) "H →Φ". iApply (twp_wp_step with "→Φ").
  iApply (twp_cas_loc_nondet with "H"). iIntros "% ? →Φ !>". by iApply "→Φ".
Qed.

Lemma twp_eq_loc W E (l1 : loc) (l2: loc) q1 q2 v1 v2 P Φ :
  (P ⊢ l1 ↦{q1} v1) → (P ⊢ l2 ↦{q2} v2) →
  (P ⊢ Φ (LitV (bool_decide (l1 = l2)))) →
  P ⊢ WP[W] BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E [{ Φ }].
Proof.
  iIntros (Hl1 Hl2 Hpost) "P".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply (twp_lift_pure_det_base_step_no_fork (Λ:=lrust_ectx_lang));
      [done|solve_exec_safe|solve_exec_puredet|].
    rewrite Hpost. by iApply twp_value.
  - iApply twp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (????) "[$ Hσ1]". inv_base_step. iModIntro. iSplit.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    iAssert (l1 ↦{q1} v1 ∧ l2 ↦{q2} v2 ∧ Φ (LitV false))%I with "[P]" as "P".
    { iSplit; last iSplit; by [iApply Hl1|iApply Hl2|iApply Hpost]. }
    clear Hl1 Hl2. iIntros (?????). inv_base_step. do 2 (iSplitR=>//).
    inv_bin_op_eval; inv_lit.
    + iExFalso. iDestruct "P" as "[Hl1 _]".
      iDestruct (heap_read with "Hσ1 Hl1") as %[??]. simplify_eq.
    + iExFalso. iDestruct "P" as "[_ [Hl2 _]]".
      iDestruct (heap_read with "Hσ1 Hl2") as %[??]. simplify_eq.
    + by iDestruct "P" as "[_ [_ $]]".
Qed.
Lemma wp_eq_loc W E (l1 : loc) (l2: loc) q1 q2 v1 v2 P Φ :
  (P ⊢ ▷ l1 ↦{q1} v1) → (P ⊢ ▷ l2 ↦{q2} v2) →
  (P ⊢ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P ⊢ WP[W] BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost) "P".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply (wp_lift_pure_det_base_step_no_fork (Λ:=lrust_ectx_lang));
      [done|solve_exec_safe|solve_exec_puredet|].
    rewrite Hpost. iIntros "!>!>!> _". by iApply wp_value.
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (?????) "[$ Hσ1]". inv_base_step. iModIntro. iSplit.
    { iPureIntro. repeat eexists. econstructor. eapply BinOpEqFalse. by auto. }
    iAssert (▷ (l1 ↦{q1} v1 ∧ l2 ↦{q2} v2 ∧ Φ (LitV false)))%I with "[P]"
      as "P".
    { iSplit; last iSplit; by [iApply Hl1|iApply Hl2|iApply Hpost]. }
    clear Hl1 Hl2. iIntros (????) "!> _". inv_base_step. iSplitR=>//.
    inv_bin_op_eval; inv_lit.
    + iExFalso. iDestruct "P" as "[Hl1 _]".
      iDestruct (heap_read with "Hσ1 Hl1") as %[??]. simplify_eq.
    + iExFalso. iDestruct "P" as "[_ [Hl2 _]]".
      iDestruct (heap_read with "Hσ1 Hl2") as %[??]. simplify_eq.
    + by iDestruct "P" as "[_ [_ $]]".
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma twp_app_ind W E f (el : list expr) (Ql : vec (val → iProp Σ) (length el))
  vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E [{ eQ.2 }]) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> vs ++ vl) @ E [{ Φ }]) -∗
    WP[W] App f ((of_val <$> vs) ++ el) @ E [{ Φ }].
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=.
    by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with
      (fill_item (AppRCtx vf vs el) e).
    iApply twp_bind. iApply (twp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.
Lemma wp_app_ind W E f (el : list expr) (Ql : vec (val → iProp Σ) (length el))
  vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP[W] App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=.
    by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with
      (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "%vl Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma twp_app_vec W E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E [{ eQ.2 }]) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> (vl : list val)) @ E [{ Φ }]) -∗
    WP[W] App f el @ E [{ Φ }].
Proof. iIntros (Hf). by iApply (twp_app_ind _ _ _ _ _ []). Qed.
Lemma wp_app_vec W E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP[W] App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP[W] App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ _ []). Qed.

Lemma twp_app (Ql : list (val → iProp Σ)) W E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E [{ eQ.2 }]) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ →
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP[W] App f (of_val <$> (vl : list val)) @ E [{ Φ }]) -∗
    WP[W] App f el @ E [{ Φ }].
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (twp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.
Lemma wp_app (Ql : list (val → iProp Σ)) W E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP[W] eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ →
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP[W] App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP[W] App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.
End lifting.
