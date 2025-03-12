(** * Proof mode utility for the program logic *)

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export proofmode.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import lifting.
From nola.rust_lang Require Export tactics lifting.
From iris.prelude Require Import options.
Import uPred WpwNotation.

Lemma tac_twp_value `{!lrustGS_gen hlc Σ} Δ W E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP[W] e @ E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ? ->. by apply twp_value. Qed.
Lemma tac_wp_value `{!lrustGS_gen hlc Σ} Δ W E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP[W] e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ? ->. by apply wp_value. Qed.

Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (twpw _ _ _ _ _) =>
      eapply tac_twp_value; [tc_solve|reduction.pm_prettify]
  | |- envs_entails _ (wpw _ _ _ _ _) =>
      eapply tac_wp_value; [tc_solve|reduction.pm_prettify]
  end.

Lemma tac_twp_pure `{!lrustGS_gen hlc Σ} K Δ W E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP[W] fill K e2 @ E [{ Φ }]) →
  envs_entails Δ (WP[W] fill K e1 @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ?? H. rewrite -twp_bind.
  rewrite -total_lifting.twp_pure_step // H. iApply twp_bind_inv.
Qed.
Lemma tac_wp_pure `{!lrustGS_gen hlc Σ} K Δ Δ' W E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP[W] fill K e2 @ E {{ Φ }}) →
  envs_entails Δ (WP[W] fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite -wp_bind HΔ' -wp_pure_step_later //. rewrite -wp_bind_inv.
  f_equiv. apply wand_intro_l. by rewrite sep_elim_r.
Qed.

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_wp_pure K);
    [simpl; tc_solve                (* PureExec *)
    |try done                       (* The pure condition for PureExec *)
    |tc_solve                       (* IntoLaters *)
    |simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_twp_pure K);
    [simpl; tc_solve                (* PureExec *)
    |try done                       (* The pure condition for PureExec *)
    |simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Lemma tac_twp_eq_loc `{!lrustGS_gen hlc Σ} K Δ W E i1 i2 l1 l2 q1 q2 v1 v2 Φ :
  envs_lookup i1 Δ = Some (false, l1 ↦{q1} v1)%I →
  envs_lookup i2 Δ = Some (false, l2 ↦{q2} v2)%I →
  envs_entails Δ (WP[W] fill K (Lit (bool_decide (l1 = l2))) @ E [{ Φ }]) →
  envs_entails Δ (WP[W]
    fill K (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2))) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> /envs_lookup_sound. rewrite sep_elim_l=> ?.
  move /envs_lookup_sound; rewrite sep_elim_l=> ? HΔ. rewrite -twp_bind.
  by eapply twp_eq_loc.
Qed.
Lemma tac_wp_eq_loc `{!lrustGS_gen hlc Σ} K Δ Δ' W E i1 i2 l1 l2 q1 q2 v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ' = Some (false, l1 ↦{q1} v1)%I →
  envs_lookup i2 Δ' = Some (false, l2 ↦{q2} v2)%I →
  envs_entails Δ' (WP[W] fill K (Lit (bool_decide (l1 = l2))) @ E {{ Φ }}) →
  envs_entails Δ (WP[W]
    fill K (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2))) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? /envs_lookup_sound /=. rewrite sep_elim_l=> ?.
  move /envs_lookup_sound; rewrite sep_elim_l=> ? HΔ. rewrite -wp_bind.
  rewrite into_laterN_env_sound /=. eapply wp_eq_loc; eauto using later_mono.
Qed.

Tactic Notation "wp_eq_loc" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
     reshape_expr e ltac:(fun K e' => eapply (tac_twp_eq_loc K));
       [iAssumptionCore|iAssumptionCore|simpl; try wp_value_head]
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
     reshape_expr e ltac:(fun K e' => eapply (tac_wp_eq_loc K));
       [tc_solve|iAssumptionCore|iAssumptionCore|simpl; try wp_value_head]
  | _ => fail "wp_eq_loc: not a 'wp'"
  end.

Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.
Tactic Notation "wp_op" := wp_pure (BinOp _ _ _) || wp_eq_loc.
Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_case" := wp_pure (Case _ _); try wp_value_head.

Lemma tac_twp_bind `{!lrustGS_gen hlc Σ} K Δ W E Φ e :
  envs_entails Δ (WP[W] e @ E [{ v, WP[W] fill K (of_val v) @ E [{ Φ }] }])%I →
  envs_entails Δ (WP[W] fill K e @ E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. apply: twp_bind. Qed.
Lemma tac_wp_bind `{!lrustGS_gen hlc Σ} K Δ W E Φ e :
  envs_entails Δ (WP[W] e @ E {{ v, WP[W] fill K (of_val v) @ E {{ Φ }} }})%I →
  envs_entails Δ (WP[W] fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. apply: wp_bind. Qed.

Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_twp_bind K); simpl
  end.
Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_wp_bind K); simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; twp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

Tactic Notation "wp_apply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; iApplyHyp H; try iNext; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Section heap.
Context `{!lrustGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).

Lemma tac_twp_alloc K Δ W E j1 j2 n Φ :
  0 < n →
  (∀ l (sz: nat), n = sz → ∃ Δ'',
    envs_app false
      (Esnoc (Esnoc Enil j1 (l ↦∗ repeat (LitV LitPoison) sz)) j2 (†l…sz)) Δ
      = Some Δ'' ∧
    envs_entails Δ'' (WP[W] fill K (Lit $ LitLoc l) @ E [{ Φ }])) →
  envs_entails Δ (WP[W] fill K (Alloc (Lit $ LitInt n)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. rewrite -twp_bind.
  eapply wand_apply; first by apply wand_entails, twp_alloc.
  rewrite -persistent_and_sep. apply and_intro; first by auto.
  apply forall_intro=> l. apply forall_intro=>sz. apply wand_intro_l.
  rewrite -persistent_and_sep_assoc. apply pure_elim_l=> Hn. apply wand_elim_r'.
  destruct (HΔ l sz) as (Δ''&?&HΔ'); first done.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.
Lemma tac_wp_alloc K Δ Δ' W E j1 j2 n Φ :
  0 < n →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l (sz: nat), n = sz → ∃ Δ'',
    envs_app false
      (Esnoc (Esnoc Enil j1 (l ↦∗ repeat (LitV LitPoison) sz)) j2 (†l…sz)) Δ'
      = Some Δ'' ∧
    envs_entails Δ'' (WP[W] fill K (Lit $ LitLoc l) @ E {{ Φ }})) →
  envs_entails Δ (WP[W] fill K (Alloc (Lit $ LitInt n)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΔ. rewrite -wp_bind.
  eapply wand_apply; first by apply wand_entails, wp_alloc.
  rewrite -persistent_and_sep. apply and_intro; first by auto.
  rewrite into_laterN_env_sound; apply later_mono, forall_intro=> l.
  apply forall_intro=>sz. apply wand_intro_l. rewrite -persistent_and_sep_assoc.
  apply pure_elim_l=> Hn. apply wand_elim_r'.
  destruct (HΔ l sz) as (Δ''&?&HΔ'); first done.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.

Lemma tac_twp_free K Δ Δ' Δ'' W E i1 i2 vl (n : Z) (n' : nat) l Φ :
  n = length vl →
  envs_lookup i1 Δ = Some (false, l ↦∗ vl)%I →
  envs_delete false i1 false Δ = Δ' →
  envs_lookup i2 Δ' = Some (false, †l…n')%I →
  envs_delete false i2 false Δ' = Δ'' →
  n' = length vl →
  envs_entails Δ'' (WP[W] fill K (Lit LitPoison) @ E [{ Φ }]) →
  envs_entails Δ (WP[W]
    fill K (Free (Lit $ LitInt n) (Lit $ LitLoc l)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> -> /envs_lookup_sound -> <-.
  move=> /envs_lookup_sound -> <- -> -> /=. iIntros "(↦ & † & ?)".
  iApply twp_bind. iApply (twp_free with "[$↦ $†]")=>//. by iIntros.
Qed.
Lemma tac_wp_free K Δ Δ' Δ'' Δ''' W E i1 i2 vl (n : Z) (n' : nat) l Φ :
  n = length vl →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ' = Some (false, l ↦∗ vl)%I →
  envs_delete false i1 false Δ' = Δ'' →
  envs_lookup i2 Δ'' = Some (false, †l…n')%I →
  envs_delete false i2 false Δ'' = Δ''' →
  n' = length vl →
  envs_entails Δ''' (WP[W] fill K (Lit LitPoison) @ E {{ Φ }}) →
  envs_entails Δ (WP[W]
    fill K (Free (Lit $ LitInt n) (Lit $ LitLoc l)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> -> ?. rewrite into_laterN_env_sound /=.
  move=> /envs_lookup_sound -> <- /envs_lookup_sound -> <- -> -> /=.
  iIntros "(>↦ & >† & ?)". iApply wp_bind. iApply (wp_free with "[$↦ $†]")=>//.
  iNext. by iIntros.
Qed.

Lemma tac_twp_read K Δ W E i l q v o Φ :
  o = Na1Ord ∨ o = ScOrd →
  envs_lookup i Δ = Some (false, l ↦{q} v)%I →
  envs_entails Δ (WP[W] fill K (of_val v) @ E [{ Φ }]) →
  envs_entails Δ (WP[W] fill K (Read o (Lit $ LitLoc l)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> eq /envs_lookup_split {2}-> -> /=.
  iIntros "[↦ ?]". iApply twp_bind.
  case: eq=> [->|->];
    by [iApply (twp_read_na with "↦")|iApply (twp_read_sc with "↦")].
Qed.
Lemma tac_wp_read K Δ Δ' W E i l q v o Φ :
  o = Na1Ord ∨ o = ScOrd →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  envs_entails Δ' (WP[W] fill K (of_val v) @ E {{ Φ }}) →
  envs_entails Δ (WP[W] fill K (Read o (Lit $ LitLoc l)) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> eq ?. rewrite into_laterN_env_sound /=.
  move=> /envs_lookup_split {2}-> -> /=. iIntros "[>↦ ?]". iApply wp_bind.
  case: eq=> [->|->];
    by [iApply (wp_read_na with "↦")|iApply (wp_read_sc with "↦")].
Qed.

Lemma tac_twp_write K Δ Δ' W E i l v e v' o Φ :
  IntoVal e v' →
  o = Na1Ord ∨ o = ScOrd →
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ = Some Δ' →
  envs_entails Δ' (WP[W] fill K (Lit LitPoison) @ E [{ Φ }]) →
  envs_entails Δ (WP[W] fill K (Write o (Lit $ LitLoc l) e) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? eq look /envs_simple_replace_sound to.
  move: (to _ look)=> -> -> /=. rewrite right_id. iIntros "[↦ ?]".
  iApply twp_bind.
  by case: eq=> [->|->];
    [iApply (twp_write_na with "↦")|iApply (twp_write_sc with "↦")].
Qed.
Lemma tac_wp_write K Δ Δ' Δ'' W E i l v e v' o Φ :
  IntoVal e v' →
  o = Na1Ord ∨ o = ScOrd →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP[W] fill K (Lit LitPoison) @ E {{ Φ }}) →
  envs_entails Δ (WP[W] fill K (Write o (Lit $ LitLoc l) e) @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? eq ?. rewrite into_laterN_env_sound /=.
  move=> look /envs_simple_replace_sound to. move: (to _ look)=> -> -> /=.
  rewrite right_id. iIntros "[>↦ ?]". iApply wp_bind.
  by case: eq=> [->|->];
    [iApply (wp_write_na with "↦")|iApply (wp_write_sc with "↦")].
Qed.
End heap.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) constr(Hf) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc K _ _ _ H Hf))
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [try fast_done
    |let sz := fresh "sz" in let Hsz := fresh "Hsz" in
     first [intros l sz Hsz | fail 1 "wp_alloc:" l "not fresh"];
     (* If Hsz is "constant Z = nat", change that to an equation on nat and
        potentially substitute away the sz. *)
     try (match goal with Hsz : ?x = _ |- _ => rewrite <-(Z2Nat.id x) in Hsz; last done end;
          apply Nat2Z.inj in Hsz;
          try (cbv [Z.to_nat Pos.to_nat] in Hsz;
               simpl in Hsz;
               (* Substitute only if we have a literal nat. *)
               match goal with Hsz : S _ = _ |- _ => subst sz end));
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "or" Hf "not fresh"
        |simpl; try wp_value_head]]
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc K _ _ _ _ H Hf))
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [try fast_done
    |tc_solve
    |let sz := fresh "sz" in let Hsz := fresh "Hsz" in
     first [intros l sz Hsz | fail 1 "wp_alloc:" l "not fresh"];
     (* If Hsz is "constant Z = nat", change that to an equation on nat and
        potentially substitute away the sz. *)
     try (match goal with Hsz : ?x = _ |- _ => rewrite <-(Z2Nat.id x) in Hsz; last done end;
          apply Nat2Z.inj in Hsz;
          try (cbv [Z.to_nat Pos.to_nat] in Hsz;
               simpl in Hsz;
               (* Substitute only if we have a literal nat. *)
               match goal with Hsz : S _ = _ |- _ => subst sz end));
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "or" Hf "not fresh"
        |simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in let Hf := iFresh in wp_alloc l as H Hf.

Tactic Notation "wp_free" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_free K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [try fast_done
    |let l := match goal with |- _ = Some (_, (?l ↦∗ _)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find" l "↦∗ ?"
    |pm_reflexivity
    |let l := match goal with |- _ = Some (_, († ?l … _)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find †" l "… ?"
    |pm_reflexivity
    |try fast_done
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [try fast_done
    |tc_solve
    |let l := match goal with |- _ = Some (_, (?l ↦∗ _)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find" l "↦∗ ?"
    |pm_reflexivity
    |let l := match goal with |- _ = Some (_, († ?l … _)%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find †" l "… ?"
    |pm_reflexivity
    |try fast_done
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_read" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_read K))
      |fail 1 "wp_read: cannot find 'Read' in" e];
    [(right; fast_done) || (left; fast_done) ||
     fail "wp_read: order is neither Na2Ord nor ScOrd"
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_read: cannot find" l "↦ ?"
    |simpl; try wp_value_head]
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read K))
      |fail 1 "wp_read: cannot find 'Read' in" e];
    [(right; fast_done) || (left; fast_done) ||
     fail "wp_read: order is neither Na2Ord nor ScOrd"
    |tc_solve
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_read: cannot find" l "↦ ?"
    |simpl; try wp_value_head]
  | _ => fail "wp_read: not a 'wp'"
  end.

Tactic Notation "wp_write" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_write K); [tc_solve|..])
      |fail 1 "wp_write: cannot find 'Write' in" e];
    [(right; fast_done) || (left; fast_done) ||
     fail "wp_write: order is neither Na2Ord nor ScOrd"
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_write: cannot find" l "↦ ?"
    |pm_reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | |- envs_entails _ (wpw ?W ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_write K); [tc_solve|..])
      |fail 1 "wp_write: cannot find 'Write' in" e];
    [(right; fast_done) || (left; fast_done) ||
     fail "wp_write: order is neither Na2Ord nor ScOrd"
    |tc_solve
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_write: cannot find" l "↦ ?"
    |pm_reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | _ => fail "wp_write: not a 'wp'"
  end.
