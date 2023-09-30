(** * Borrowing machinery *)

From nola Require Export prelude.
From nola.iris Require Export lft upd.
From iris.algebra Require Import excl agree gmap auth.
From iris.bi Require Import fractional.
From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.

(** ** Ghost state *)

(** ID for a borrower/lender *)
Local Definition bor_id := positive.
Local Definition lend_id := positive.
Implicit Type (j : bor_id) (i : lend_id).

(** State of a borrower *)
Local Definition bor_st PROP : Type :=
  PROP * option Qp (* Deposited fraction *).
(** State of the borrowers *)
Local Definition bor_stm PROP : Type := gmap bor_id (bor_st PROP).
(** Core state of a lender *)
Local Definition lend_cst PROP : Type :=
  PROP * bool (* Whether lending or not *).
(** State of a lender *)
Local Definition lend_st PROP : Type := lft * lend_cst PROP * bor_stm PROP.
(** State of the lenders *)
Local Definition lend_stm PROP : Type := gmap lend_id (lend_st PROP).

Implicit Type (α : lft) (b : option Qp) (l : bool).

(** Algebra for a borrower *)
Local Definition borR PROP := exclR (leibnizO (bor_st PROP)).

(** Algebra for a lender *)
Local Definition lendR PROP := prodR
  (prodR (agreeR (leibnizO lft)) (optionR (exclR (leibnizO (lend_cst PROP)))))
  (gmapR bor_id (borR PROP)).

(** Algebra for the borrowing machinery *)
Definition borrowR PROP := authR (gmapR lend_id (lendR PROP)).

(** Ghost state for the borrowing machinery *)
Class borrowGS PROP Σ := BorrowGS {
  borrowGS_borrow :: inG Σ (borrowR PROP);
  borrow_name : gname;
}.
Local Existing Instance borrowGS_borrow.
Class borrowGpreS PROP Σ := BorrowGpreS {
  borrowGpreS_borrow :: inG Σ (borrowR PROP);
}.
Definition borrowΣ PROP : gFunctors := #[GFunctor (borrowR PROP)].
#[export] Instance subG_borrow `{!subG (borrowΣ PROP) Σ} : borrowGpreS PROP Σ.
Proof. solve_inG. Qed.

(** ** Tokens *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (P Q : PROP)
    (B : bor_st PROP) (L : lend_st PROP) (Lm : lend_stm PROP).

  (** Borrower token *)
  Local Definition bor_ijtok i j α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, None, {[j := Excl B]})]}).
  Definition bor_tok α P : iProp Σ := ∃ i j, bor_ijtok i j α (P, None).
  Definition bor_otok `{!lftG Σ} α P q : iProp Σ :=
    (q/2).[α] ∗ ∃ i j, bor_ijtok i j α (P, Some (q/2)%Qp).

  (** Lender token *)
  Local Definition lend_itok i α P : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, Excl' (P, true), ε)]}).
  Definition lend_tok α P : iProp Σ := ∃ i, lend_itok i α P.

  (** Borrower and lender tokens are timeless *)
  Fact bor_tok_timeless {α P} : Timeless (bor_tok α P).
  Proof. apply _. Qed.
  Fact bor_otok_timeless `{!lftG Σ} {α P q} : Timeless (bor_otok α P q).
  Proof. apply _. Qed.
  Fact lend_tok_timeless {α P} : Timeless (lend_tok α P).
  Proof. apply _. Qed.

  (** Token for [lend_stm] *)
  Local Definition lend_st_to_lendR L : lendR PROP :=
    (to_agree L.1.1, Excl' L.1.2, (Excl : bor_st _ → _) <$> L.2).
  Local Definition lend_stm_tok Lm : iProp Σ :=
    own borrow_name (● (lend_st_to_lendR <$> Lm : gmapR _ _)).

  (** Create [bor_ijtok] and [lend_itok] w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_create {Lm α P} :
    lend_stm_tok Lm -∗ |==> ∃ i j,
      lend_stm_tok (<[i := (α, (P, true), {[j := (P, None)]})]> Lm) ∗
      bor_ijtok i j α (P, None) ∗ lend_itok i α P.
  Proof.
    iIntros "●". iExists (fresh (dom Lm)), 1%positive.
    iMod (own_update with "●") as "[$[$$]]"; [|done].
    rewrite -auth_frag_op singleton_op fmap_insert. apply auth_update_alloc.
    have <-: lend_st_to_lendR (α, (P, true), {[1%positive := (P, None)]}) ≡
      ((to_agree α, None, {[1%positive := Excl (P, None)]}) : lendR _) ⋅
        (to_agree α, Excl' (P, true), ε).
    { split; [split|]=>/=; by [rewrite agree_idemp|]. }
    apply alloc_singleton_local_update.
    - rewrite lookup_fmap. apply fmap_None, not_elem_of_dom_1, is_fresh.
    - split; [split|]=>/=; by [|rewrite map_fmap_singleton singleton_valid].
  Qed.

  (** Agreement between [lend_stm_tok] and [bor_ijtok] *)
  Local Lemma lend_stm_bor_agree {Lm i j α B} :
    lend_stm_tok Lm -∗ bor_ijtok i j α B -∗
      ⌜∃ C Bm, Lm !! i = Some (α, C, Bm) ∧ Bm !! j = Some B⌝.
  Proof.
    iIntros "● B". iDestruct (own_valid_2 with "● B") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[
      /Some_equiv_eq[?[/lookup_fmap_Some[[[? C]Bm][<-+]]<-]]
      /Some_included_total/prod_included[/prod_included/=
        [/to_agree_included/leibniz_equiv_iff ? _]incl]]]_]=> ?.
    apply singleton_included_exclusive_l in incl; [|apply _| ]; last first.
    { move=> j'. rewrite lookup_fmap. by case: (Bm !! j'). }
    move: incl. rewrite lookup_fmap leibniz_equiv_iff fmap_Some.
    move=> [?[?[?]]]. subst. by eexists _, _.
  Qed.
  (** Update the borrower state w.r.t. [lend_stm_tok] and [bor_ijtok] *)
  Local Lemma lend_stm_bor_stupd {Lm i j α C Bm B B'} :
    Lm !! i = Some (α, C, Bm) → Bm !! j = Some B →
    lend_stm_tok Lm -∗ bor_ijtok i j α B ==∗
      lend_stm_tok (<[i := (α, C, <[j := B']> Bm)]> Lm) ∗ bor_ijtok i j α B'.
  Proof.
    move=> ??. iIntros "● B". iMod (own_update_2 with "● B") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_insert. apply: singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. } by apply exclusive_local_update.
  Qed.

  (** Agreement between [lend_stm_tok] and [lend_itok] *)
  Local Lemma lend_stm_lend_agree {Lm i α P} :
    lend_stm_tok Lm -∗ lend_itok i α P -∗
      ⌜∃ Bm, Lm !! i = Some (α, (P, true), Bm)⌝.
  Proof.
    iIntros "● l". iDestruct (own_valid_2 with "● l") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[
      /Some_equiv_eq[?[/lookup_fmap_Some[[[??]Bm][<-?]]<-]]
      /Some_included_total/prod_included[/prod_included/=[
        /to_agree_included/leibniz_equiv_iff? /Excl_included/leibniz_equiv_iff?]
        _]]]_].
    subst. by eexists _.
  Qed.
  (** Extend a lender w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_lend_extend {Lm i α P Bm Q} :
    Lm !! i = Some (α, (P, true), Bm) →
    lend_stm_tok Lm -∗ lend_itok i α P ==∗
      lend_stm_tok (<[i := (α, (Q, true), Bm)]> Lm) ∗ lend_itok i α Q.
  Proof.
    move=> ?. iIntros "● l". iMod (own_update_2 with "● l") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    apply: option_local_update. by apply exclusive_local_update.
  Qed.
  (** Retrieve for a lender w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_lend_retrieve {Lm i α P Bm} :
    Lm !! i = Some (α,(P,true),Bm) →
    lend_stm_tok Lm -∗ lend_itok i α P ==∗
      lend_stm_tok (<[i := (α, (P, false), Bm)]> Lm).
  Proof.
    move=> ?. iIntros "● l". iMod (own_update_2 with "● l") as "[$_]"; [|done].
    apply auth_update. rewrite fmap_insert.
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    apply: option_local_update. by apply exclusive_local_update.
  Qed.
End borrow.

(** ** World satisfactions *)

Section borrow.
  Context `{!lftG Σ, !borrowGS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type (E : coPset) (W : iProp Σ) (intp : PROP → iProp Σ)
    (P Q : PROP) (B : bor_st PROP) (Bm : bor_stm PROP).

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat intp α B : iProp Σ :=
    match B.2 with None => intp B.1 | Some q => q.[α] end.

  (** World satisfaction for a lender *)
  Local Definition lend_wsat' E W intp α P Bm : iProp Σ :=
    ([∗ map] _ ↦ B ∈ Bm, bor_wsat intp α B) ∗
    (([∗ map] _ ↦ B ∈ Bm, intp B.1) =[W]{E}=∗ intp P).
  Local Definition lend_wsat E W intp α P l Bm : iProp Σ :=
    if l then lend_wsat' E W intp α P Bm else [†α]%I.

  (** World satisfaction for the borrowing machinery *)
  Local Definition borrow_wsat_def E W intp : iProp Σ :=
    ∃ Lm, lend_stm_tok Lm ∗
      [∗ map] _ ↦ L ∈ Lm, lend_wsat E W intp L.1.1 L.1.2.1 L.1.2.2 L.2.
  Local Definition borrow_wsat_aux : seal borrow_wsat_def.
  Proof. by eexists. Qed.
  Definition borrow_wsat := borrow_wsat_aux.(unseal).
  Local Lemma borrow_wsat_unseal : borrow_wsat = borrow_wsat_def.
  Proof. exact: borrow_wsat_aux.(seal_eq). Qed.

  (** Create a borrower and a lender *)
  Lemma bor_lend_create {E W intp α P} :
    intp P =[borrow_wsat E W intp]=∗ bor_tok α P ∗ lend_tok α P.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "P [%Lm[● Lm]]".
    iMod (lend_stm_create with "●") as (??) "[● [b l]]"; [done..|]. iModIntro.
    iSplitR "b l"; [|iSplitL "b"; by [iExists _, _|iExists _]]. iExists _.
    iFrame "●". iApply (big_sepM_insert_2 with "[P] Lm")=>/=.
    iSplitL; rewrite big_sepM_singleton; by [|iIntros].
  Qed.

  (** [lend_wsat] with a lifetime token *)
  Local Lemma lend_wsat_tok {E W intp q α P l Bm} :
    q.[α] -∗ lend_wsat E W intp α P l Bm -∗ ⌜l = true⌝.
  Proof.
    iIntros "α †". case: l; [done|]=>/=.
    iDestruct (lft_tok_dead with "α †") as "[]".
  Qed.
  (** Update the borrower state *)
  Local Lemma bor_stupd {E W intp q i j α P b b'} :
    q.[α] -∗ bor_ijtok i j α (P, b) -∗ bor_wsat intp α (P, b')
      =[borrow_wsat E W intp]=∗
      q.[α] ∗ bor_ijtok i j α (P, b') ∗ bor_wsat intp α (P, b).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "α b B' [%Lm[● Lm]]".
    iDestruct (lend_stm_bor_agree with "● b") as %[[Q l][Bm[??]]].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat_tok with "α L") as %->. iFrame "α".
    iDestruct "L" as "[Bm →Q]".
    iDestruct (big_sepM_insert_acc with "Bm") as "[$ →Bm]"; [done|].
    iMod (lend_stm_bor_stupd with "● b") as "[● $]"; [done..|]. iModIntro.
    iExists _. iFrame "●". iApply "→Lm"=>/=. iSplitR "→Q"; [by iApply "→Bm"|].
    iStopProof. f_equiv=>/=. apply bi.equiv_entails_1_1.
    by apply: big_sepM_insert_override.
  Qed.
  (** Open the borrower *)
  Lemma bor_open {E W intp q α P} :
    bor_tok α P -∗ q.[α] =[borrow_wsat E W intp]=∗ intp P ∗ bor_otok α P q.
  Proof.
    iIntros "[%i[%j b]] [α α']".
    iMod (bor_stupd (b':=Some _) with "α b α'") as "[$[b $]]". iModIntro.
    by iExists _, _.
  Qed.
  (** Close the borrower *)
  Lemma bor_close {E W intp q α P} :
    bor_otok α P q -∗ intp P =[borrow_wsat E W intp]=∗ q.[α] ∗ bor_tok α P.
  Proof.
    iIntros "[α[%i[%j b]]] P".
    iMod (bor_stupd (b':=None) with "α b P") as "[$[b $]]". iModIntro.
    by iExists _, _.
  Qed.

  (** Extend the lender token *)
  Lemma lend_extend {E W intp α P Q} :
    lend_tok α P -∗ (intp P =[W]{E}=∗ intp Q) =[borrow_wsat E W intp]=∗
      lend_tok α Q.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[%i l] PQ [%Lm[● Lm]]".
    iDestruct (lend_stm_lend_agree with "● l") as %[Bm ?].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iMod (lend_stm_lend_extend with "● l") as "[● l]"; [done|]. iModIntro.
    iSplitR "l"; [|by iExists _]. iExists _. iFrame "●". iApply "→Lm"=>/=.
    iDestruct "L" as "[$ →P]". iIntros "Bm". iMod ("→P" with "Bm") as "P".
    by iApply "PQ".
  Qed.

  (** [bor_wsat] with the dead lifetime token *)
  Local Lemma bor_wsat_dead {intp α B} : [†α] -∗ bor_wsat intp α B -∗ intp B.1.
  Proof.
    case B=> [P[q|]]=>/=; [|by iIntros]. iIntros "† q".
    iDestruct (lft_tok_dead with "q †") as "[]".
  Qed.
  (** [lend_wsat'] with the dead lifetime token *)
  Local Lemma lend_wsat'_dead {E W intp α P Bm} :
    [†α] -∗ lend_wsat' E W intp α P Bm =[W]{E}=∗ intp P.
  Proof.
    iIntros "#† [Bm →P]". iApply "→P". iApply (big_sepM_impl with "Bm").
    iIntros "!>" (?? _). by iApply bor_wsat_dead.
  Qed.
  (** Retrieve from the lender token *)
  Lemma lend_retrieve {E W intp α P} :
    [†α] -∗ lend_tok α P =[borrow_wsat E W intp]=∗ |=[W]{E}=> intp P.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "#† [%i l] [%Lm[● Lm]]".
    iDestruct (lend_stm_lend_agree with "● l") as %[Bm ?].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat'_dead with "† L") as "$". iExists _.
    iMod (lend_stm_lend_retrieve with "● l") as "$"; by [|iApply "→Lm"].
  Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc `{!lftG Σ, !borrowGpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : borrowGS PROP Σ, ∀ E W intp, borrow_wsat E W intp.
Proof.
  iMod (own_alloc (● ∅)) as (γ) "●"; [by apply auth_auth_valid|]. iModIntro.
  iExists (BorrowGS _ _ _ γ). iIntros (E W intp). rewrite borrow_wsat_unseal.
  iExists ∅. by iFrame "●".
Qed.
