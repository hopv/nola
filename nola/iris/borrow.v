(** * Borrowing machinery *)

From nola.util Require Export prod.
From nola.iris Require Import gmap sinv.
From nola.iris Require Export lft upd.
From nola.util Require Import prod.
From iris.algebra Require Import excl agree gmap auth.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.

(** ** Ghost state *)

Implicit Type PROP : Type.
Implicit Type (α : lft) (q : Qp).

(** ID for a borrower/deposit/lender *)
Local Definition bor_id := positive.
Local Definition depo_id := positive.
Local Definition lend_id := positive.
Implicit Type (i : depo_id) (j : bor_id) (k : lend_id).

(** Mode of a borrower *)
Variant bor_mode : Set :=
| #[local] Clsd (* Closed *)
| #[local] Open (q : Qp) (* Open with a fraction *)
| #[local] Rebor (α : lft) (* Reborrowed *).
Implicit Type b : bor_mode.
(** State of a borrower *)
Local Definition bor_st PROP : Type := PROP *' bor_mode.
(** State of the borrowers *)
Local Notation bor_stm PROP := (gmap bor_id (bor_st PROP)).

(** State of the lenders *)
Local Notation lendm PROP := (gmap lend_id PROP).

(** Kind of a deposit *)
Local Definition depo_kind : Type := nat (* depth *) *' lft.
Implicit Type e : depo_kind.
(** State of a deposit *)
Local Definition depo_st PROP : Type :=
  depo_kind *' bor_stm PROP *' lendm PROP.
(** State of the deposits *)
Local Notation depo_stm PROP := (gmap depo_id (depo_st PROP)).

(** Algebra for a borrower *)
Local Definition borR PROP := exclR (leibnizO (bor_st PROP)).
(** Algebra for a lender *)
Local Definition lendR PROP := exclR (leibnizO PROP).
(** Algebra for a deposit *)
Local Definition depoR PROP := prodR (prodR
  (agreeR (leibnizO depo_kind))
  (gmapR bor_id (borR PROP)))
  (gmapR lend_id (lendR PROP)).

(** Algebra for the borrowing machinery *)
Local Definition borrowR_def PROP := authR (gmapR depo_id (depoR PROP)).
Local Lemma borrowR_aux : seal borrowR_def. Proof. by eexists. Qed.
Definition borrowR := borrowR_aux.(unseal).
Local Lemma borrowR_unseal : borrowR = borrowR_def.
Proof. exact: seal_eq. Qed.

(** Ghost state for the borrowing machinery *)
Class borrowGS PROP Σ := BorrowGS {
  borrowGS_lft :: lftG Σ;
  borrowGS_borrow : inG Σ (borrowR PROP);
  borrow_name : gname;
}.
Local Existing Instance borrowGS_borrow.
Local Instance inG_borrow_def `{!inG Σ (borrowR PROP)} :
  inG Σ (borrowR_def PROP).
Proof. rewrite -borrowR_unseal. exact _. Qed.
Class borrowGpreS PROP Σ := BorrowGpreS {
  borrowGpreS_lft :: lftG Σ;
  borrowGpreS_borrow : inG Σ (borrowR PROP);
}.
Local Existing Instance borrowGpreS_borrow.
Definition borrowΣ PROP : gFunctors :=
  #[GFunctor lftR; GFunctor (borrowR PROP)].
#[export] Instance subG_borrow `{!subG (borrowΣ PROP) Σ} : borrowGpreS PROP Σ.
Proof. solve_inG. Qed.

(** ** Tokens *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (P Q : PROP) (Pl Ql : list PROP)
    (D : depo_st PROP) (Dm : depo_stm PROP)
    (B : bor_st PROP) (Bm : bor_stm PROP) (Pm : lendm PROP).

  (** General borrower token *)
  Local Definition bor_itok i j d α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree (d, α)', {[j := Excl B]}, ε)]}).

  (** Closed borrower token

    It may be a dead lifetime token or a closed borrower

    Slightly stronger than [bor_tok] *)
  Local Definition bor_ctok_def α P : iProp Σ :=
    [†α] ∨ ∃ i j d α', α ⊑□ α' ∗ bor_itok i j d α' (P, Clsd)'.
  Local Lemma bor_ctok_aux : seal bor_ctok_def. Proof. by eexists. Qed.
  Definition bor_ctok := bor_ctok_aux.(unseal).
  Local Lemma bor_ctok_unseal : bor_ctok = bor_ctok_def.
  Proof. exact: seal_eq. Qed.

  (** Borrower token

    It may be [bor_tok] or a retrieving reborrower *)
  Local Definition bor_tok_def α P : iProp Σ :=
    bor_ctok α P ∨ ∃ i j d α' β,
      α ⊑□ α' ∗ [†β] ∗ bor_itok i j d α' (P, Rebor β)'.
  Local Lemma bor_tok_aux : seal bor_tok_def. Proof. by eexists. Qed.
  Definition bor_tok := bor_tok_aux.(unseal).
  Local Lemma bor_tok_unseal : bor_tok = bor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open borrower token

    It keeps a lifetime token [(r/2).[α']] at hand *)
  Local Definition bor_otok_def α P q : iProp Σ :=
    ∃ α' r i j d, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗
      (r/2).[α'] ∗ bor_itok i j d α' (P, Open (r/2))'.
  Local Lemma bor_otok_aux : seal bor_otok_def. Proof. by eexists. Qed.
  Definition bor_otok := bor_otok_aux.(unseal).
  Local Lemma bor_otok_unseal : bor_otok = bor_otok_def.
  Proof. exact: seal_eq. Qed.

  (** Lender token *)
  Local Definition lend_itok i k d α P : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree (d, α)', ε, {[k := Excl P]})]}).
  Local Definition lend_dtok d α P : iProp Σ :=
    ∃ i k, lend_itok i k d α P.
  Local Definition lend_tok_def α P : iProp Σ :=
    ∃ α', α' ⊑□ α ∗ ∃ d, lend_dtok d α' P.
  Local Lemma lend_tok_aux : seal lend_tok_def. Proof. by eexists. Qed.
  Definition lend_tok := lend_tok_aux.(unseal).
  Local Lemma lend_tok_unseal : lend_tok = lend_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Borrower and lender tokens are timeless *)
  #[export] Instance bor_ctok_timeless {α P} : Timeless (bor_ctok α P).
  Proof. rewrite bor_ctok_unseal. apply _. Qed.
  #[export] Instance bor_tok_timeless {α P} : Timeless (bor_tok α P).
  Proof. rewrite bor_tok_unseal. apply _. Qed.
  #[export] Instance bor_otok_timeless {α P q} : Timeless (bor_otok α P q).
  Proof. rewrite bor_otok_unseal. apply _. Qed.
  #[export] Instance lend_tok_timeless {α P} : Timeless (lend_tok α P).
  Proof. rewrite lend_tok_unseal. apply _. Qed.

  (** Turn [bor_ctok] to [bor_tok] *)
  Lemma bor_ctok_tok {α P} : bor_ctok α P ⊢ bor_tok α P.
  Proof. rewrite bor_tok_unseal. iIntros. by iLeft. Qed.

  (** Fake a borrower token from the dead lifetime token *)
  Lemma bor_ctok_fake {α P} : [†α] ⊢ bor_ctok α P.
  Proof. rewrite bor_ctok_unseal. iIntros. by iLeft. Qed.
  Lemma bor_tok_fake {α P} : [†α] ⊢ bor_tok α P.
  Proof. by rewrite bor_ctok_fake bor_ctok_tok. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma bor_ctok_lft {α α' P} : α' ⊑□ α -∗ bor_ctok α P -∗ bor_ctok α' P.
  Proof.
    rewrite bor_ctok_unseal. iIntros "#? [?|c]".
    { iLeft. by iApply lft_sincl_dead. }
    iDestruct "c" as (????) "[#? c]". iRight. iExists _, _, _, _. iFrame "c".
    by iApply lft_sincl_trans.
  Qed.
  #[export] Instance bor_ctok_mono : Proper (flip (⊑) ==> (=) ==> (⊢)) bor_ctok.
  Proof. move=>/= ?????<-. iApply bor_ctok_lft. by iApply lft_incl_sincl. Qed.
  #[export] Instance bor_ctok_mono' :
    Proper ((⊑) ==> (=) ==> flip (⊢)) bor_ctok.
  Proof. solve_proper. Qed.
  Lemma bor_tok_lft {α α' P} : α' ⊑□ α -∗ bor_tok α P -∗ bor_tok α' P.
  Proof.
    rewrite bor_tok_unseal. iIntros "#⊑ [c|r]".
    { iLeft. by iApply (bor_ctok_lft with "⊑ c"). }
    iDestruct "r" as (?????) "[#? r]". iRight. iExists _, _, _, _, _.
    iFrame "r". by iApply lft_sincl_trans.
  Qed.
  #[export] Instance bor_tok_mono : Proper (flip (⊑) ==> (=) ==> (⊢)) bor_tok.
  Proof. move=>/= ?????<-. iApply bor_tok_lft. by iApply lft_incl_sincl. Qed.
  #[export] Instance bor_tok_mono' : Proper ((⊑) ==> (=) ==> flip (⊢)) bor_tok.
  Proof. solve_proper. Qed.
  Lemma bor_otok_lft {α α' P q r} :
    α' ⊑□ α -∗ (q.[α] -∗ r.[α']) -∗ bor_otok α P q -∗ bor_otok α' P r.
  Proof.
    rewrite bor_otok_unseal. iIntros "#? →α'".
    iDestruct 1 as (α'' ????) "[#?[→α o]]". iExists _, _, _, _, _. iFrame "o".
    iSplit; [by iApply lft_sincl_trans|]. iIntros "α''". iApply "→α'".
    by iApply "→α".
  Qed.
  Lemma lend_tok_lft {α α' P} : α ⊑□ α' -∗ lend_tok α P -∗ lend_tok α' P.
  Proof.
    rewrite lend_tok_unseal. iIntros "#? [%α''[#? l]]". iExists _. iFrame "l".
    by iApply lft_sincl_trans.
  Qed.
  #[export] Instance lend_tok_mono : Proper ((⊑) ==> (=) ==> (⊢)) lend_tok.
  Proof. move=>/= ?????<-. iApply lend_tok_lft. by iApply lft_incl_sincl. Qed.
  #[export] Instance lend_tok_mono' :
    Proper (flip (⊑) ==> (=) ==> flip (⊢)) lend_tok.
  Proof. solve_proper. Qed.

  (** Token for [depo_stm] *)
  Local Definition depo_st_R D : depoR PROP :=
    let '(e, Bm, Pm)' := D in (to_agree e, Excl <$> Bm, Excl <$> Pm).
  Arguments depo_st_R _ /.
  Local Definition depo_stm_tok Dm : iProp Σ :=
    own borrow_name (● (depo_st_R <$> Dm : gmapR _ _)).

  (** Lemma for [to_bor_itoks] *)
  Local Lemma bor_insert_op {i j e B Bm} :
    Bm !! j = None →
    (◯ {[i := (to_agree e, Excl <$> <[j:=B]> Bm, ε)]} : borrowR_def _) ≡
      ◯ {[i := (to_agree e, {[j:=Excl B]}, ε)]} ⋅
      ◯ {[i := (to_agree e, Excl <$> Bm, ε)]}.
  Proof.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp| |done].
    rewrite (insert_singleton_op _ _ (_ : borR _)); [done|].
    rewrite lookup_fmap. by rewrite eq.
  Qed.
  (** Get [bor_itok]s out of [own] *)
  Local Lemma to_bor_itoks {i d α Bm} :
    own borrow_name (◯ {[i := (to_agree (d, α)', Excl <$> Bm, ε)]}) ⊢
      [∗ map] j ↦ B ∈ Bm, bor_itok i j d α B.
  Proof.
    induction Bm as [|j B Bm ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH bor_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Lemma for [to_lend_itoks] *)
  Local Lemma lend_insert_op {i k e P Pm} :
    Pm !! k = None →
    (◯ {[i := (to_agree e, ε, Excl <$> <[k:=P]> Pm)]} : borrowR_def _) ≡
      ◯ {[i := (to_agree e, ε, {[k:=Excl P]})]} ⋅
      ◯ {[i := (to_agree e, ε, Excl <$> Pm)]}.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp|done|].
    rewrite (insert_singleton_op _ _ (_ : exclR (leibnizO _))); [done|].
    rewrite lookup_fmap. by rewrite eq.
  Qed.
  (** Get [lend_itok]s out of [own] *)
  Local Lemma to_lend_itoks {i d α Pm} :
    own borrow_name (◯ {[i := (to_agree (d, α)', ε, Excl <$> Pm)]}) ⊢
      [∗ map] k ↦ P ∈ Pm, lend_itok i k d α P.
  Proof.
    induction Pm as [|k P Pm ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH lend_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Create [bor_itok]s and [lend_itok]s w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_bor_lend_new {Dm} d α Pl Ql :
    depo_stm_tok Dm -∗ |==> ∃ i,
      let Bm := map_by _ (fmap (M:=list) (λ P, (P, Clsd)') Pl) in
      let Qm := map_by _ Ql in
      depo_stm_tok (<[i := ((d, α)', Bm, Qm)']> Dm) ∗
      ([∗ map] j ↦ B ∈ Bm, bor_itok i j d α B) ∗
      [∗ map] k ↦ Q ∈ Qm, lend_itok i k d α Q.
  Proof.
    iIntros "●". iExists (fresh (dom Dm)).
    iMod (own_update with "●") as "[$[c l]]"; last first.
    { iModIntro. iDestruct (to_bor_itoks (d:=d) with "c") as "$".
      iApply (to_lend_itoks with "l"). }
    rewrite -auth_frag_op singleton_op fmap_insert.
    have <- : ∀ x y, ((to_agree (d, α)', x, y) : depoR _) ≡
      ((to_agree (d, α)', x, ε) : depoR _) ⋅ (to_agree (d, α)', ε, y).
    { split; [split|]=>/=; by
        [rewrite agree_idemp|rewrite left_id|rewrite right_id]. }
    apply auth_update_alloc, alloc_singleton_local_update.
    - rewrite lookup_fmap. apply fmap_None, not_elem_of_dom_1, is_fresh.
    - split; [split|]=>/=; [done|by apply: gmap_fmap_valid..].
  Qed.

  (** Agreement between [depo_stm_tok] and [lend_itok] *)
  Local Lemma depo_stm_lend_agree {Dm i k d α P} :
    depo_stm_tok Dm -∗ lend_itok i k d α P -∗
      ⌜∃ Bm Pm, Dm !! i = Some ((d, α)', Bm, Pm)' ∧ Pm !! k = Some P⌝.
  Proof.
    iIntros "● l". iDestruct (own_valid_2 with "● l") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[++]]_].
    move=> /Some_equiv_eq[[[??]?][+<-]].
    move=> /lookup_fmap_Some[[?[??]][[<-<-<-]?]].
    move=> /Some_included_total/prod_included[/prod_included/=[+_]inc].
    move=> /to_agree_included/leibniz_equiv_iff ?.
    apply singleton_included_exclusive_l in inc;
      [|exact _|by apply: gmap_fmap_valid]. move: inc.
    rewrite lookup_fmap leibniz_equiv_iff fmap_Some. move=> [?[?[?]]]. subst.
    by eexists _, _.
  Qed.
  (** Delete a lender w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_lend_delete {Dm i k d α Bm Pm P} :
    Dm !! i = Some ((d, α)', Bm, Pm)' → Pm !! k = Some P →
    depo_stm_tok Dm -∗ lend_itok i k d α P ==∗
      depo_stm_tok (<[i := ((d, α)', Bm, delete k Pm)']> Dm).
  Proof.
    move=> ??. iIntros "● l". iMod (own_update_2 with "● l") as "[$_]"; [|done].
    apply auth_update. rewrite fmap_insert.
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_delete. apply: delete_local_update; last first.
    { by rewrite lookup_singleton. } exact _.
  Qed.
  (** Add lenders w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_lend_add {Dm i d α Bm Pm} Ql :
    Dm !! i = Some ((d, α)', Bm, Pm)' →
    depo_stm_tok Dm ==∗
      depo_stm_tok (<[i := ((d, α)', Bm, map_with Pm Ql)']> Dm) ∗
      [∗ map] k ↦ Q ∈ map_without Pm Ql, lend_itok i k d α Q.
  Proof.
    move=> eq. iIntros "●". iMod (own_update with "●") as "[$ ?]"; last first.
    { iModIntro. by iApply to_lend_itoks. }
    rewrite fmap_insert. apply auth_update_alloc, gmap_local_update.
    move=> i'. case: (decide (i = i'))=> [<-|?]; last first.
    { rewrite lookup_insert_ne; [|done]. by rewrite lookup_singleton_ne. }
    rewrite lookup_empty lookup_fmap eq !lookup_insert /=.
    apply local_update_unital_discrete=> ?[/=??]. rewrite left_id=> <-. split.
    { split; [done|]. by apply: gmap_fmap_valid. }
    rewrite -Some_op. f_equiv.
    split; [split|]=>/=; [by rewrite agree_idemp|by rewrite left_id|].
    rewrite gmap_op_disj; [|by apply map_disjoint_fmap, map_without_disj].
    by rewrite -map_fmap_union -map_with_without.
  Qed.

  (** Agreement between [depo_stm_tok] and [bor_itok] *)
  Local Lemma depo_stm_bor_agree {Dm i j d α B} :
    depo_stm_tok Dm -∗ bor_itok i j d α B -∗
      ⌜∃ Bm Pm, Dm !! i = Some ((d, α)', Bm, Pm)' ∧ Bm !! j = Some B⌝.
  Proof.
    iIntros "● B". iDestruct (own_valid_2 with "● B") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[++]]_].
    move=> /Some_equiv_eq[[[??]?][+<-]].
    move=> /lookup_fmap_Some[[?[??]][[<-<-<-]?]].
    move=> /Some_included_total/prod_included[/prod_included/=[+ inc]_].
    move=> /to_agree_included/leibniz_equiv_iff ?.
    apply singleton_included_exclusive_l in inc;
      [|exact _|by apply: gmap_fmap_valid]. move: inc.
    rewrite lookup_fmap leibniz_equiv_iff fmap_Some. move=> [?[?[?]]]. subst.
    by eexists _, _.
  Qed.
  (** Update the borrower state w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_bor_stupd {Dm i j d α Bm Pm B B'} :
    Dm !! i = Some ((d, α)', Bm, Pm)' → Bm !! j = Some B →
    depo_stm_tok Dm -∗ bor_itok i j d α B ==∗
      depo_stm_tok (<[i := ((d, α)', <[j := B']> Bm, Pm)']> Dm) ∗
      bor_itok i j d α B'.
  Proof.
    move=> ??. iIntros "● B". iMod (own_update_2 with "● B") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    rewrite fmap_insert. apply: singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. } by apply exclusive_local_update.
  Qed.
End borrow.

(** ** World satisfactions *)

Section borrow.
  Context `{!borrowGS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type (W : iProp Σ) (E : coPset) (intp : PROP -d> iProp Σ)
    (P Q : PROP) (D : depo_st PROP) (Dm : depo_stm PROP) (Bm : bor_stm PROP)
    (Pm : lendm PROP).

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat intp d α B : iProp Σ :=
    let '(Q, b)' := B in match b with
    | Clsd => intp Q | Open q => q.[α]
    | Rebor β => ∃ d', ⌜d < d'⌝ ∗ lend_dtok d' (α ⊓ β) Q
    end.

  (** World satisfaction for a deposit *)
  Local Definition depo_wsat_in W E intp d α Bm Pm : iProp Σ :=
    ([∗ map] B ∈ Bm, bor_wsat intp d α B) ∗
    ([†α] -∗ ([∗ map] '(Q, _)' ∈ Bm, intp Q) =[W]{E}=∗ [∗ map] P ∈ Pm, intp P).
  Local Definition depo_wsat_dead W E intp α Pm : iProp Σ :=
    [†α] ∗ |=[W]{E}=> [∗ map] P ∈ Pm, intp P.
  Local Definition depo_wsat W E intp d α Bm Pm : iProp Σ :=
    depo_wsat_in W E intp d α Bm Pm ∨ depo_wsat_dead W E intp α Pm.

  (** World satisfaction for the borrowing machinery *)
  Notation borrow_wsat' W E intp Dm :=
    ([∗ map] '((d, α)', Bm, Pm)' ∈ Dm, depo_wsat W E intp d α Bm Pm)%I.
  Local Definition borrow_wsat_def W E intp : iProp Σ :=
    ∃ Dm, depo_stm_tok Dm ∗ borrow_wsat' W E intp Dm.
  Local Definition borrow_wsat_aux : seal borrow_wsat_def.
  Proof. by eexists. Qed.
  Definition borrow_wsat := borrow_wsat_aux.(unseal).
  Local Lemma borrow_wsat_unseal : borrow_wsat = borrow_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [borrow_wsat] is non-expansive *)
  Local Instance bor_wsat_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) bor_wsat.
  Proof. solve_proper. Qed.
  Local Instance depo_wsat_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡) ==> (=) ==> (=) ==> (=) ==> (=) ==>
      (≡{n}≡)) depo_wsat.
  Proof.
    move=> ?????<-?????<-??<-??<-??<-. rewrite /depo_wsat.
    f_equiv; solve_proper.
  Qed.
  #[export] Instance borrow_wsat_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡) ==> (≡{n}≡)) borrow_wsat.
  Proof.
    rewrite borrow_wsat_unseal /borrow_wsat_def. move=> ?????<-???.
    do 6 f_equiv. by apply depo_wsat_ne.
  Qed.
  #[export] Instance borrow_wsat_proper :
    Proper ((≡) ==> (=) ==> (≡) ==> (≡)) borrow_wsat.
  Proof.
    move=> ?????<-???. apply equiv_dist=> ?. f_equiv; by apply equiv_dist.
  Qed.

  (** Create borrowers and lenders with a specific depth *)
  Local Lemma bor_lend_tok_new_list' {W E intp} d α Pl Ql :
    ([∗ list] P ∈ Pl, intp P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, intp P) =[W]{E}=∗ [∗ list] Q ∈ Ql, intp Q)
    =[borrow_wsat W E intp]=∗
      ([∗ list] P ∈ Pl, bor_ctok α P) ∗ [∗ list] Q ∈ Ql, lend_dtok d α Q.
  Proof.
    rewrite borrow_wsat_unseal bor_ctok_unseal. iIntros "Pl →Ql [%Dm[● Dm]]".
    iMod (depo_stm_bor_lend_new d α Pl Ql with "●") as (?) "[●[c l]]".
    iModIntro. rewrite !big_sepM_map_by' big_sepL_fmap.
    iSplitR "c l"; last first; [iSplitL "c"; iStopProof; do 3 f_equiv;
      iIntros "[% ?]"; [|by iExists _, _]|].
    { iRight. iExists _, _, _, _. iSplitR; by [iApply lft_sincl_refl|]. }
    iExists _. iFrame "●". iApply (big_sepM_insert_2 with "[Pl →Ql] Dm"). iLeft.
    iSplitL "Pl"; by rewrite !big_sepM_map_by big_sepL_fmap.
  Qed.
  (** Create borrowers and lenders *)
  Lemma bor_lend_tok_new_list {W E intp} α Pl Ql :
    ([∗ list] P ∈ Pl, intp P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, intp P) =[W]{E}=∗ [∗ list] Q ∈ Ql, intp Q)
    =[borrow_wsat W E intp]=∗
      ([∗ list] P ∈ Pl, bor_ctok α P) ∗ [∗ list] Q ∈ Ql, lend_tok α Q.
  Proof.
    iIntros "Pl →Ql". iMod (bor_lend_tok_new_list' 0 with "Pl →Ql") as "[$ ?]".
    iModIntro. iStopProof. do 3 f_equiv. iIntros "l". rewrite lend_tok_unseal.
    iExists _. iSplit; [by iApply lft_sincl_refl|]. by iExists _.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma bor_lend_tok_create {W E intp} α P :
    intp P =[borrow_wsat W E intp]=∗ bor_ctok α P ∗ lend_tok α P.
  Proof.
    iIntros "P". iMod (bor_lend_tok_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Extend a lender *)
  Lemma lend_tok_extend {W E intp α P} Ql :
    lend_tok α P -∗ (intp P =[W]{E}=∗ [∗ list] Q ∈ Ql, intp Q)
      =[borrow_wsat W E intp]=∗ [∗ list] Q ∈ Ql, lend_tok α Q.
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "[%α'[#?[%d[%i[%k l]]]]] PQ [%Dm[● Dm]]".
    iDestruct (depo_stm_lend_agree with "● l") as %[Bm[Pm[??]]].
    iMod (depo_stm_lend_delete with "● l") as "●"; [done..|].
    iMod (depo_stm_lend_add Ql with "●") as "[● ls]"; [apply lookup_insert|].
    iModIntro. iSplitR "ls"; last first.
    { rewrite big_sepM_map_without'. iApply (big_sepL_impl with "ls").
      iIntros "!> %% ⊑ [% ?]". iExists _. iSplit; [done|]. by iExists _, _, _. }
    iExists _. iFrame "●". rewrite insert_insert.
    iDestruct (big_sepM_insert_acc with "Dm") as "[D →Dm]"; [done|]=>/=.
    iApply "→Dm". iDestruct "D" as "[[Bm →Pm]|[† Pm]]".
    - iLeft. iFrame "Bm". iIntros "† Bm". iMod ("→Pm" with "† Bm") as "Pm".
      rewrite big_sepM_map_with.
      iDestruct (big_sepM_delete with "Pm") as "[? $]"; [done|]. by iApply "PQ".
    - iRight. iFrame "†". iMod "Pm". rewrite big_sepM_map_with.
      iDestruct (big_sepM_delete with "Pm") as "[P $]"; [done|]. by iApply "PQ".
  Qed.

  (** Filter [depo_stm] with a depth *)
  Local Notation dep_of D := D.1'.1'.
  Local Notation filter_ge d := (filter (λ iD, d ≤ dep_of iD.2)).
  Local Notation filter_lt d := (filter (λ iD, dep_of iD.2 < d)).
  Local Notation filter_eq d := (filter (λ iD, dep_of iD.2 = d)).
  (** [borrow_wsat'] with deposits under [d] and [α] retrieved *)
  Local Definition depo_wsat_ret W E intp d' α β Bm Pm : iProp Σ :=
    if decide (β ⊑ α) then depo_wsat_dead W E intp β Pm
    else depo_wsat W E intp d' β Bm Pm.
  Local Definition borrow_wsat_ret W E intp Dm d α : iProp Σ :=
    ∃ Dm', ⌜filter_lt d Dm' = filter_lt d Dm⌝ ∗ depo_stm_tok Dm' ∗
      [∗ map] '((d', β)', Bm, Pm)' ∈ filter_ge d Dm',
        depo_wsat_ret W E intp d' α β Bm Pm.

  (** Retrieve from [borrow_wsat_ret] using [lend_dtok] *)
  Local Lemma lend_dtok_ret_retrieve {W E intp Dm d d' α β P} : d ≤ d' → β ⊑ α →
    lend_dtok d' β P =[borrow_wsat_ret W E intp Dm d α ∗ W]{E}=∗ intp P.
  Proof.
    move=> ??. iIntros "[%[% l]] [[%Dm'[%[● Dm']]] W]".
    iDestruct (depo_stm_lend_agree with "● l") as %[Bm[Pm[eq ?]]].
    iDestruct (big_sepM_insert_acc with "Dm'") as "[D →Dm']".
    { rewrite map_filter_lookup_Some. split; [done|simpl; lia]. }
    rewrite /depo_wsat_ret decide_True; [|done]. iDestruct "D" as "[† Pm]".
    iMod ("Pm" with "W") as "[$ Pm]".
    iDestruct (big_sepM_delete with "Pm") as "[$ Pm]"; [done|]=>/=.
    iMod (depo_stm_lend_delete with "● l") as "●"; [done..|]. iModIntro.
    iExists _. iFrame "●". iSplit.
    { iPureIntro. rewrite map_filter_insert_False /=; [|lia].
      rewrite map_filter_delete_not; [done|]. rewrite eq. move=> ?[<-]/=. lia. }
    rewrite map_filter_insert_True; [|simpl; lia].
    iApply "→Dm'". rewrite decide_True; [|done]. by iFrame.
  Qed.

  (** Retrieve from [bor_wsat] *)
  Local Lemma bor_wsat_retrieve {W E intp Dm d α β P b} : β ⊑ α →
    [†β] -∗ bor_wsat intp d β (P, b)'
      =[borrow_wsat_ret W E intp Dm (S d) α ∗ W]{E}=∗ intp P.
  Proof.
    move=> ?. iIntros "† B". case b=> [|q|?]/=; [done|..].
    { iDestruct (lft_tok_dead with "B †") as "[]". }
    iDestruct "B" as (??) "l". iApply (lend_dtok_ret_retrieve with "l"); [lia|].
    etrans; [|done]. apply lft_incl_meet_l.
  Qed.
  (** Retrieve from [bor_wsat]s *)
  Local Lemma bor_wsats_retrieve {W E intp Dm d α β Bl} : β ⊑ α →
    [†β] -∗ ([∗ list] B ∈ Bl, bor_wsat intp d β B)
      =[borrow_wsat_ret W E intp Dm (S d) α ∗ W]{E}=∗
      [∗ list] '(P, _)' ∈ Bl, intp P.
  Proof.
    move=> ?. elim: Bl; [by iIntros|]=>/= B Bl IH. iIntros "#† [B Bl]".
    iMod (IH with "† Bl") as "$". by iApply bor_wsat_retrieve.
  Qed.
  (** Retrieve from [depo_wsat] *)
  Local Lemma depo_wsat_retrieve {W E intp Dm d α β Bm Pm} : β ⊑ α →
    [†β] -∗ depo_wsat W E intp d β Bm Pm
      =[borrow_wsat_ret W E intp Dm (S d) α ∗ W]{E}=∗
      depo_wsat_dead W E intp β Pm.
  Proof.
    move=> ?. iIntros "#† [[Bl →Pm]|?]"; [|done]. iFrame "†".
    iDestruct ("→Pm" with "†") as "→Pm". rewrite !big_sepM_map_to_list_snd.
    move: (map_to_list Bm).*2=> Bl.
    iMod (bor_wsats_retrieve with "† Bl") as "Bl"; [done..|].
    by iDestruct ("→Pm" with "Bl") as "$".
  Qed.
  (** Retrieve from [depo_wsat]s *)
  Local Lemma depo_wsats_retrieve {W E intp Dm d α Dl} :
    [†α] -∗ ([∗ list] '((d', β)', Bm, Pm)' ∈ Dl,
      if decide (d' = d) then depo_wsat W E intp d' β Bm Pm else emp)
      =[borrow_wsat_ret W E intp Dm (S d) α ∗ W]{E}=∗
      [∗ list] '((d', β)', Bm, Pm)' ∈ Dl,
        if decide (d' = d) then depo_wsat_ret W E intp d' α β Bm Pm else emp.
  Proof.
    elim: Dl; [by iIntros|]. move=> [[d' β][??]] Dl IH. iIntros "#† [D Dl]".
    iMod (IH with "† Dl") as "$". rewrite /depo_wsat_ret.
    case: (decide (β ⊑ α)); [|done]=> ?. rewrite lft_incl_dead; [|done].
    case: (decide (d' = d)); [|done]=> ->. by iApply depo_wsat_retrieve.
  Qed.
  (** Lemmas for [borrow_wsat_eq_retrieve] *)
  Local Lemma filter_eq_lt d Dm :
    filter_eq d Dm = filter_eq d (filter_lt (S d) Dm).
  Proof.
    rewrite map_filter_filter. apply map_filter_ext=> ?[[??]?]/=?. lia.
  Qed.
  Local Lemma filter_lt_lt d Dm :
    filter_lt d Dm = filter_lt d (filter_lt (S d) Dm).
  Proof.
    rewrite map_filter_filter. apply map_filter_ext=> ?[[??]?]/=?. lia.
  Qed.
  (** Retrieve from [borrow_wsat'] on [filter_eq] *)
  Local Lemma borrow_wsat_eq_retrieve {W E intp Dm d α} :
    [†α] -∗ borrow_wsat' W E intp (filter_eq d Dm) -∗
      borrow_wsat_ret W E intp Dm (S d) α =[W]{E}=∗
      borrow_wsat_ret W E intp Dm d α.
  Proof.
    iIntros "† eq ret W". rewrite big_sepM_filter' /= big_sepM_map_to_list_snd.
    iMod (depo_wsats_retrieve with "† eq [$ret $W]") as "[[ret $] eq]".
    iModIntro. iDestruct "ret" as (Dm' eq) "[● ret]". iExists _. iFrame "●".
    rewrite -big_sepM_map_to_list_snd -big_sepM_filter''.
    rewrite filter_eq_lt (filter_lt_lt d Dm) -!eq -filter_eq_lt -filter_lt_lt.
    iSplit; [done|].
    iApply (big_sepM_filter_complement (λ iD, dep_of iD.2 ≠ d)). iStopProof.
    do 2 f_equiv; rewrite map_filter_filter;
      apply map_filter_ext=> ?[[??][??]]/= _; lia.
  Qed.
  (** Lemma for [borrow_wsat_lt_retrieve] *)
  Local Lemma borrow_wsat_lt_S_split {W E intp} d Dm :
    borrow_wsat' W E intp (filter_lt (S d) Dm) ⊣⊢
      borrow_wsat' W E intp (filter_eq d Dm) ∗
      borrow_wsat' W E intp (filter_lt d Dm).
  Proof.
    rewrite (big_sepM_filter_complement (λ iD, dep_of iD.2 = d)).
    do 2 f_equiv; rewrite map_filter_filter;
      apply map_filter_ext=> ?[[??][??]]/= _; lia.
  Qed.
  (** Retrieve from [borrow_wsat'] on [filter_lt] *)
  Local Lemma borrow_wsat_lt_retrieve {W E intp Dm d α} :
    [†α] -∗ borrow_wsat' W E intp (filter_lt d Dm) -∗
      borrow_wsat_ret W E intp Dm d α =[W]{E}=∗ borrow_wsat_ret W E intp Dm 0 α.
  Proof.
    elim: d; [by iIntros|]=> ? IH. rewrite borrow_wsat_lt_S_split.
    iIntros "#† [eq lt] ret".
    iMod (borrow_wsat_eq_retrieve with "† eq ret") as "ret".
    iApply (IH with "† lt ret").
  Qed.

  (** Find large enough [d] that empties [filter_ge d Dm] *)
  Local Lemma filter_ge_empty Dm : ∃ d, filter_ge d Dm = ∅.
  Proof.
    induction Dm as [|i[[d' ?]?]?? [d eq]] using map_ind; [by exists 0|].
    exists (d `max` S d'). rewrite map_filter_insert_False /=; [|lia].
    rewrite map_filter_delete -(delete_empty i). f_equal.
    apply (f_equal (filter_ge (S d'))) in eq. move: eq.
    rewrite map_filter_filter map_filter_empty=> <-.
    apply map_filter_ext=> ?[[??]?]/=. lia.
  Qed.
  (** Retrive using [lend_dtok] *)
  Lemma lend_dtok_retrieve {W E intp d α P} :
    [†α] -∗ lend_dtok d α P =[borrow_wsat W E intp ∗ W]{E}=∗ intp P.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "† l [[%Dm[● Dm]] W]".
    case: (filter_ge_empty Dm)=> d' eq.
    iMod (borrow_wsat_lt_retrieve (d:=d') with "† [Dm] [●] W") as "[W ret]".
    { iDestruct (big_sepM_filter_complement with "Dm") as "[$ _]". }
    { iExists _. iFrame "●". rewrite eq. by iSplit. }
    iMod (lend_dtok_ret_retrieve with "l [$ret $W]") as "[[[%[_[● ?]]] $] $]";
      [lia|done|]. iModIntro.
    iExists _. iFrame "●". rewrite map_filter_id; [|lia]. iStopProof.
    do 2 f_equiv. move=> [[? β][??]]. rewrite /depo_wsat_ret.
    case: (decide (β ⊑ α))=> ?; [|done]. iIntros. by iRight.
  Qed.
  (** Retrive using [lend_tok] *)
  Lemma lend_tok_retrieve {W E intp α P} :
    [†α] -∗ lend_tok α P =[borrow_wsat W E intp ∗ W]{E}=∗ intp P.
  Proof.
    rewrite lend_tok_unseal. iIntros "† [%α'[⊑[%d l]]]".
    iDestruct (lft_sincl_dead with "⊑ †") as "†".
    iApply (lend_dtok_retrieve with "† l").
  Qed.

  (** [depo_wsat] with a lifetime token *)
  Local Lemma depo_wsat_tok {W E intp d α Bm Pm q} :
    q.[α] -∗ depo_wsat W E intp d α Bm Pm -∗
      q.[α] ∗ depo_wsat_in W E intp d α Bm Pm.
  Proof.
    iIntros "α [$|[† _]]"; [done|]. iDestruct (lft_tok_dead with "α †") as "[]".
  Qed.

  (** Update the borrower state to [Open q] *)
  Local Lemma bor_open_core {W E intp i j d α P b q} :
    q.[α] -∗ bor_itok i j d α (P, b)' =[borrow_wsat W E intp]=∗
      bor_otok α P q ∗ bor_wsat intp d α (P, b)'.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[α α'] b [%Dm[● Dm]]".
    iDestruct (depo_stm_bor_agree with "● b") as %[Bm[Qm[??]]].
    iDestruct (big_sepM_insert_acc with "Dm") as "[D →Dm]"; [done|].
    iDestruct (depo_wsat_tok with "α D") as "[α [Bm →Qm]]".
    iMod (depo_stm_bor_stupd with "● b") as "[● o]"; [done..|].
    iDestruct (big_sepM_insert_acc with "Bm") as "[$ →Bm]"; [done|]. iModIntro.
    iSplitR "α o"; last first.
    { rewrite bor_otok_unseal. iExists _, _, _, _, _.
      iSplitR; [iApply lft_sincl_refl|]. iSplitR; [by iIntros|]. iFrame. }
    iExists _. iFrame "●". iApply "→Dm". iLeft.
    iSplitR "→Qm"=>/=; [by iApply "→Bm"|]. iStopProof. do 2 f_equiv.
    apply bi.equiv_entails_1_1. by apply: big_sepM_insert_override.
  Qed.
  (** Open a closed borrower *)
  Lemma bor_ctok_open {W E intp q α P} :
    q.[α] -∗ bor_ctok α P =[borrow_wsat W E intp]=∗
      bor_otok α P q ∗ intp P.
  Proof.
    rewrite bor_ctok_unseal. iIntros "α [†|c]".
    { by iDestruct (lft_tok_dead with "α †") as "[]". }
    iDestruct "c" as (????) "[#⊑ c]".
    iMod (lft_sincl_tok_acc with "⊑ α") as (r) "[α' →α]".
    iMod (bor_open_core with "α' c") as "[o $]". iModIntro.
    iApply (bor_otok_lft with "⊑ →α o").
  Qed.
  (** Open a borrower *)
  Lemma bor_tok_open {W E intp q α P} :
    q.[α] -∗ bor_tok α P =[borrow_wsat W E intp ∗ W]{E}=∗
      bor_otok α P q ∗ intp P.
  Proof.
    rewrite bor_tok_unseal. iIntros "α [c|r]".
    { by iMod (bor_ctok_open with "α c"). }
    iDestruct "r" as (?????) "[#⊑ [#† r]]".
    iMod (lft_sincl_tok_acc with "⊑ α") as (r) "[α' →α]".
    iMod (bor_open_core with "α' r") as "[o [%[_ l]]]".
    iDestruct (bor_otok_lft with "⊑ →α o") as "$".
    iApply (lend_dtok_retrieve with "[] l").
    iApply (lft_sincl_dead with "[] †"). iApply lft_sincl_meet_r.
  Qed.

  (** Open borrow token with the depth and real lifetime explicit *)
  Local Definition bor_odtok d α α' P q : iProp Σ :=
    ∃ i j r, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗ (r/2).[α'] ∗
      bor_itok i j d α' (P, Open (r/2))'.
  (** Turn [bor_otok] into [bor_odtok] *)
  Local Lemma bor_otok_odtok {α P q} :
    bor_otok α P q ⊢ ∃ d α', α ⊑□ α' ∗ bor_odtok d α α' P q.
  Proof.
    rewrite bor_otok_unseal. iDestruct 1 as (α' r ???) "[#⊑ b]". iExists _, _.
    iFrame "⊑". by iExists _, _, _.
  Qed.

  (** Turn [bor_odtok] to a reborrower using [lend_dtok] *)
  Local Lemma bor_odtok_reborrow {W E intp d α α' P q β d'} : d < d' →
    bor_odtok d α α' P q -∗ lend_dtok d' (α' ⊓ β) P =[borrow_wsat W E intp]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α P).
  Proof.
    rewrite borrow_wsat_unseal. iDestruct 1 as (i j r) "[#⊑[→α[α' o]]]".
    iIntros "[%i'[%k l]] [%Dm [● Dm]]".
    iDestruct (depo_stm_bor_agree with "● o") as %[Bm[Pm[??]]].
    iDestruct (big_sepM_insert_acc with "Dm") as "[D →Dm]"; [done|]=>/=.
    iMod (depo_stm_bor_stupd (B':=(_,Rebor β)') with "● o") as "[● r]";
      [done..|]. iModIntro.
    iDestruct (depo_wsat_tok with "α' D") as "[α'[Bm →Pm]]".
    iDestruct (big_sepM_insert_acc with "Bm") as "[α'2 →Bm]"; [done|].
    iDestruct ("→α" with "[$α' $α'2]") as "$". iSplitR "r"; last first.
    { iIntros "†". rewrite bor_tok_unseal. iRight. iExists _, _, _, _, _.
      by iFrame. }
    iExists _. iFrame "●". iApply "→Dm". iLeft. iSplitR "→Pm".
    - iApply "→Bm". iExists _. iSplit; [done|]. by iExists _, _.
    - iClear "#". iStopProof. do 2 f_equiv=>/=. iIntros "Bm".
      iApply big_sepM_insert_override; [done| |done]. done.
  Qed.

  (** Lemma for [bor_otok_merge_subdiv] *)
  Local Lemma bor_otoks_odtoks_bound {α Pql} :
    ([∗ list] '(P, q)' ∈ Pql, bor_otok α P q) ⊢ ∃ d β, α ⊑□ β ∗
      [∗ list] '(P, q)' ∈ Pql, ∃ d' α' β',
        ⌜d' < d ∧ β = α' ⊓ β'⌝ ∗ bor_odtok d' α α' P q.
  Proof.
    elim: Pql=>/=.
    { iIntros. iExists 0, ⊤. iSplit; [iApply lft_sincl_top|done]. }
    move=> [P q] Pql ->. rewrite bor_otok_odtok.
    iIntros "[[%d[%α'[#⊑ o]]] [%d'[%β[#? big]]]]".
    iExists (S d `max` d'), (α' ⊓ β).
    iSplitR; [by iApply lft_sincl_meet_intro|]. iSplitL "o".
    { iExists _, _, _. iFrame "o". iPureIntro. split; [lia|done]. }
    iClear "#". iStopProof. do 3 f_equiv.
    iDestruct 1 as (d'' α'' β' [?->]) "o". iExists _, _, _. iFrame "o".
    iPureIntro. split; [lia|]. by rewrite assoc [α' ⊓ α'']comm -assoc.
  Qed.
  (** Merge and subdivide borrowers *)
  Lemma bor_otok_merge_subdiv {W E intp α} Pql Ql :
    ([∗ list] '(P, q)' ∈ Pql, bor_otok α P q) -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) =[W]{E}=∗ [∗ list] P ∈ Pql.*1', intp P)
      =[borrow_wsat W E intp]=∗
      ([∗ list] q ∈ Pql.*2', q.[α]) ∗ [∗ list] Q ∈ Ql, bor_ctok α Q.
  Proof.
    rewrite bor_otoks_odtoks_bound. iIntros "[%d[%β[#⊑ Pql]]] Ql →P".
    iMod (bor_lend_tok_new_list' d β Ql Pql.*1' with "Ql [→P]")
      as "[bl ll]"=>/=.
    { iIntros "† Ql". iDestruct (lft_sincl_dead with "⊑ †") as "†".
      by iMod ("→P" with "† Ql") as "$". }
    iSplitR "bl"; last first.
    { iModIntro. iApply (big_sepL_impl with "bl"). iIntros "!> %% _".
      by iApply bor_ctok_lft. }
    iInduction Pql as [|[P q]Pql] "IH"=>/=; [done|].
    iDestruct "Pql" as "[big Pql]". iDestruct "big" as (???[?->]) "o".
    iDestruct "ll" as "[l ll]". iMod ("IH" with "Pql ll") as "$".
    iMod (bor_odtok_reborrow with "o l") as "[$ _]"; [lia|done].
  Qed.
  (** Subdivide a borrower *)
  Lemma bor_otok_subdiv {W E intp α P q} Ql :
    bor_otok α P q -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) =[W]{E}=∗ intp P)
      =[borrow_wsat W E intp]=∗ q.[α] ∗ [∗ list] Q ∈ Ql, bor_ctok α Q.
  Proof.
    iIntros "o Ql →P".
    iMod (bor_otok_merge_subdiv [(_,_)'] with "[o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma bor_tok_close {W E intp q α P} :
    bor_otok α P q -∗ intp P =[borrow_wsat W E intp]=∗ q.[α] ∗ bor_ctok α P.
  Proof.
    iIntros "o P". iMod (bor_otok_subdiv [P] with "o [P] []") as "[$[$_]]"=>/=;
      by [iFrame|iIntros "_[$_]"|].
  Qed.

  (** Reborrow a borrower *)
  Lemma bor_otok_reborrow {W E intp α P q} β :
    bor_otok α P q -∗ intp P =[borrow_wsat W E intp]=∗
      q.[α] ∗ bor_ctok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P).
  Proof.
    rewrite bor_otok_odtok. iIntros "[%d[%α'[#? o]]] P".
    iMod (bor_lend_tok_new_list' (S d) (α' ⊓ β) [P] [P] with "[P] []")
      as "[[b _] [l _]]"; [by iFrame|by iIntros|].
    iMod (bor_odtok_reborrow with "o l") as "[$$]"; [lia|]. iModIntro.
    iApply (bor_ctok_lft with "[] b"). by iApply lft_sincl_meet_mono_l.
  Qed.
  Lemma bor_ctok_reborrow {W E intp α P q} β :
    q.[α] -∗ bor_ctok α P =[borrow_wsat W E intp]=∗
      q.[α] ∗ bor_ctok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P).
  Proof.
    iIntros "α c". iMod (bor_ctok_open with "α c") as "[o P]".
    by iMod (bor_otok_reborrow with "o P").
  Qed.
  Lemma bor_tok_reborrow {W E intp α P q} β :
    q.[α] -∗ bor_tok α P =[borrow_wsat W E intp ∗ W]{E}=∗
      q.[α] ∗ bor_ctok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P).
  Proof.
    iIntros "α b". iMod (bor_tok_open with "α b") as "[o P]".
    by iMod (bor_otok_reborrow with "o P").
  Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc `{!borrowGpreS PROP Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : borrowGS PROP Σ, ∀ W E intp, borrow_wsat W E intp.
Proof.
  iMod (own_alloc (● (∅ : gmapR _ _))) as (γ) "●"; [by apply auth_auth_valid|].
  iModIntro. iExists (BorrowGS _ _ _ _ γ). iIntros (???).
  rewrite borrow_wsat_unseal. iExists ∅. by iFrame.
Qed.

(** ** Fractured borrowing *)

(** State of a fractured borrower *)
Local Definition fbor_st PROP : Type := lft *' (Qp → PROP).

(** Ghost state for fractured borrowing *)
Class fborrowGS PROP Σ := fborrowGS_in : sinvGS (fbor_st PROP) Σ.
Local Existing Instance fborrowGS_in.
Class fborrowGpreS PROP Σ := fborrowGpreS_in : sinvGpreS (fbor_st PROP) Σ.
Local Existing Instance fborrowGpreS_in.
Definition fborrowΣ PROP : gFunctors := sinvΣ (fbor_st PROP).
#[export] Instance subG_fborrow `{!subG (fborrowΣ PROP) Σ} :
  fborrowGpreS PROP Σ.
Proof. solve_inG. Qed.

Section fborrow.
  Context `{!fborrowGS PROP Σ, !borrowGS PROP Σ, !invGS_gen hlc Σ}.
  Implicit Type (c : bool) (Φ : Qp → PROP).

  (** Fractional borrower token *)
  Local Definition fbor_tok_def α Φ : iProp Σ :=
    ∃ α', α ⊑□ α' ∗ sinv_tok (α', Φ)'.
  Local Lemma fbor_tok_aux : seal fbor_tok_def. Proof. by eexists. Qed.
  Definition fbor_tok := fbor_tok_aux.(unseal).
  Local Lemma fbor_tok_unseal : fbor_tok = fbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [fbor_tok] is persistent and timeless *)
  #[export] Instance fbor_tok_persistent {α Φ} : Persistent (fbor_tok α Φ).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.
  #[export] Instance fbor_tok_timeless {α Φ} : Timeless (fbor_tok α Φ).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.

  (** Modify the lifetime of [fbor_tok] *)
  Lemma fbor_tok_lft {α α' Φ} : α' ⊑□ α -∗ fbor_tok α Φ -∗ fbor_tok α' Φ.
  Proof.
    rewrite fbor_tok_unseal. iIntros "#? [%α''[#? f]]". iExists _. iFrame "f".
    by iApply lft_sincl_trans.
  Qed.

  (** Choice between [bor_ctok] and [bor_tok] *)
  Definition bor_xtok c := if c then bor_ctok else bor_tok.
  Lemma bor_xtok_tok {c α P} : bor_xtok c α P ⊢ bor_tok α P.
  Proof. case: c; [exact bor_ctok_tok|done]. Qed.
  Lemma bor_ctok_xtok {c α P} : bor_ctok α P ⊢ bor_xtok c α P.
  Proof. case: c; [done|exact bor_ctok_tok]. Qed.
  #[export] Instance bor_xtok_timeless {c α P} : Timeless (bor_xtok c α P).
  Proof. case: c; exact _. Qed.

  (** World satisfaction for the fractional borrowing machinery *)
  Definition fborrow_wsat_def c : iProp Σ :=
    sinv_wsat (λ '(α, Φ)', ∃ q, bor_xtok c α (Φ q))%I.
  Local Lemma fborrow_wsat_aux : seal fborrow_wsat_def. Proof. by eexists. Qed.
  Definition fborrow_wsat := fborrow_wsat_aux.(unseal).
  Local Lemma fborrow_wsat_unseal : fborrow_wsat = fborrow_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [fborrow_wsat] is timeless *)
  #[export] Instance fborrow_wsat_timeless {c} : Timeless (fborrow_wsat c).
  Proof. rewrite fborrow_wsat_unseal. exact _. Qed.

  (** Turn [bor_ctok] into [fbor_tok] *)
  Lemma bor_fbor_tok {α Φ q} c :
    bor_xtok c α (Φ q) =[fborrow_wsat c]=∗ fbor_tok α Φ.
  Proof.
    rewrite fborrow_wsat_unseal. iIntros "b W".
    iMod (sinv_alloc (_,_)' with "W") as "[#t →W]". iModIntro. iSplitL.
    { iApply "→W". by iExists _. }
    rewrite fbor_tok_unseal. iExists _. iSplit; by [iApply lft_sincl_refl|].
  Qed.

  (** Open [fbor_tok] *)
  Lemma fbor_tok_open' {W E intp α q} `(!Fractional (intp ∘ Φ)) :
    q.[α] -∗ fbor_tok α Φ =[fborrow_wsat true ∗ borrow_wsat W E intp]=∗
      ∃ r, bor_otok α (Φ r) q ∗ intp (Φ r).
  Proof.
    rewrite fbor_tok_unseal fborrow_wsat_unseal. iIntros "α [%α'[#⊑ i]] [F B]".
    iDestruct (sinv_acc with "i F") as "[[%r c] →F]".
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[α' →α]".
    iMod (bor_ctok_open with "α' c B") as "[B [o Φ]]".
    have eq : intp (Φ r) ⊣⊢ intp (Φ (r/2)%Qp) ∗ intp (Φ (r/2)%Qp).
    { by erewrite fractional_half; [|apply: fractional_as_fractional]. }
    rewrite eq. iDestruct "Φ" as "[Φ Φ']".
    iMod (bor_otok_subdiv [_;_] with "o [Φ Φ'] [] B") as "[B [α'[c[c' _]]]]".
    { by iFrame. } { rewrite eq. by iIntros "_ [$[$ _]]". }
    iMod (bor_ctok_open with "α' c' B") as "[$ [o Φ]]". iModIntro.
    iDestruct (bor_otok_lft with "[//] →α o") as "o".
    iSplitR "o Φ"; [|iExists _; by iFrame]. iApply "→F". by iExists _.
  Qed.
  Lemma fbor_tok_open {c W E intp α q} `(!Fractional (intp ∘ Φ)) :
    q.[α] -∗ fbor_tok α Φ =[fborrow_wsat c ∗ borrow_wsat W E intp ∗ W]{E}=∗
      ∃ r, bor_otok α (Φ r) q ∗ intp (Φ r).
  Proof.
    rewrite fbor_tok_unseal fborrow_wsat_unseal. iIntros "α [%α'[#⊑ i]] [F BW]".
    iDestruct (sinv_acc with "i F") as "[[%r b] →F]". rewrite bor_xtok_tok.
    iMod (lft_sincl_tok_acc with "⊑ α") as (s) "[α' →α]".
    iMod (bor_tok_open with "α' b BW") as "[[B $] [o Φ]]".
    have eq : intp (Φ r) ⊣⊢ intp (Φ (r/2)%Qp) ∗ intp (Φ (r/2)%Qp).
    { by erewrite fractional_half; [|apply: fractional_as_fractional]. }
    rewrite eq. iDestruct "Φ" as "[Φ Φ']".
    iMod (bor_otok_subdiv [_;_] with "o [Φ Φ'] [] B") as "[B [α'[c[c' _]]]]".
    { by iFrame. } { rewrite eq. by iIntros "_ [$[$ _]]". }
    iMod (bor_ctok_open with "α' c' B") as "[$ [o Φ]]". iModIntro.
    iDestruct (bor_otok_lft with "[//] →α o") as "o".
    iSplitR "o Φ"; [|iExists _; by iFrame]. iApply "→F". rewrite bor_ctok_xtok.
    by iExists _.
  Qed.
End fborrow.

(** Allocate [fborrow_wsat] *)
Lemma fborrow_wsat_alloc `{!fborrowGpreS PROP Σ, !borrowGS PROP Σ} :
  ⊢ |==> ∃ _ : fborrowGS PROP Σ, ∀ c, fborrow_wsat c.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _. iIntros (?).
  rewrite fborrow_wsat_unseal. iApply "W".
Qed.
