(** * Borrowing machinery *)

From nola.util Require Export prod.
From nola.bi Require Export gen_upd updw.
From nola.bi Require Import order gmap.
From nola.iris Require Export ofe lft.
From iris.bi.lib Require Import cmra.
From iris.algebra Require Import excl agree gmap auth.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation LftNotation UpdwNotation.

Implicit Type (PROP : oFunctor) (α : lft) (q : Qp).

(** ** Ghost state *)

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
#[warning="-redundant-canonical-projection"]
Local Canonical bor_modeO := leibnizO bor_mode.

(** State of a borrower *)
Local Definition bor_stOF PROP : oFunctor := PROP * bor_modeO.
(** State of the borrowers *)
Local Definition bor_stmOF PROP := (gmapOF bor_id (bor_stOF PROP)).

(** State of the lenders *)
Local Definition lendmOF PROP := (gmapOF lend_id PROP).

(** Kind of a deposit *)
Local Definition depo_kind : Set := nat (* depth *) *' lft.
Implicit Type e : depo_kind.
#[warning="-redundant-canonical-projection"]
Local Canonical depo_kindO := leibnizO depo_kind.

(** State of a deposit *)
Local Definition depo_stOF PROP : oFunctor :=
  depo_kindO * bor_stmOF PROP * lendmOF PROP.
(** State of the deposits *)
Local Definition depo_stmOF PROP := (gmapOF depo_id (depo_stOF PROP)).

(** Algebra for a borrower *)
Local Definition borRF PROP := exclRF (bor_stOF PROP).
(** Algebra for a lender *)
Local Definition lendRF PROP := exclRF PROP.
(** Algebra for a deposit *)
Local Definition depoRF PROP : rFunctor :=
  agreeRF depo_kindO *
  gmapRF bor_id (borRF PROP) * gmapRF lend_id (lendRF PROP).

(** Algebra for the borrowing machinery *)
Local Definition borrowRF_def PROP := authRF (gmapURF depo_id (depoRF PROP)).
Local Lemma borrowRF_aux : seal borrowRF_def. Proof. by eexists. Qed.
Definition borrowRF := borrowRF_aux.(unseal).
Local Lemma borrowRF_unseal : borrowRF = borrowRF_def.
Proof. exact: seal_eq. Qed.
Local Instance borrowRF_contractive `{!oFunctorContractive PROP} :
  rFunctorContractive (borrowRF PROP).
Proof. rewrite borrowRF_unseal. exact _. Qed.

(** Ghost state for the borrowing machinery *)
Class borrowGpreS PROP Σ := BorrowGpreS {
  borrowGpreS_lft :: lftG Σ;
  borrowGpreS_borrow : inG Σ (borrowRF PROP $ri Σ);
}.
Local Existing Instance borrowGpreS_borrow.
Class borrowGS PROP Σ := BorrowGS {
  borrowGS_pre :: borrowGpreS PROP Σ;
  borrow_name : gname;
}.
Local Instance inG_borrow_def `{!inG Σ (borrowRF PROP $ri Σ)} :
  inG Σ (borrowRF_def PROP $ri Σ).
Proof. rewrite -borrowRF_unseal. exact _. Qed.
Definition borrowΣ PROP `{!oFunctorContractive PROP} : gFunctors :=
  #[GFunctor lftR; GFunctor (borrowRF PROP)].
#[export] Instance subG_borrow
  `{!oFunctorContractive PROP, !subG (borrowΣ PROP) Σ} : borrowGpreS PROP Σ.
Proof. solve_inG. Qed.

(** ** Tokens *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (P Q : PROP $oi Σ) (Pl Ql : list (PROP $oi Σ))
    (D : depo_stOF PROP $oi Σ) (Dm : depo_stmOF PROP $oi Σ)
    (B : bor_stOF PROP $oi Σ) (Bm : bor_stmOF PROP $oi Σ)
    (Pm : lendmOF PROP $oi Σ).

  (** General borrower token *)
  Local Definition bor_itok i j d α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree (d, α)', {[j := Excl B]}, ε)]}).

  (** Closed borrower token

    It may be a dead lifetime token or a closed borrower

    Slightly stronger than [bor_tok] *)
  Local Definition borc_tok_def α P : iProp Σ :=
    [†α] ∨ ∃ i j d α', α ⊑□ α' ∗ bor_itok i j d α' (P, Clsd).
  Local Lemma borc_tok_aux : seal borc_tok_def. Proof. by eexists. Qed.
  Definition borc_tok := borc_tok_aux.(unseal).
  Local Lemma borc_tok_unseal : borc_tok = borc_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Borrower token

    It may be [bor_tok] or a retrieving reborrower *)
  Local Definition bor_tok_def α P : iProp Σ :=
    borc_tok α P ∨ ∃ i j d α' β,
      α ⊑□ α' ∗ [†β] ∗ bor_itok i j d α' (P, Rebor β).
  Local Lemma bor_tok_aux : seal bor_tok_def. Proof. by eexists. Qed.
  Definition bor_tok := bor_tok_aux.(unseal).
  Local Lemma bor_tok_unseal : bor_tok = bor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open borrower token

    It keeps an alive lifetime token [(r/2).[α']] at hand *)
  Local Definition obor_tok_def α q P : iProp Σ :=
    ∃ α' r i j d, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗
      (r/2).[α'] ∗ bor_itok i j d α' (P, Open (r/2)).
  Local Lemma obor_tok_aux : seal obor_tok_def. Proof. by eexists. Qed.
  Definition obor_tok := obor_tok_aux.(unseal).
  Local Lemma obor_tok_unseal : obor_tok = obor_tok_def.
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

  (** Borrower and lender tokens are non-expansive *)
  Local Instance bor_itok_ne {i j d α} : NonExpansive (bor_itok i j d α).
  Proof.
    unfold bor_itok=> ????. do 2 f_equiv. apply singleton_ne.
    do 2 apply pair_ne=>//. apply singleton_ne. by f_equiv.
  Qed.
  #[export] Instance borc_tok_ne {α} : NonExpansive (borc_tok α).
  Proof. rewrite borc_tok_unseal. solve_proper. Qed.
  #[export] Instance bor_tok_ne {α} : NonExpansive (bor_tok α).
  Proof. rewrite bor_tok_unseal. solve_proper. Qed.
  #[export] Instance obor_tok_ne {α q} : NonExpansive (obor_tok α q).
  Proof. rewrite obor_tok_unseal. solve_proper. Qed.
  Local Instance lend_itok_ne {i k d α} : NonExpansive (lend_itok i k d α).
  Proof.
    unfold lend_itok=> ????. do 2 f_equiv. apply singleton_ne.
    apply pair_ne=>//. apply singleton_ne. by f_equiv.
  Qed.
  Local Instance lend_dtok_ne {d α} : NonExpansive (lend_dtok d α).
  Proof. solve_proper. Qed.
  #[export] Instance lend_tok_ne {α} : NonExpansive (lend_tok α).
  Proof. rewrite lend_tok_unseal. solve_proper. Qed.

  (** Borrower and lender tokens are timeless for discrete propositions *)
  #[export] Instance borc_tok_timeless `{!Discrete P} {α} :
    Timeless (borc_tok α P).
  Proof. rewrite borc_tok_unseal. exact _. Qed.
  #[export] Instance bor_tok_timeless `{!Discrete P} {α} :
    Timeless (bor_tok α P).
  Proof. rewrite bor_tok_unseal. exact _. Qed.
  #[export] Instance obor_tok_timeless `{!Discrete P} {α q} :
    Timeless (obor_tok α q P).
  Proof. rewrite obor_tok_unseal. exact _. Qed.
  #[export] Instance lend_tok_timeless `{!Discrete P} {α} :
    Timeless (lend_tok α P).
  Proof. rewrite lend_tok_unseal. exact _. Qed.

  (** Turn [borc_tok] to [bor_tok] *)
  Lemma borc_tok_bor_tok {α P} : borc_tok α P ⊢ bor_tok α P.
  Proof. rewrite bor_tok_unseal. iIntros. by iLeft. Qed.

  (** Fake a borrower token from the dead lifetime token *)
  Lemma borc_tok_fake {α} P : [†α] ⊢ borc_tok α P.
  Proof. rewrite borc_tok_unseal. iIntros. by iLeft. Qed.
  Lemma bor_tok_fake {α} P : [†α] ⊢ bor_tok α P.
  Proof. by rewrite borc_tok_fake borc_tok_bor_tok. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma borc_tok_lft {α β P} : β ⊑□ α -∗ borc_tok α P -∗ borc_tok β P.
  Proof.
    rewrite borc_tok_unseal. iIntros "#? [?|c]".
    { iLeft. by iApply lft_sincl_dead. }
    iDestruct "c" as (????) "[#? c]". iRight. iExists _, _, _, _. iFrame "c".
    by iApply lft_sincl_trans.
  Qed.
  Lemma bor_tok_lft {α β P} : β ⊑□ α -∗ bor_tok α P -∗ bor_tok β P.
  Proof.
    rewrite bor_tok_unseal. iIntros "#⊑ [c|r]".
    { iLeft. by iApply (borc_tok_lft with "⊑ c"). }
    iDestruct "r" as (?????) "[#? r]". iRight. iExists _, _, _, _, _.
    iFrame "r". by iApply lft_sincl_trans.
  Qed.
  Lemma obor_tok_lft {α β q r P} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor_tok α q P -∗ obor_tok β r P.
  Proof.
    rewrite obor_tok_unseal. iIntros "#? →β".
    iDestruct 1 as (α' ????) "[#?[→α o]]". iExists _, _, _, _, _. iFrame "o".
    iSplit; [by iApply lft_sincl_trans|]. iIntros "α'". iApply "→β".
    by iApply "→α".
  Qed.
  Lemma lend_tok_lft {α β P} : α ⊑□ β -∗ lend_tok α P -∗ lend_tok β P.
  Proof.
    rewrite lend_tok_unseal. iIntros "#? [%α'[#? l]]". iExists _. iFrame "l".
    by iApply lft_sincl_trans.
  Qed.

  (** Token for [depo_stm] *)
  Local Definition depo_st_R D : depoRF PROP $ri Σ :=
    let '(e, Bm, Pm) := D in (to_agree e, Excl <$> Bm, Excl <$> Pm).
  Arguments depo_st_R _ /.
  Local Definition depo_stm_tok Dm : iProp Σ :=
    own borrow_name (● (depo_st_R <$> Dm : gmapR _ _)).

  (** Lemma for [to_bor_itoks] *)
  Local Lemma bor_insert_op {i j e B Bm} :
    Bm !! j = None →
    (◯ {[i := (to_agree e, Excl <$> <[j:=B]> Bm, ε)]} : borrowRF_def _ $ri _) ≡
      ◯ {[i := (to_agree e, {[j:=Excl B]}, ε)]} ⋅
      ◯ {[i := (to_agree e, Excl <$> Bm, ε)]}.
  Proof.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp| |done].
    rewrite insert_singleton_op; [done|]. by rewrite lookup_fmap eq.
  Qed.
  (** Get [bor_itok]s out of [own] *)
  Local Lemma to_bor_itoks {i d α Bm} :
    own borrow_name (◯ {[i := (to_agree (d, α)', Excl <$> Bm, ε)]}) ⊢
      [∗ map] j ↦ B ∈ Bm, bor_itok i j d α B.
  Proof.
    induction (Bm : gmap _ _) as [|j B Bm' ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH bor_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Lemma for [to_lend_itoks] *)
  Local Lemma lend_insert_op {i k e P Pm} :
    Pm !! k = None →
    (◯ {[i := (to_agree e, ε, Excl <$> <[k:=P]> Pm)]} : borrowRF_def _ $ri _) ≡
      ◯ {[i := (to_agree e, ε, {[k:=Excl P]})]} ⋅
      ◯ {[i := (to_agree e, ε, Excl <$> Pm)]}.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp|done|].
    rewrite insert_singleton_op; [done|]. by rewrite lookup_fmap eq.
  Qed.
  (** Get [lend_itok]s out of [own] *)
  Local Lemma to_lend_itoks {i d α Pm} :
    own borrow_name (◯ {[i := (to_agree (d, α)', ε, Excl <$> Pm)]}) ⊢
      [∗ map] k ↦ P ∈ Pm, lend_itok i k d α P.
  Proof.
    induction (Pm : gmap _ _) as [|k P Pm' ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH lend_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Create [bor_itok]s and [lend_itok]s w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_borc_lend_new {Dm} d α Pl Ql :
    depo_stm_tok Dm -∗ |==> ∃ i,
      let Bm := map_by _ (fmap (M:=list) (λ P, (P, Clsd)) Pl) in
      let Qm := map_by _ Ql in
      depo_stm_tok (<[i := ((d, α)', Bm, Qm)]> Dm) ∗
      ([∗ map] j ↦ B ∈ Bm, bor_itok i j d α B) ∗
      [∗ map] k ↦ Q ∈ Qm, lend_itok i k d α Q.
  Proof.
    iIntros "●". iExists (fresh (dom Dm)).
    iMod (own_update with "●") as "[$[c l]]"; last first.
    { iModIntro. iDestruct (to_bor_itoks (d:=d) with "c") as "$".
      iApply (to_lend_itoks with "l"). }
    rewrite -auth_frag_op singleton_op fmap_insert.
    have <- : ∀ x y, ((to_agree (d, α)', x, y) : depoRF _ $ri _) ≡
      ((to_agree (d, α)', x, ε) : depoRF _ $ri _) ⋅ (to_agree (d, α)', ε, y).
    { split; [split|]=>/=; by
        [rewrite agree_idemp|rewrite left_id|rewrite right_id]. }
    apply auth_update_alloc, alloc_singleton_local_update.
    - rewrite lookup_fmap. apply fmap_None, not_elem_of_dom_1, is_fresh.
    - split; [split|]=>/=; [done|by apply: gmap_fmap_valid..].
  Qed.

  (** Lemma for [depo_stm_lend_agree] and [depo_stm_bor_agree] *)
  Local Lemma depo_stm_own_agree {Dm i d α Bx Px} :
    depo_stm_tok Dm -∗
    own borrow_name (◯ {[i := (to_agree (d, α)', Bx, Px)]}) -∗
    ∃ Bm Pm, ⌜Dm !! i = Some ((d, α)', Bm, Pm)⌝ ∧
      Bx ≼ Excl <$> Bm ∧ Px ≼ Excl <$> Pm.
  Proof.
    iIntros "● o". iDestruct (own_valid_2 with "● o") as "?". iStopProof.
    unfold internal_included. uPred.unseal. split=> n ? _.
    (repeat unfold uPred_holds=>/=)=> valid.
    apply auth_both_validN, proj1, singleton_includedN_l in valid as
      [?[eqv incl]].
    apply Some_equiv_eq in eqv as (?&eq&eqv).
    apply lookup_fmap_Some in eq as ([[dα Bm]Pm]&<-&?). exists Bm, Pm.
    rewrite Some_includedN_total in incl. rewrite -eqv in incl.
    apply prod_includedN in incl as [incl ?].
    apply prod_includedN in incl as [incl ?]. simpl in *.
    by apply to_agree_includedN, leibniz_equiv in incl as <-.
  Qed.

  (** Agreement between [depo_stm_tok] and [lend_itok] *)
  Local Lemma depo_stm_lend_agree {Dm i k d α P} :
    depo_stm_tok Dm -∗ lend_itok i k d α P -∗ ∃ Bm Pm P',
      ⌜Dm !! i = Some ((d, α)', Bm, Pm)⌝ ∧ ⌜Pm !! k = Some P'⌝ ∧ P' ≡ P.
  Proof.
    iIntros "● l".
    iDestruct (depo_stm_own_agree with "● l") as (Bm Pm ?) "[_?]".
    iStopProof. unfold internal_included. uPred.unseal. split=> n ? _.
    repeat unfold uPred_holds=>/=.
    move /singleton_includedN_l=>
      [?[/Some_equiv_eq[?[/lookup_fmap_Some[P'[<-?]]<-]]/Excl_includedN incl]].
    by exists Bm, Pm, P'.
  Qed.
  (** Delete a lender w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_lend_delete {Dm i k d α Bm Pm P} :
    Dm !! i = Some ((d, α)', Bm, Pm) →
    depo_stm_tok Dm -∗ lend_itok i k d α P ==∗
      depo_stm_tok (<[i := ((d, α)', Bm, delete k Pm)]> Dm).
  Proof.
    move=> ?. iIntros "● l". iMod (own_update_2 with "● l") as "[$_]"; [|done].
    apply auth_update. rewrite fmap_insert.
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_delete. apply: delete_local_update; last first.
    { by rewrite lookup_singleton. } exact _.
  Qed.
  (** Add lenders w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_lend_add {Dm i d α Bm Pm} Ql :
    Dm !! i = Some ((d, α)', Bm, Pm) →
    depo_stm_tok Dm ==∗
      depo_stm_tok (<[i := ((d, α)', Bm, map_with Pm Ql)]> Dm) ∗
      [∗ map] k ↦ Q ∈ map_without Pm Ql, lend_itok i k d α Q.
  Proof.
    move=> eq. iIntros "●". iMod (own_update with "●") as "[$ ?]"; last first.
    { iModIntro. by iApply to_lend_itoks. }
    rewrite fmap_insert. apply auth_update_alloc, gmap_local_update.
    move=> i'. case: (decide (i = i'))=> [<-|?]; last first.
    { rewrite lookup_insert_ne; [|done]. by rewrite lookup_singleton_ne. }
    rewrite lookup_empty lookup_fmap eq !lookup_insert /=.
    apply local_update_unital=> n ?[/=??]. rewrite left_id=> <-. split.
    { split; [done|]. by apply: gmap_fmap_valid. }
    rewrite -Some_op. f_equiv.
    split; [split|]=>/=; [by rewrite agree_idemp|by rewrite left_id|].
    rewrite gmap_op_disj; [|by apply map_disjoint_fmap, map_without_disj].
    by rewrite -map_fmap_union -map_with_without.
  Qed.

  (** Agreement between [depo_stm_tok] and [bor_itok] *)
  Local Lemma depo_stm_bor_agree {Dm i j d α B} :
    depo_stm_tok Dm -∗ bor_itok i j d α B -∗ ∃ Bm Pm B',
      ⌜Dm !! i = Some ((d, α)', Bm, Pm)⌝ ∧ ⌜Bm !! j = Some B'⌝ ∧ B' ≡ B.
  Proof.
    iIntros "● B".
    iDestruct (depo_stm_own_agree with "● B") as (Bm Pm ?) "[? _]".
    iStopProof. unfold internal_included. uPred.unseal. split=> n ? _.
    repeat unfold uPred_holds=>/=.
    move /singleton_includedN_l=>
      [?[/Some_equiv_eq[?[/lookup_fmap_Some[B'[<-?]]<-]]/Excl_includedN incl]].
    by exists Bm, Pm, B'.
  Qed.
  (** Update the borrower state w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_bor_stupd {Dm i j d α Bm Pm B B'} :
    Dm !! i = Some ((d, α)', Bm, Pm) →
    depo_stm_tok Dm -∗ bor_itok i j d α B ==∗
      depo_stm_tok (<[i := ((d, α)', <[j := B']> Bm, Pm)]> Dm) ∗
      bor_itok i j d α B'.
  Proof.
    move=> eq. iIntros "● B".
    iDestruct (depo_stm_bor_agree with "● B") as (??? eq' eq'') "#_".
    move: eq' eq''. rewrite eq. move=> [<- _] ?.
    iMod (own_update_2 with "● B") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    rewrite fmap_insert. apply: singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. } by apply exclusive_local_update.
  Qed.
End borrow.

(** ** World satisfactions *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (M : iProp Σ → iProp Σ) (ip : PROP $oi Σ -d> iProp Σ)
    (P Q : PROP $oi Σ) (D : depo_stOF PROP $oi Σ) (Dm : depo_stmOF PROP $oi Σ)
    (B : bor_stOF PROP $oi Σ) (Bm : bor_stmOF PROP $oi Σ)
    (Pm : lendmOF PROP $oi Σ).

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat ip d α B : iProp Σ :=
    let '(Q, b) := B in match b with
    | Clsd => ip Q | Open q => q.[α]
    | Rebor β => ∃ d', ⌜d < d'⌝ ∗ lend_dtok d' (α ⊓ β) Q
    end.

  (** World satisfaction for a deposit *)
  Local Definition depo_wsat_in M ip d α Bm Pm : iProp Σ :=
    ([∗ map] B ∈ Bm, bor_wsat ip d α B) ∗
    ([†α] -∗ ([∗ map] '(Q, _) ∈ Bm, ip Q) -∗ M ([∗ map] P ∈ Pm, ip P)%I).
  Local Definition depo_wsat_dead M ip α Pm : iProp Σ :=
    [†α] ∗ M ([∗ map] P ∈ Pm, ip P)%I.
  Local Definition depo_wsat M ip d α Bm Pm : iProp Σ :=
    depo_wsat_in M ip d α Bm Pm ∨ depo_wsat_dead M ip α Pm.

  (** World satisfaction for the borrowing machinery *)
  Local Definition borrow_wsat' M ip Dm :=
    ([∗ map] '((d, α)', Bm, Pm) ∈ Dm, depo_wsat M ip d α Bm Pm)%I.
  Local Definition borrow_wsat_def M ip : iProp Σ :=
    ∃ Dm, depo_stm_tok Dm ∗ borrow_wsat' M ip Dm.
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
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (=) ==> (=) ==> (=) ==>
      (=) ==> (≡{n}≡)) depo_wsat.
  Proof.
    move=> ?? eqv ?????<-??<-??<-??<-.
    unfold depo_wsat, depo_wsat_in, depo_wsat_dead.
    (repeat f_equiv); [done|..]; apply eqv; solve_proper.
  Qed.
  #[export] Instance borrow_wsat_ne {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡)) borrow_wsat.
  Proof.
    rewrite borrow_wsat_unseal /borrow_wsat_def /borrow_wsat'=> ??????.
    repeat f_equiv. by apply depo_wsat_ne.
  Qed.

  (** [borrow_wsat] is monotone over the modality *)
  Local Instance depo_wsat_mono :
    Mono (OT:=_ → _ : bi) (OT':=_ → _ → _ → _ → _ → _ : bi) depo_wsat.
  Proof.
    move=> ?? to ?????. unfold depo_wsat, depo_wsat_in, depo_wsat_dead.
    repeat f_equiv; exact: to.
  Qed.
  #[export] Instance borrow_wsat_mono :
    Mono (OT:=_ → _ : bi) (OT':=_ → _ : bi) borrow_wsat.
  Proof.
    rewrite borrow_wsat_unseal /borrow_wsat_def /borrow_wsat'=> ????.
    repeat f_equiv. by apply: depo_wsat_mono.
  Qed.

  Context `{!GenUpd M, !GenUpdBupd M, !NonExpansive ip}.

  (** Create new borrowers and lenders with a specific depth *)
  Local Lemma borc_lend_tok_new_list' d α Pl Ql :
    ([∗ list] P ∈ Pl, ip P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ip P) -∗ M ([∗ list] Q ∈ Ql, ip Q)%I)
      =[borrow_wsat M ip]=∗
      ([∗ list] P ∈ Pl, borc_tok α P) ∗ [∗ list] Q ∈ Ql, lend_dtok d α Q.
  Proof.
    rewrite borrow_wsat_unseal borc_tok_unseal. iIntros "Pl →Ql [%Dm[● Dm]]".
    iMod (depo_stm_borc_lend_new d α Pl Ql with "●") as (?) "[●[c l]]".
    iModIntro. rewrite !big_sepM_map_by' big_sepL_fmap.
    iSplitR "c l"; last first; [iSplitL "c"; iStopProof; do 3 f_equiv;
      iIntros "[% ?]"; [|by iExists _, _]|].
    { iRight. iExists _, _, _, _. iSplitR; by [iApply lft_sincl_refl|]. }
    iExists _. iFrame "●". iApply (big_sepM_insert_2 with "[Pl →Ql] Dm"). iLeft.
    iSplitL "Pl";by rewrite !big_sepM_map_by big_sepL_fmap.
  Qed.

  (** Create new borrowers and lenders *)
  Lemma borc_lend_tok_new_list α Pl Ql :
    ([∗ list] P ∈ Pl, ip P) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ip P) -∗ M ([∗ list] Q ∈ Ql, ip Q)%I)
      =[borrow_wsat M ip]=∗
      ([∗ list] P ∈ Pl, borc_tok α P) ∗ [∗ list] Q ∈ Ql, lend_tok α Q.
  Proof.
    iIntros "Pl →Ql". iMod (borc_lend_tok_new_list' 0 with "Pl →Ql") as "[$ ?]".
    iModIntro. iStopProof. do 3 f_equiv. iIntros "l". rewrite lend_tok_unseal.
    iExists _. iSplit; [by iApply lft_sincl_refl|]. by iExists _.
  Qed.
  (** Simply create a new borrower and a new lender *)
  Lemma borc_lend_tok_new α P :
    ip P =[borrow_wsat M ip]=∗ borc_tok α P ∗ lend_tok α P.
  Proof.
    iIntros "P". iMod (borc_lend_tok_new_list α [P] [P] with "[P] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma lend_tok_split {α P} Ql :
    lend_tok α P -∗ (ip P -∗ M ([∗ list] Q ∈ Ql, ip Q))
      =[borrow_wsat M ip]=∗ [∗ list] Q ∈ Ql, lend_tok α Q.
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "[%α'[#?[%d[%i[%k l]]]]] PQ [%Dm[● Dm]]".
    iDestruct (depo_stm_lend_agree with "● l") as (Bm Pm P' ? ?) "#eqv".
    iRewrite -"eqv" in "PQ".
    iMod (depo_stm_lend_delete with "● l") as "●"; [done|].
    iMod (depo_stm_lend_add Ql with "●") as "[● ls]".
    { apply (lookup_insert (M:=gmap _)). }
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
  Local Notation dep_of D := D.1.1.1'.
  Local Notation filter_ge d := (filter (λ iD, d ≤ dep_of iD.2)).
  Local Notation filter_lt d := (filter (λ iD, dep_of iD.2 < d)).
  Local Notation filter_eq d := (filter (λ iD, dep_of iD.2 = d)).
  (** [borrow_wsat'] with deposits under [d] and [α] retrieved *)
  Local Definition depo_wsat_ret M ip d' α β Bm Pm : iProp Σ :=
    if decide (β ⊑ α) then depo_wsat_dead M ip β Pm
    else depo_wsat M ip d' β Bm Pm.
  Local Definition borrow_wsat_ret M ip Dm d α : iProp Σ :=
    ∃ Dm', ⌜filter_lt d Dm' = filter_lt d Dm⌝ ∗ depo_stm_tok Dm' ∗
      [∗ map] '((d', β)', Bm, Pm) ∈ filter_ge d Dm',
        depo_wsat_ret M ip d' α β Bm Pm.

  (** Retrieve from [borrow_wsat_ret] using [lend_dtok] *)
  Local Lemma lend_dtok_ret_retrieve {Dm d d' α β P} : d ≤ d' → β ⊑ α →
    lend_dtok d' β P -∗ modw M (borrow_wsat_ret M ip Dm d α) (ip P).
  Proof.
    move=> ??. iIntros "[%[% l]] [%Dm'[%[● Dm']]]".
    iDestruct (depo_stm_lend_agree with "● l") as (Bm Pm P' eq ?) "#eqv".
    iRewrite -"eqv". iDestruct (big_sepM_insert_acc with "Dm'") as "[D →Dm']".
    { rewrite map_lookup_filter_Some. split; [done|]. unfold dep_of=>/=. lia. }
    rewrite /depo_wsat_ret decide_True; [|done]. iDestruct "D" as "[† >Pm]".
    iDestruct (big_sepM_delete with "Pm") as "[$ Pm]"; [done|]=>/=.
    iMod (depo_stm_lend_delete with "● l") as "●"; [done..|]. iModIntro.
    iExists _. iFrame "●". iSplit.
    { iPureIntro. rewrite map_filter_insert_False /=; [|lia].
      rewrite map_filter_delete_not; [done|]. rewrite eq. move=> ?[<-]/=. lia. }
    rewrite map_filter_insert_True /=; [|done]. iApply "→Dm'".
    rewrite decide_True; [|done]. by iFrame.
  Qed.

  (** Retrieve from [bor_wsat] *)
  Local Lemma bor_wsat_retrieve {Dm d α β P b} : β ⊑ α →
    [†β] -∗ bor_wsat ip d β (P, b) -∗
      modw M (borrow_wsat_ret M ip Dm (S d) α) (ip P).
  Proof.
    move=> ?. iIntros "† B". case b=> [|q|?]/=; [done|..].
    { iDestruct (lft_alive_dead with "B †") as "[]". }
    iDestruct "B" as (??) "l". iApply (lend_dtok_ret_retrieve with "l"); [lia|].
    etrans; [|done]. apply lft_incl_meet_l.
  Qed.
  (** Retrieve from [bor_wsat]s *)
  Local Lemma bor_wsats_retrieve {Dm d α β Bl} : β ⊑ α →
    [†β] -∗ ([∗ list] B ∈ Bl, bor_wsat ip d β B) -∗
      modw M (borrow_wsat_ret M ip Dm (S d) α) ([∗ list] '(P, _) ∈ Bl, ip P)%I.
  Proof.
    move=> ?. elim: Bl; [by iIntros|]. move=>/= [??]Bl IH. iIntros "#† [B Bl]".
    iMod (IH with "† Bl") as "$". by iApply bor_wsat_retrieve.
  Qed.
  (** Retrieve from [depo_wsat] *)
  Local Lemma depo_wsat_retrieve {Dm d α β Bm Pm} : β ⊑ α →
    [†β] -∗ depo_wsat M ip d β Bm Pm -∗
      modw M (borrow_wsat_ret M ip Dm (S d) α) (depo_wsat_dead M ip β Pm)%I.
  Proof.
    move=> ?. iIntros "#† [[Bl →Pm]|?]"; [|done]. iFrame "†". iApply modw_fold.
    iDestruct ("→Pm" with "†") as "→Pm". rewrite !big_sepM_map_to_list_snd.
    move: (map_to_list Bm).*2=> Bl.
    iMod (bor_wsats_retrieve with "† Bl") as "Bl"; [done..|].
    iDestruct ("→Pm" with "Bl") as "$". by iIntros.
  Qed.
  (** Retrieve from [depo_wsat]s *)
  Local Lemma depo_wsats_retrieve {Dm d α Dl} :
    [†α] -∗ ([∗ list] D ∈ Dl,
      if decide (dep_of D = d) then let '((d', β)', Bm, Pm) := D in
        depo_wsat M ip d' β Bm Pm else emp) -∗
      modw M (borrow_wsat_ret M ip Dm (S d) α)
        ([∗ list] D ∈ Dl,
          if decide (dep_of D = d) then let '((d', β)', Bm, Pm) := D in
            depo_wsat_ret M ip d' α β Bm Pm else emp)%I.
  Proof.
    elim: Dl; [by iIntros|]. move=> [[[d' β]?]?] Dl IH /=. iIntros "#† [D Dl]".
    iMod (IH with "† Dl") as "$". iApply modw_fold. rewrite /depo_wsat_ret.
    case: (decide (β ⊑ α)); [|done]=> ?. rewrite lft_incl_dead; [|done].
    case: (decide (d' = d)); [|done]=> ->. by iApply depo_wsat_retrieve.
  Qed.
  (** Lemmas for [borrow_wsat_eq_retrieve] *)
  Local Lemma filter_eq_lt d Dm :
    filter_eq d Dm = filter_eq d (filter_lt (S d) Dm).
  Proof.
    rewrite map_filter_filter.
    apply (map_filter_ext (M:=gmap _))=> ?[[??]?]/=?. lia.
  Qed.
  Local Lemma filter_lt_lt d Dm :
    filter_lt d Dm = filter_lt d (filter_lt (S d) Dm).
  Proof.
    rewrite map_filter_filter.
    apply (map_filter_ext (M:=gmap _))=> ?[[??]?]/=?. lia.
  Qed.
  (** Retrieve from [borrow_wsat'] on [filter_eq] *)
  Local Lemma borrow_wsat_eq_retrieve {Dm d α} :
    [†α] -∗ borrow_wsat' M ip (filter_eq d Dm) -∗
      borrow_wsat_ret M ip Dm (S d) α -∗
      M (borrow_wsat_ret M ip Dm d α).
  Proof.
    iIntros "† eq ret".
    rewrite /borrow_wsat' big_sepM_filter' /= big_sepM_map_to_list_snd.
    iMod (depo_wsats_retrieve with "† eq ret") as "[ret eq]".
    iModIntro. iDestruct "ret" as (Dm' eq) "[● ret]". iExists _. iFrame "●".
    rewrite -big_sepM_map_to_list_snd -big_sepM_filter''.
    rewrite filter_eq_lt (filter_lt_lt d Dm) -!eq -filter_eq_lt -filter_lt_lt.
    iSplit; [done|].
    iApply (big_sepM_filter_complement (λ iD, dep_of iD.2 ≠ d)). iStopProof.
    do 2 f_equiv; rewrite map_filter_filter;
      apply (map_filter_ext (M:=gmap _))=>/=; lia.
  Qed.
  (** Lemma for [borrow_wsat_lt_retrieve] *)
  Local Lemma borrow_wsat_lt_S_split d Dm :
    borrow_wsat' M ip (filter_lt (S d) Dm) ⊣⊢
      borrow_wsat' M ip (filter_eq d Dm) ∗ borrow_wsat' M ip (filter_lt d Dm).
  Proof.
    rewrite /borrow_wsat' (big_sepM_filter_complement (λ iD, dep_of iD.2 = d)).
    do 2 f_equiv; rewrite map_filter_filter;
      apply (map_filter_ext (M:=gmap _))=>/=; lia.
  Qed.
  (** Retrieve from [borrow_wsat'] on [filter_lt] *)
  Local Lemma borrow_wsat_lt_retrieve {Dm d α} :
    [†α] -∗ borrow_wsat' M ip (filter_lt d Dm) -∗
      borrow_wsat_ret M ip Dm d α -∗ M (borrow_wsat_ret M ip Dm 0 α).
  Proof.
    elim: d; [by iIntros|]=> ? IH. rewrite borrow_wsat_lt_S_split.
    iIntros "#† [eq lt] ret".
    iMod (borrow_wsat_eq_retrieve with "† eq ret") as "ret".
    iApply (IH with "† lt ret").
  Qed.

  (** Find large enough [d] that empties [filter_ge d Dm] *)
  Local Lemma filter_ge_empty Dm : ∃ d, filter_ge d Dm = ∅.
  Proof.
    induction (Dm : gmap _ _) as [|i[[[d' ?] ?]?]?? [d eq]] using map_ind;
      [by exists 0|].
    exists (d `max` S d'). rewrite map_filter_insert_False /=; [|lia].
    rewrite map_filter_delete -(delete_empty i). f_equal.
    apply (f_equal (filter_ge (S d'))) in eq. move: eq.
    rewrite map_filter_filter map_filter_empty=> <-.
    apply map_filter_ext=> ?[[??]?]/=. lia.
  Qed.
  (** Retrive using [lend_dtok] *)
  Local Lemma lend_dtok_retrieve {d α P} :
    [†α] -∗ lend_dtok d α P -∗ modw M (borrow_wsat M ip) (ip P).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "† l [%Dm[● Dm]]".
    case: (filter_ge_empty Dm)=> d' eq.
    iMod (borrow_wsat_lt_retrieve (d:=d') with "† [Dm] [●]") as "ret".
    { iDestruct (big_sepM_filter_complement with "Dm") as "[$ _]". }
    { iExists _. iFrame "●". rewrite eq. by iSplit. }
    iMod (lend_dtok_ret_retrieve with "l ret") as "[[%[_[● ?]]]$]"; [lia|done|].
    iModIntro. iExists _. iFrame "●".
    rewrite map_filter_id; [|lia]. iStopProof. unfold borrow_wsat'.
    do 2 f_equiv. move=> [[[? β]?]?]. unfold depo_wsat_ret.
    case: (decide (β ⊑ α))=> ?; [|done]. iIntros. by iRight.
  Qed.
  (** Retrive using [lend_tok] *)
  Lemma lend_tok_retrieve {α P} :
    [†α] -∗ lend_tok α P -∗ modw M (borrow_wsat M ip) (ip P).
  Proof.
    rewrite lend_tok_unseal. iIntros "† [%α'[⊑[%d l]]]".
    iDestruct (lft_sincl_dead with "⊑ †") as "†".
    by iApply (lend_dtok_retrieve with "† l").
  Qed.

  (** [depo_wsat] with an alive lifetime token *)
  Local Lemma depo_wsat_tok {d α Bm Pm q} :
    q.[α] -∗ depo_wsat M ip d α Bm Pm -∗ q.[α] ∗ depo_wsat_in M ip d α Bm Pm.
  Proof.
    iIntros "α [$|[† _]]"; [done|].
    iDestruct (lft_alive_dead with "α †") as "[]".
  Qed.

  (** [bor_wsat] is non-expansive over the borrower state *)
  Local Instance bor_wsat_ne_st {d α} : NonExpansive (bor_wsat ip d α).
  Proof.
    move=> ?[?[|?|?]][?[|?|?]][//=eqv /leibniz_equiv_iff].
    { by rewrite eqv. } { by move=> [<-]. }
    move=> [<-]. unfold lend_dtok, lend_itok. do 9 f_equiv.
    apply singleton_ne. split=>/=; [done|]. by rewrite eqv.
  Qed.

  (** Update the borrower state to [Open q] *)
  Local Lemma bor_open_core {i j d α P b q} :
    q.[α] -∗ bor_itok i j d α (P, b) =[borrow_wsat M ip]=∗
      obor_tok α q P ∗ bor_wsat ip d α (P, b).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[α α'] b [%Dm[● Dm]]".
    iDestruct (depo_stm_bor_agree with "● b") as (Bm Qm [P' b'] ??) "#eqv".
    iDestruct (big_sepM_insert_acc with "Dm") as "[D →Dm]"; [done|].
    iDestruct (depo_wsat_tok with "α D") as "[α [Bm →Qm]]".
    iMod (depo_stm_bor_stupd with "● b") as "[● o]"; [done..|]. iRewrite -"eqv".
    iDestruct (big_sepM_insert_acc with "Bm") as "[$ →Bm]"; [done|]. iModIntro.
    iSplitR "α o"; last first.
    { rewrite obor_tok_unseal. iExists _, _, _, _, _.
      iSplitR; [iApply lft_sincl_refl|]. iSplitR; [by iIntros|]. iFrame. }
    iExists _. iFrame "●". iApply "→Dm". iLeft.
    iSplitR "→Qm"=>/=; [by iApply "→Bm"|]. iIntros "† big".
    iApply ("→Qm" with "†").
    iApply (big_sepM_insert_override_1 with "big"); [done|].
    rewrite prod_equivI /=. iDestruct "eqv" as "[eqv _]". iRewrite "eqv".
    by iIntros.
  Qed.
  (** Open a closed borrower *)
  Lemma borc_tok_open {α q P} :
    q.[α] -∗ borc_tok α P =[borrow_wsat M ip]=∗ obor_tok α q P ∗ ip P.
  Proof.
    rewrite borc_tok_unseal. iIntros "α [†|c]".
    { by iDestruct (lft_alive_dead with "α †") as "[]". }
    iDestruct "c" as (????) "[#⊑ c]".
    iMod (lft_sincl_alive_acc with "⊑ α") as (r) "[α' →α]".
    iMod (bor_open_core with "α' c") as "[o $]". iModIntro.
    iApply (obor_tok_lft with "⊑ →α o").
  Qed.
  (** Open a borrower *)
  Lemma bor_tok_open {α q P} :
    q.[α] -∗ bor_tok α P -∗ modw M (borrow_wsat M ip) (obor_tok α q P ∗ ip P).
  Proof.
    rewrite bor_tok_unseal. iIntros "α [c|r]".
    { by iMod (borc_tok_open with "α c"). }
    iDestruct "r" as (?????) "[#⊑ [#† r]]".
    iMod (lft_sincl_alive_acc with "⊑ α") as (r) "[α' →α]".
    iMod (bor_open_core with "α' r") as "[o [%[_ l]]]".
    iDestruct (obor_tok_lft with "⊑ →α o") as "$". iApply modw_fold.
    iApply (lend_dtok_retrieve with "[] l").
    iApply (lft_sincl_dead with "[] †"). iApply lft_sincl_meet_r.
  Qed.

  (** Open borrow token with the depth and real lifetime explicit *)
  Local Definition obor_dtok d α α' q P : iProp Σ :=
    ∃ i j r, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗ (r/2).[α'] ∗
      bor_itok i j d α' (P, Open (r/2)).
  (** Turn [obor_tok] into [obor_dtok] *)
  Local Lemma obor_tok_dtok {α q P} :
    obor_tok α q P ⊢ ∃ d α', α ⊑□ α' ∗ obor_dtok d α α' q P.
  Proof.
    rewrite obor_tok_unseal. iDestruct 1 as (α' r ???) "[#⊑ b]". iExists _, _.
    iFrame "⊑". by iExists _, _, _.
  Qed.

  (** Turn [obor_dtok] to a reborrower using [lend_dtok] *)
  Local Lemma obor_dtok_reborrow {d α α' q P β d'} : d < d' →
    obor_dtok d α α' q P -∗ lend_dtok d' (α' ⊓ β) P =[borrow_wsat M ip]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α P).
  Proof.
    rewrite borrow_wsat_unseal. iDestruct 1 as (i j r) "[#⊑[→α[α' o]]]".
    iIntros "[%i'[%k l]] [%Dm [● Dm]]".
    iDestruct (depo_stm_bor_agree with "● o") as (Bm Pm B' ??) "#eqv".
    iDestruct (big_sepM_insert_acc with "Dm") as "[D →Dm]"; [done|]=>/=.
    iMod (depo_stm_bor_stupd (B':=(_,Rebor β)) with "● o") as "[● r]";
      [done..|]. iModIntro.
    iDestruct (depo_wsat_tok with "α' D") as "[α'[Bm →Pm]]".
    iDestruct (big_sepM_insert_acc with "Bm") as "[B' →Bm]"; [done|].
    iRewrite "eqv" in "B'"=>/=.
    iDestruct ("→α" with "[$α' $B']") as "$". iSplitR "r"; last first.
    { iIntros "†". rewrite bor_tok_unseal. iRight. iExists _, _, _, _, _.
      by iFrame. }
    iExists _. iFrame "●". iApply "→Dm". iLeft. iSplitR "→Pm".
    { iApply "→Bm". iExists _. iSplit; [done|]. by iExists _, _. }
    iIntros "† big". iApply ("→Pm" with "†").
    iApply (big_sepM_insert_override_1 with "big"); [done|].
    rewrite prod_equivI /=. iDestruct "eqv" as "[eqv _]". case B'=>/= ??.
    iRewrite "eqv". by iIntros.
  Qed.

  (** Lemma for [obor_tok_merge_subdiv] *)
  Local Lemma obor_toks_dtoks_bound {αqPl β} :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obor_tok α q P) ⊢ ∃ d γ, β ⊑□ γ ∗
      [∗ list] '(α, q, P)' ∈ αqPl, ∃ d' α' γ',
        ⌜d' < d ∧ γ = α' ⊓ γ'⌝ ∗ obor_dtok d' α α' q P.
  Proof.
    elim: αqPl=>/=.
    { iIntros. iExists 0, ⊤. iSplit; [iApply lft_sincl_top|done]. }
    move=> [α[P q]] αqPl ->. rewrite obor_tok_dtok.
    iIntros "[[#βα[%d[%α'[#αα' o]]]] [%d'[%γ[#βγ big]]]]".
    iExists (S d `max` d'), (α' ⊓ γ). iSplitR.
    { iApply lft_sincl_meet_intro; [|done].
      by iApply lft_sincl_trans; [|done]. } iSplitL "o".
    { iExists _, _, _. iFrame "o". iPureIntro. split; [lia|done]. }
    iClear "#". iStopProof. do 3 f_equiv.
    iDestruct 1 as (d'' α'' β' [?->]) "o". iExists _, _, _. iFrame "o".
    iPureIntro. split; [lia|]. by rewrite assoc [α' ⊓ α'']comm -assoc.
  Qed.
  (** Merge and subdivide borrowers *)
  Lemma obor_tok_merge_subdiv αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obor_tok α q P) -∗
    ([∗ list] Q ∈ Ql, ip Q) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ip Q) -∗ M ([∗ list] '(_, _, P)' ∈ αqPl, ip P)%I)
      =[borrow_wsat M ip]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ [∗ list] Q ∈ Ql, borc_tok β Q.
  Proof.
    rewrite/= obor_toks_dtoks_bound. iIntros "[%d[%γ[#⊑ αqPl]]] Ql →P".
    iMod (borc_lend_tok_new_list' d γ Ql ((λ '(_, _, P)', P) <$> αqPl)
      with "Ql [→P]") as "[bl ll]"=>/=.
    { iIntros "† Ql". iDestruct (lft_sincl_dead with "⊑ †") as "†".
      rewrite big_sepL_fmap. iApply ("→P" with "† Ql"). }
    iSplitR "bl"; last first.
    { iModIntro. iApply (big_sepL_impl with "bl"). iIntros "!> %% _".
      by iApply borc_tok_lft. }
    iInduction αqPl as [|[α[q P]]αqPl] "IH"=>/=; [done|].
    iDestruct "αqPl" as "[big αqPl]". iDestruct "big" as (???[?->]) "o".
    iDestruct "ll" as "[l ll]". iMod ("IH" with "αqPl ll") as "$".
    iMod (obor_dtok_reborrow with "o l") as "[$ _]"; [lia|done].
  Qed.
  (** Subdivide a borrower *)
  Lemma obor_tok_subdiv {α q P} Ql β :
    β ⊑□ α -∗ obor_tok α q P -∗ ([∗ list] Q ∈ Ql, ip Q) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ip Q) -∗ M (ip P))
      =[borrow_wsat M ip]=∗ q.[α] ∗ [∗ list] Q ∈ Ql, borc_tok β Q.
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (obor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]")
      as "[[$_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obor_tok_close {α q P} :
    obor_tok α q P -∗ ip P =[borrow_wsat M ip]=∗ q.[α] ∗ borc_tok α P.
  Proof.
    iIntros "o P".
    iMod (obor_tok_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Reborrow a borrower *)
  Lemma obor_tok_reborrow {α q P} β :
    obor_tok α q P -∗ ip P =[borrow_wsat M ip]=∗
      q.[α] ∗ borc_tok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P).
  Proof.
    rewrite obor_tok_dtok. iIntros "[%d[%α'[#? o]]] P".
    iMod (borc_lend_tok_new_list' (S d) (α' ⊓ β) [P] [P] with "[P] []")
      as "[[b _] [l _]]"; [by iFrame|by iIntros|].
    iMod (obor_dtok_reborrow with "o l") as "[$$]"; [lia|]. iModIntro.
    iApply (borc_tok_lft with "[] b"). by iApply lft_sincl_meet_mono_l.
  Qed.
  Lemma borc_tok_reborrow {α q P} β :
    q.[α] -∗ borc_tok α P =[borrow_wsat M ip]=∗
      q.[α] ∗ borc_tok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P).
  Proof.
    iIntros "α c". iMod (borc_tok_open with "α c") as "[o P]".
    by iMod (obor_tok_reborrow with "o P").
  Qed.
  Lemma bor_tok_reborrow {α q P} β :
    q.[α] -∗ bor_tok α P -∗ modw M (borrow_wsat M ip)
      (q.[α] ∗ borc_tok (α ⊓ β) P ∗ ([†β] -∗ bor_tok α P)).
  Proof.
    iIntros "α b". iMod (bor_tok_open with "α b") as "[o P]".
    by iMod (obor_tok_reborrow with "o P").
  Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc `{!borrowGpreS PROP Σ} :
  ⊢ |==> ∃ _ : borrowGS PROP Σ, ∀ M ip, borrow_wsat M ip.
Proof.
  iMod (own_alloc (● (∅ : gmap _ _) : borrowRF_def PROP $ri Σ)) as (γ) "●";
    [by apply auth_auth_valid|].
  iModIntro. iExists (BorrowGS _ _ _ γ). iIntros (??).
  rewrite borrow_wsat_unseal. iExists ∅. unfold borrow_wsat'. by iFrame.
Qed.
