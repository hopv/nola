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

Implicit Type (FML : oFunctor) (α : lft) (q : Qp).

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
Local Definition bor_stOF FML : oFunctor := FML * bor_modeO.
(** State of the borrowers *)
Local Definition bor_stmOF FML := (gmapOF bor_id (bor_stOF FML)).

(** State of the lenders *)
Local Definition lendmOF FML := (gmapOF lend_id FML).

(** Kind of a deposit *)
Local Definition depo_kind : Set := nat (* depth *) *' lft.
Implicit Type e : depo_kind.
#[warning="-redundant-canonical-projection"]
Local Canonical depo_kindO := leibnizO depo_kind.

(** State of a deposit *)
Local Definition depo_stOF FML : oFunctor :=
  depo_kindO * bor_stmOF FML * lendmOF FML.
(** State of the deposits *)
Local Definition depo_stmOF FML := (gmapOF depo_id (depo_stOF FML)).

(** Algebra for a borrower *)
Local Definition borRF FML := exclRF (bor_stOF FML).
(** Algebra for a lender *)
Local Definition lendRF FML := exclRF FML.
(** Algebra for a deposit *)
Local Definition depoRF FML : rFunctor :=
  agreeRF depo_kindO *
  gmapRF bor_id (borRF FML) * gmapRF lend_id (lendRF FML).

(** Algebra for the borrowing machinery *)
Local Definition borrowRF_def FML := authRF (gmapURF depo_id (depoRF FML)).
Local Lemma borrowRF_aux : seal borrowRF_def. Proof. by eexists. Qed.
Definition borrowRF := borrowRF_aux.(unseal).
Local Lemma borrowRF_unseal : borrowRF = borrowRF_def.
Proof. exact: seal_eq. Qed.
Local Instance borrowRF_contractive `{!oFunctorContractive FML} :
  rFunctorContractive (borrowRF FML).
Proof. rewrite borrowRF_unseal. exact _. Qed.

(** Ghost state for the borrowing machinery *)
Class borrowGpreS FML Σ := BorrowGpreS {
  borrowGpreS_lft :: lftG Σ;
  borrowGpreS_borrow : inG Σ (borrowRF FML $ri Σ);
}.
Local Existing Instance borrowGpreS_borrow.
Class borrowGS FML Σ := BorrowGS {
  borrowGS_pre :: borrowGpreS FML Σ;
  borrow_name : gname;
}.
Local Instance inG_borrow_def `{!inG Σ (borrowRF FML $ri Σ)} :
  inG Σ (borrowRF_def FML $ri Σ).
Proof. rewrite -borrowRF_unseal. exact _. Qed.
Definition borrowΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[GFunctor lftR; GFunctor (borrowRF FML)].
#[export] Instance subG_borrow
  `{!oFunctorContractive FML, !subG (borrowΣ FML) Σ} : borrowGpreS FML Σ.
Proof. solve_inG. Qed.

(** ** Tokens *)

Section borrow.
  Context `{!borrowGS FML Σ}.
  Implicit Type (Px Qx : FML $oi Σ) (Pxl Qxl : list (FML $oi Σ))
    (D : depo_stOF FML $oi Σ) (Dm : depo_stmOF FML $oi Σ)
    (B : bor_stOF FML $oi Σ) (Bm : bor_stmOF FML $oi Σ)
    (Pm : lendmOF FML $oi Σ).

  (** General borrower token *)
  Local Definition bor_itok i j d α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree (d, α)', {[j := Excl B]}, ε)]}).

  (** Borrower token

    It may be a dead lifetime token, a closed borrower, or a retrieving
    reborrower *)
  Local Definition bor_tok_def α Px : iProp Σ :=
    [†α] ∨ ∃ α' i j d, α ⊑□ α' ∗
      (bor_itok i j d α' (Px, Clsd) ∨
      ∃ β, [†β] ∗ bor_itok i j d α' (Px, Rebor β)).
  Local Lemma bor_tok_aux : seal bor_tok_def. Proof. by eexists. Qed.
  Definition bor_tok := bor_tok_aux.(unseal).
  Local Lemma bor_tok_unseal : bor_tok = bor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open borrower token

    It keeps a live lifetime token [(r/2).[α']] at hand *)
  Local Definition obor_tok_def α q Px : iProp Σ :=
    ∃ α' r i j d, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗
      (r/2).[α'] ∗ bor_itok i j d α' (Px, Open (r/2)).
  Local Lemma obor_tok_aux : seal obor_tok_def. Proof. by eexists. Qed.
  Definition obor_tok := obor_tok_aux.(unseal).
  Local Lemma obor_tok_unseal : obor_tok = obor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Lender token *)
  Local Definition lend_itok i k d α Px : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree (d, α)', ε, {[k := Excl Px]})]}).
  Local Definition lend_dtok d α Px : iProp Σ :=
    ∃ i k, lend_itok i k d α Px.
  Local Definition lend_tok_def α Px : iProp Σ :=
    ∃ α', α' ⊑□ α ∗ ∃ d, lend_dtok d α' Px.
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

  (** Borrower and lender tokens are timeless for discrete formulas *)
  #[export] Instance bor_tok_timeless `{!Discrete Px} {α} :
    Timeless (bor_tok α Px).
  Proof. rewrite bor_tok_unseal. exact _. Qed.
  #[export] Instance obor_tok_timeless `{!Discrete Px} {α q} :
    Timeless (obor_tok α q Px).
  Proof. rewrite obor_tok_unseal. exact _. Qed.
  #[export] Instance lend_tok_timeless `{!Discrete Px} {α} :
    Timeless (lend_tok α Px).
  Proof. rewrite lend_tok_unseal. exact _. Qed.

  (** Fake a borrower token from the dead lifetime token *)
  Lemma bor_tok_fake {α} Px : [†α] ⊢ bor_tok α Px.
  Proof. rewrite bor_tok_unseal. iIntros. by iLeft. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma bor_tok_lft {α β Px} : β ⊑□ α -∗ bor_tok α Px -∗ bor_tok β Px.
  Proof.
    rewrite bor_tok_unseal. iIntros "#? [?|b]".
    { iLeft. by iApply lft_sincl_dead. }
    iDestruct "b" as (????) "[#? b]". iRight. iExists _, _, _, _. iFrame "b".
    by iApply lft_sincl_trans.
  Qed.
  Lemma obor_tok_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor_tok α q Px -∗ obor_tok β r Px.
  Proof.
    rewrite obor_tok_unseal. iIntros "#? →β".
    iDestruct 1 as (α' ????) "[#?[→α o]]". iExists _, _, _, _, _. iFrame "o".
    iSplit; [by iApply lft_sincl_trans|]. iIntros "α'". iApply "→β".
    by iApply "→α".
  Qed.
  Lemma lend_tok_lft {α β Px} : α ⊑□ β -∗ lend_tok α Px -∗ lend_tok β Px.
  Proof.
    rewrite lend_tok_unseal. iIntros "#? [%α'[#? l]]". iExists _. iFrame "l".
    by iApply lft_sincl_trans.
  Qed.

  (** Token for [depo_stm] *)
  Local Definition depo_st_R D : depoRF FML $ri Σ :=
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
  Local Lemma lend_insert_op {i k e Px Pm} :
    Pm !! k = None →
    (◯ {[i := (to_agree e, ε, Excl <$> <[k:=Px]> Pm)]} : borrowRF_def _ $ri _) ≡
      ◯ {[i := (to_agree e, ε, {[k:=Excl Px]})]} ⋅
      ◯ {[i := (to_agree e, ε, Excl <$> Pm)]}.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp|done|].
    rewrite insert_singleton_op; [done|]. by rewrite lookup_fmap eq.
  Qed.
  (** Get [lend_itok]s out of [own] *)
  Local Lemma to_lend_itoks {i d α Pm} :
    own borrow_name (◯ {[i := (to_agree (d, α)', ε, Excl <$> Pm)]}) ⊢
      [∗ map] k ↦ Px ∈ Pm, lend_itok i k d α Px.
  Proof.
    induction (Pm : gmap _ _) as [|k Px Pm' ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH lend_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Create [bor_itok]s and [lend_itok]s w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_bor_lend_new {Dm} d α Pxl Qxl :
    depo_stm_tok Dm -∗ |==> ∃ i,
      let Bm := map_by _ (fmap (M:=list) (λ Px, (Px, Clsd)) Pxl) in
      let Qm := map_by _ Qxl in
      depo_stm_tok (<[i := ((d, α)', Bm, Qm)]> Dm) ∗
      ([∗ map] j ↦ B ∈ Bm, bor_itok i j d α B) ∗
      [∗ map] k ↦ Qx ∈ Qm, lend_itok i k d α Qx.
  Proof.
    iIntros "●". iExists (fresh (dom Dm)).
    iMod (own_update with "●") as "[$[b l]]"; last first.
    { iModIntro. iDestruct (to_bor_itoks (d:=d) with "b") as "$".
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
  Local Lemma depo_stm_own_agree {Dm i d α Bx Pxx} :
    depo_stm_tok Dm -∗
    own borrow_name (◯ {[i := (to_agree (d, α)', Bx, Pxx)]}) -∗
    ∃ Bm Pm, ⌜Dm !! i = Some ((d, α)', Bm, Pm)⌝ ∧
      Bx ≼ Excl <$> Bm ∧ Pxx ≼ Excl <$> Pm.
  Proof.
    iIntros "● o". iDestruct (own_valid_2 with "● o") as "?". iStopProof.
    unfold internal_included. uPred.unseal. split=> n ? _.
    (repeat unfold uPred_holds=>/=)=> valid.
    apply auth_both_validN, proj1, singleton_includedN_l in valid as
      [?[eqv incl]].
    apply Some_equiv_eq in eqv as (? & eq & eqv).
    apply lookup_fmap_Some in eq as ([[dα Bm]Pm] & <- & ?). exists Bm, Pm.
    rewrite Some_includedN_total in incl. rewrite -eqv in incl.
    apply prod_includedN in incl as [incl ?].
    apply prod_includedN in incl as [incl ?]. simpl in *.
    by apply to_agree_includedN, leibniz_equiv in incl as <-.
  Qed.

  (** Agreement between [depo_stm_tok] and [lend_itok] *)
  Local Lemma depo_stm_lend_agree {Dm i k d α Px} :
    depo_stm_tok Dm -∗ lend_itok i k d α Px -∗ ∃ Bm Pm Px',
      ⌜Dm !! i = Some ((d, α)', Bm, Pm)⌝ ∧ ⌜Pm !! k = Some Px'⌝ ∧ Px' ≡ Px.
  Proof.
    iIntros "● l".
    iDestruct (depo_stm_own_agree with "● l") as (Bm Pm ?) "[_?]".
    iStopProof. unfold internal_included. uPred.unseal. split=> n ? _.
    repeat unfold uPred_holds=>/=.
    move /singleton_includedN_l=>
      [?[/Some_equiv_eq[?[/lookup_fmap_Some[Px'[<-?]]<-]]/Excl_includedN incl]].
    by exists Bm, Pm, Px'.
  Qed.
  (** Delete a lender w.r.t. [depo_stm_tok] *)
  Local Lemma depo_stm_lend_delete {Dm i k d α Bm Pm Px} :
    Dm !! i = Some ((d, α)', Bm, Pm) →
    depo_stm_tok Dm -∗ lend_itok i k d α Px ==∗
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
  Local Lemma depo_stm_lend_add {Dm i d α Bm Pm} Qxl :
    Dm !! i = Some ((d, α)', Bm, Pm) →
    depo_stm_tok Dm ==∗
      depo_stm_tok (<[i := ((d, α)', Bm, map_with Pm Qxl)]> Dm) ∗
      [∗ map] k ↦ Qx ∈ map_without Pm Qxl, lend_itok i k d α Qx.
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
  Context `{!borrowGS FML Σ}.
  Implicit Type (M : iProp Σ → iProp Σ) (sm : FML $oi Σ -d> iProp Σ)
    (Px Qx : FML $oi Σ) (D : depo_stOF FML $oi Σ) (Dm : depo_stmOF FML $oi Σ)
    (B : bor_stOF FML $oi Σ) (Bm : bor_stmOF FML $oi Σ)
    (Pm : lendmOF FML $oi Σ).

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat sm d α B : iProp Σ :=
    let '(Qx, b) := B in match b with
    | Clsd => sm Qx | Open q => q.[α]
    | Rebor β => ∃ d', ⌜d < d'⌝ ∗ lend_dtok d' (α ⊓ β) Qx
    end.

  (** World satisfaction for a deposit *)
  Local Definition depo_wsat_in M sm d α Bm Pm : iProp Σ :=
    ([∗ map] B ∈ Bm, bor_wsat sm d α B) ∗
    ([†α] -∗ ([∗ map] '(Qx, _) ∈ Bm, sm Qx) -∗ M ([∗ map] Px ∈ Pm, sm Px)%I).
  Local Definition depo_wsat_dead M sm α Pm : iProp Σ :=
    [†α] ∗ M ([∗ map] Px ∈ Pm, sm Px)%I.
  Local Definition depo_wsat M sm d α Bm Pm : iProp Σ :=
    depo_wsat_in M sm d α Bm Pm ∨ depo_wsat_dead M sm α Pm.

  (** World satisfaction for the borrowing machinery *)
  Local Definition borrow_wsat' M sm Dm :=
    ([∗ map] '((d, α)', Bm, Pm) ∈ Dm, depo_wsat M sm d α Bm Pm)%I.
  Local Definition borrow_wsat_def M sm : iProp Σ :=
    ∃ Dm, depo_stm_tok Dm ∗ borrow_wsat' M sm Dm.
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

  Context `{!GenUpd M, !GenUpdBupd M, !NonExpansive sm}.

  (** Create new borrowers and lenders with a specific depth *)
  Local Lemma bor_lend_tok_new_list' d α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, sm Px) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, sm Px) -∗ M ([∗ list] Qx ∈ Qxl, sm Qx)%I)
      =[borrow_wsat M sm]=∗
      ([∗ list] Px ∈ Pxl, bor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, lend_dtok d α Qx.
  Proof.
    rewrite borrow_wsat_unseal bor_tok_unseal. iIntros "Pxl →Qxl [%Dm[● Dm]]".
    iMod (depo_stm_bor_lend_new d α Pxl Qxl with "●") as (?) "[●[b l]]".
    iModIntro. rewrite !big_sepM_map_by' big_sepL_fmap.
    iSplitR "b l"; last first; [iSplitL "b"; iStopProof; do 3 f_equiv;
      iIntros "[% ?]"; [|by iExists _, _]|].
    { iRight. iExists _, _, _, _. iSplitR; by [iApply lft_sincl_refl|iLeft]. }
    iExists _. iFrame "●". iApply (big_sepM_insert_2 with "[Pxl →Qxl] Dm").
    iLeft. iSplitL "Pxl"; by rewrite !big_sepM_map_by big_sepL_fmap.
  Qed.

  (** Create new borrowers and lenders *)
  Lemma bor_lend_tok_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, sm Px) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, sm Px) -∗ M ([∗ list] Qx ∈ Qxl, sm Qx)%I)
      =[borrow_wsat M sm]=∗
      ([∗ list] Px ∈ Pxl, bor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, lend_tok α Qx.
  Proof.
    iIntros "Pxl →Qxl".
    iMod (bor_lend_tok_new_list' 0 with "Pxl →Qxl") as "[$ ?]".
    iModIntro. iStopProof. do 3 f_equiv. iIntros "l". rewrite lend_tok_unseal.
    iExists _. iSplit; [by iApply lft_sincl_refl|]. by iExists _.
  Qed.
  (** Simply create a new borrower and a new lender *)
  Lemma bor_lend_tok_new α Px :
    sm Px =[borrow_wsat M sm]=∗ bor_tok α Px ∗ lend_tok α Px.
  Proof.
    iIntros "Px". iMod (bor_lend_tok_new_list α [Px] [Px] with "[Px] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma lend_tok_split {α Px} Qxl :
    lend_tok α Px -∗ (sm Px -∗ M ([∗ list] Qx ∈ Qxl, sm Qx))
      =[borrow_wsat M sm]=∗ [∗ list] Qx ∈ Qxl, lend_tok α Qx.
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "[%α'[#?[%d[%i[%k l]]]]] PQ [%Dm[● Dm]]".
    iDestruct (depo_stm_lend_agree with "● l") as (Bm Pm Px' ? ?) "#eqv".
    iRewrite -"eqv" in "PQ".
    iMod (depo_stm_lend_delete with "● l") as "●"; [done|].
    iMod (depo_stm_lend_add Qxl with "●") as "[● ls]".
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
      iDestruct (big_sepM_delete with "Pm") as "[Px $]"; [done|].
      by iApply "PQ".
  Qed.

  (** Filter [depo_stm] with a depth *)
  Local Notation dep_of D := D.1.1.1'.
  Local Notation filter_ge d := (filter (λ iD, d ≤ dep_of iD.2)).
  Local Notation filter_lt d := (filter (λ iD, dep_of iD.2 < d)).
  Local Notation filter_eq d := (filter (λ iD, dep_of iD.2 = d)).
  (** [borrow_wsat'] with deposits under [d] and [α] retrieved *)
  Local Definition depo_wsat_ret M sm d' α β Bm Pm : iProp Σ :=
    if decide (β ⊑ α) then depo_wsat_dead M sm β Pm
    else depo_wsat M sm d' β Bm Pm.
  Local Definition borrow_wsat_ret M sm Dm d α : iProp Σ :=
    ∃ Dm', ⌜filter_lt d Dm' = filter_lt d Dm⌝ ∗ depo_stm_tok Dm' ∗
      [∗ map] '((d', β)', Bm, Pm) ∈ filter_ge d Dm',
        depo_wsat_ret M sm d' α β Bm Pm.

  (** Retrieve from [borrow_wsat_ret] using [lend_dtok] *)
  Local Lemma lend_dtok_ret_retrieve {Dm d d' α β Px} : d ≤ d' → β ⊑ α →
    lend_dtok d' β Px -∗ modw M (borrow_wsat_ret M sm Dm d α) (sm Px).
  Proof.
    move=> ??. iIntros "[%[% l]] [%Dm'[%[● Dm']]]".
    iDestruct (depo_stm_lend_agree with "● l") as (Bm Pm Px' eq ?) "#eqv".
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
  Local Lemma bor_wsat_retrieve {Dm d α β Px b} : β ⊑ α →
    [†β] -∗ bor_wsat sm d β (Px, b) -∗
      modw M (borrow_wsat_ret M sm Dm (S d) α) (sm Px).
  Proof.
    move=> ?. iIntros "† B". case b=> [|q|?]/=; [done|..].
    { iDestruct (lft_live_dead with "B †") as "[]". }
    iDestruct "B" as (??) "l". iApply (lend_dtok_ret_retrieve with "l"); [lia|].
    etrans; [|done]. apply lft_incl_meet_l.
  Qed.
  (** Retrieve from [bor_wsat]s *)
  Local Lemma bor_wsats_retrieve {Dm d α β Bl} : β ⊑ α →
    [†β] -∗ ([∗ list] B ∈ Bl, bor_wsat sm d β B) -∗
      modw M (borrow_wsat_ret M sm Dm (S d) α)
        ([∗ list] '(Px, _) ∈ Bl, sm Px)%I.
  Proof.
    move=> ?. elim: Bl; [by iIntros|]. move=>/= [??]Bl IH. iIntros "#† [B Bl]".
    iMod (IH with "† Bl") as "$". by iApply bor_wsat_retrieve.
  Qed.
  (** Retrieve from [depo_wsat] *)
  Local Lemma depo_wsat_retrieve {Dm d α β Bm Pm} : β ⊑ α →
    [†β] -∗ depo_wsat M sm d β Bm Pm -∗
      modw M (borrow_wsat_ret M sm Dm (S d) α) (depo_wsat_dead M sm β Pm)%I.
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
        depo_wsat M sm d' β Bm Pm else emp) -∗
      modw M (borrow_wsat_ret M sm Dm (S d) α)
        ([∗ list] D ∈ Dl,
          if decide (dep_of D = d) then let '((d', β)', Bm, Pm) := D in
            depo_wsat_ret M sm d' α β Bm Pm else emp)%I.
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
    [†α] -∗ borrow_wsat' M sm (filter_eq d Dm) -∗
      borrow_wsat_ret M sm Dm (S d) α -∗
      M (borrow_wsat_ret M sm Dm d α).
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
    borrow_wsat' M sm (filter_lt (S d) Dm) ⊣⊢
      borrow_wsat' M sm (filter_eq d Dm) ∗ borrow_wsat' M sm (filter_lt d Dm).
  Proof.
    rewrite /borrow_wsat' (big_sepM_filter_complement (λ iD, dep_of iD.2 = d)).
    do 2 f_equiv; rewrite map_filter_filter;
      apply (map_filter_ext (M:=gmap _))=>/=; lia.
  Qed.
  (** Retrieve from [borrow_wsat'] on [filter_lt] *)
  Local Lemma borrow_wsat_lt_retrieve {Dm d α} :
    [†α] -∗ borrow_wsat' M sm (filter_lt d Dm) -∗
      borrow_wsat_ret M sm Dm d α -∗ M (borrow_wsat_ret M sm Dm 0 α).
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
  Local Lemma lend_dtok_retrieve {d α Px} :
    [†α] -∗ lend_dtok d α Px -∗ modw M (borrow_wsat M sm) (sm Px).
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
  Lemma lend_tok_retrieve {α Px} :
    [†α] -∗ lend_tok α Px -∗ modw M (borrow_wsat M sm) (sm Px).
  Proof.
    rewrite lend_tok_unseal. iIntros "† [%α'[⊑[%d l]]]".
    iDestruct (lft_sincl_dead with "⊑ †") as "†".
    by iApply (lend_dtok_retrieve with "† l").
  Qed.

  (** [depo_wsat] with a live lifetime token *)
  Local Lemma depo_wsat_tok {d α Bm Pm q} :
    q.[α] -∗ depo_wsat M sm d α Bm Pm -∗ q.[α] ∗ depo_wsat_in M sm d α Bm Pm.
  Proof.
    iIntros "α [$|[† _]]"; [done|].
    iDestruct (lft_live_dead with "α †") as "[]".
  Qed.

  (** [bor_wsat] is non-expansive over the borrower state *)
  Local Instance bor_wsat_ne_st {d α} : NonExpansive (bor_wsat sm d α).
  Proof.
    move=> ?[?[|?|?]][?[|?|?]][//=eqv /leibniz_equiv_iff].
    { by rewrite eqv. } { by move=> [<-]. }
    move=> [<-]. unfold lend_dtok, lend_itok. do 9 f_equiv.
    apply singleton_ne. split=>/=; [done|]. by rewrite eqv.
  Qed.

  (** Update the borrower state to [Open q] *)
  Local Lemma bor_open_core {i j d α Px b q} :
    q.[α] -∗ bor_itok i j d α (Px, b) =[borrow_wsat M sm]=∗
      obor_tok α q Px ∗ bor_wsat sm d α (Px, b).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[α α'] b [%Dm[● Dm]]".
    iDestruct (depo_stm_bor_agree with "● b") as (Bm Qm [Px' b'] ??) "#eqv".
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
  (** Open a borrower *)
  Lemma bor_tok_open {α q Px} :
    q.[α] -∗ bor_tok α Px -∗
      modw M (borrow_wsat M sm) (obor_tok α q Px ∗ sm Px).
  Proof.
    rewrite bor_tok_unseal. iIntros "α [†|b]".
    { by iDestruct (lft_live_dead with "α †") as "[]". }
    iDestruct "b" as (????) "[#⊑ b]".
    iMod (lft_sincl_live_acc with "⊑ α") as (r) "[α' →α]".
    iDestruct "b" as "[b|[%β[#† r]]]".
    - iMod (bor_open_core with "α' b") as "[o $]". iApply modw_fold.
      iApply (obor_tok_lft with "⊑ →α o").
    - iMod (bor_open_core with "α' r") as "[o [%[_ l]]]".
      iDestruct (obor_tok_lft with "⊑ →α o") as "$". iApply modw_fold.
      iApply (lend_dtok_retrieve with "[] l").
      iApply (lft_sincl_dead with "[] †"). iApply lft_sincl_meet_r.
  Qed.

  (** Open borrow token with the depth and real lifetime explicit *)
  Local Definition obor_dtok d α α' q Px : iProp Σ :=
    ∃ i j r, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗ (r/2).[α'] ∗
      bor_itok i j d α' (Px, Open (r/2)).
  (** Turn [obor_tok] into [obor_dtok] *)
  Local Lemma obor_tok_dtok {α q Px} :
    obor_tok α q Px ⊢ ∃ d α', α ⊑□ α' ∗ obor_dtok d α α' q Px.
  Proof.
    rewrite obor_tok_unseal. iDestruct 1 as (α' r ???) "[#⊑ b]". iExists _, _.
    iFrame "⊑". by iExists _, _, _.
  Qed.

  (** Turn [obor_dtok] to a reborrower using [lend_dtok] *)
  Local Lemma obor_dtok_reborrow {d α α' q Px β d'} : d < d' →
    obor_dtok d α α' q Px -∗ lend_dtok d' (α' ⊓ β) Px =[borrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α Px).
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
    { iIntros "†". rewrite bor_tok_unseal. iRight. iExists _, _, _, _.
      iFrame "⊑". iRight. iExists _. iFrame. }
    iExists _. iFrame "●". iApply "→Dm". iLeft. iSplitR "→Pm".
    { iApply "→Bm". iExists _. iSplit; [done|]. by iExists _, _. }
    iIntros "† big". iApply ("→Pm" with "†").
    iApply (big_sepM_insert_override_1 with "big"); [done|].
    rewrite prod_equivI /=. iDestruct "eqv" as "[eqv _]". case B'=>/= ??.
    iRewrite "eqv". by iIntros.
  Qed.

  (** Lemma for [obor_tok_merge_subdiv] *)
  Local Lemma obor_toks_dtoks_bound {αqPl β} :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ obor_tok α q Px) ⊢ ∃ d γ, β ⊑□ γ ∗
      [∗ list] '(α, q, Px)' ∈ αqPl, ∃ d' α' γ',
        ⌜d' < d ∧ γ = α' ⊓ γ'⌝ ∗ obor_dtok d' α α' q Px.
  Proof.
    elim: αqPl=>/=.
    { iIntros. iExists 0, ⊤. iSplit; [iApply lft_sincl_top|done]. }
    move=> [α[Px q]] αqPl ->. rewrite obor_tok_dtok.
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
  Lemma obor_tok_merge_subdiv αqPl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ obor_tok α q Px) -∗
    ([∗ list] Qx ∈ Qxl, sm Qx) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗
      M ([∗ list] '(_, _, Px)' ∈ αqPl, sm Px)%I)
      =[borrow_wsat M sm]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ [∗ list] Qx ∈ Qxl, bor_tok β Qx.
  Proof.
    rewrite/= obor_toks_dtoks_bound. iIntros "[%d[%γ[#⊑ αqPl]]] Qxl →P".
    iMod (bor_lend_tok_new_list' d γ Qxl ((λ '(_, _, Px)', Px) <$> αqPl)
      with "Qxl [→P]") as "[bl ll]"=>/=.
    { iIntros "† Qxl". iDestruct (lft_sincl_dead with "⊑ †") as "†".
      rewrite big_sepL_fmap. iApply ("→P" with "† Qxl"). }
    iSplitR "bl"; last first.
    { iModIntro. iApply (big_sepL_impl with "bl"). iIntros "!> %% _".
      by iApply bor_tok_lft. }
    iInduction αqPl as [|[α[q Px]]αqPl] "IH"=>/=; [done|].
    iDestruct "αqPl" as "[big αqPl]". iDestruct "big" as (???[?->]) "o".
    iDestruct "ll" as "[l ll]". iMod ("IH" with "αqPl ll") as "$".
    iMod (obor_dtok_reborrow with "o l") as "[$ _]"; [lia|done].
  Qed.
  (** Subdivide a borrower *)
  Lemma obor_tok_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ obor_tok α q Px -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗ M (sm Px))
      =[borrow_wsat M sm]=∗ q.[α] ∗ [∗ list] Qx ∈ Qxl, bor_tok β Qx.
  Proof.
    iIntros "⊑ o Qxl →P".
    iMod (obor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→P]")
      as "[[$_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obor_tok_close {α q Px} :
    obor_tok α q Px -∗ sm Px =[borrow_wsat M sm]=∗ q.[α] ∗ bor_tok α Px.
  Proof.
    iIntros "o Px".
    iMod (obor_tok_subdiv [Px] with "[] o [Px] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Reborrow a borrower *)
  Lemma obor_tok_reborrow {α q Px} β :
    obor_tok α q Px -∗ sm Px =[borrow_wsat M sm]=∗
      q.[α] ∗ bor_tok (α ⊓ β) Px ∗ ([†β] -∗ bor_tok α Px).
  Proof.
    rewrite obor_tok_dtok. iIntros "[%d[%α'[#? o]]] Px".
    iMod (bor_lend_tok_new_list' (S d) (α' ⊓ β) [Px] [Px] with "[Px] []")
      as "[[b _] [l _]]"; [by iFrame|by iIntros|].
    iMod (obor_dtok_reborrow with "o l") as "[$$]"; [lia|]. iModIntro.
    iApply (bor_tok_lft with "[] b"). by iApply lft_sincl_meet_mono_l.
  Qed.
  Lemma bor_tok_reborrow {α q Px} β :
    q.[α] -∗ bor_tok α Px -∗ modw M (borrow_wsat M sm)
      (q.[α] ∗ bor_tok (α ⊓ β) Px ∗ ([†β] -∗ bor_tok α Px)).
  Proof.
    iIntros "α b". iMod (bor_tok_open with "α b") as "[o Px]".
    by iMod (obor_tok_reborrow with "o Px").
  Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc `{!borrowGpreS FML Σ} :
  ⊢ |==> ∃ _ : borrowGS FML Σ, ∀ M sm, borrow_wsat M sm.
Proof.
  iMod (own_alloc (● (∅ : gmap _ _) : borrowRF_def FML $ri Σ)) as (γ) "●";
    [by apply auth_auth_valid|].
  iModIntro. iExists (BorrowGS _ _ _ γ). iIntros (??).
  rewrite borrow_wsat_unseal. iExists ∅. unfold borrow_wsat'. by iFrame.
Qed.
