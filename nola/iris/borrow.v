(** * Borrowing machinery *)

From nola.util Require Export prod.
From nola.bi Require Export modw.
From nola.bi Require Import order gmap.
From nola.iris Require Export iprop lft.
From iris.bi.lib Require Import cmra.
From iris.algebra Require Import excl agree gmap auth.
From iris.proofmode Require Import proofmode.
Import ProdNotation FunPNotation iPropAppNotation LftNotation UpdwNotation.

Implicit Type (FML : oFunctor) (α : lft) (q : Qp).

(** ** Ghost state *)

(** ID for a borrower/deposit/lender *)
Local Definition depo_id := nat.
Local Definition bor_id := nat.
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
Local Definition bor_stl FML Σ := list (bor_stOF FML $oi Σ).
(** State of the lenders *)
Local Definition lend_stm FML Σ := gmap lend_id (FML $oi Σ).
(** State of a deposit *)
Local Definition depo_st FML Σ : Type :=
  lft *' bor_stl FML Σ *' lend_stm FML Σ.
(** State of the deposits *)
Local Notation depo_stl FML Σ := (list (depo_st FML Σ)).

(** Algebra for a borrower *)
Local Definition borRF FML := exclRF (bor_stOF FML).
(** Algebra for a lender *)
Local Definition lendRF FML := exclRF FML.
(** Algebra for a deposit *)
#[warning="-redundant-canonical-projection"]
Local Canonical lftO := leibnizO lft.
Local Definition depoRF FML : rFunctor :=
  agreeR lftO * gmapRF bor_id (borRF FML) * gmapRF lend_id (lendRF FML).

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
  borrowGS_lft :: lftG Σ;
  borrowGS_borrow : inG Σ (borrowRF FML $ri Σ);
  borrow_name : gname;
}.
Local Existing Instance borrowGS_borrow.
Local Instance inG_borrow_def `{!inG Σ (borrowRF FML $ri Σ)} :
  inG Σ (borrowRF_def FML $ri Σ).
Proof. rewrite -borrowRF_unseal. exact _. Qed.
Definition borrowΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[lftΣ; GFunctor (borrowRF FML)].
#[export] Instance subG_borrow
  `{!oFunctorContractive FML, !subG (borrowΣ FML) Σ} : borrowGpreS FML Σ.
Proof. solve_inG. Qed.

Section borrow.
  Context `{!borrowGS FML Σ}.
  Implicit Type (M : iProp Σ → iProp Σ) (sm : FML $oi Σ -d> iProp Σ)
    (Px Qx : FML $oi Σ) (Pxl Qxl : list (FML $oi Σ))
    (D : depo_st FML Σ) (Dl : depo_stl FML Σ)
    (B : bor_stOF FML $oi Σ) (Bl : bor_stl FML Σ) (Lm : lend_stm FML Σ).

  (** ** Tokens *)

  (** General borrower token *)
  Local Definition bor_jtok i j α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, {[j := Excl B]}, ε)]}).

  (** Borrower token

    It may be a dead lifetime token, a closed borrower, or a retrieving
    reborrower *)
  Local Definition bor_tok_def α Px : iProp Σ :=
    [†α] ∨ ∃ α' i j, α ⊑□ α' ∗
      (bor_jtok i j α' (Px, Clsd) ∨
      ∃ β, [†β] ∗ bor_jtok i j α' (Px, Rebor β)).
  Local Lemma bor_tok_aux : seal bor_tok_def. Proof. by eexists. Qed.
  Definition bor_tok := bor_tok_aux.(unseal).
  Local Lemma bor_tok_unseal : bor_tok = bor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Open borrower token

    It keeps a live lifetime token [(r/2).[α']] at hand *)
  Local Definition obor_itok i α' α q Px : iProp Σ :=
    ∃ j r, α ⊑□ α' ∗ (r.[α'] -∗ q.[α]) ∗ (r/2).[α'] ∗
      bor_jtok i j α' (Px, Open (r/2)).
  Local Definition obor_tok_def α q Px : iProp Σ :=
    ∃ i α', obor_itok i α' α q Px.
  Local Lemma obor_tok_aux : seal obor_tok_def. Proof. by eexists. Qed.
  Definition obor_tok := obor_tok_aux.(unseal).
  Local Lemma obor_tok_unseal : obor_tok = obor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Lender token *)
  Local Definition lend_ktok i k α Px : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, ε, {[k := Excl Px]})]}).
  Local Definition lend_itok i α Px : iProp Σ :=
    ∃ k, lend_ktok i k α Px.
  Local Definition lend_tok_def α Px : iProp Σ :=
    ∃ α', α' ⊑□ α ∗ ∃ i, lend_itok i α' Px.
  Local Lemma lend_tok_aux : seal lend_tok_def. Proof. by eexists. Qed.
  Definition lend_tok := lend_tok_aux.(unseal).
  Local Lemma lend_tok_unseal : lend_tok = lend_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Borrower and lender tokens are non-expansive *)
  Local Instance bor_itok_ne {i j α} : NonExpansive (bor_jtok i j α).
  Proof.
    unfold bor_jtok=> ????. do 2 f_equiv. apply singleton_ne.
    do 2 apply pair_ne=>//. apply singleton_ne. by f_equiv.
  Qed.
  #[export] Instance bor_tok_ne {α} : NonExpansive (bor_tok α).
  Proof. rewrite bor_tok_unseal. solve_proper. Qed.
  #[export] Instance bor_tok_proper {α} : Proper ((≡) ==> (⊣⊢)) (bor_tok α).
  Proof. apply ne_proper, _. Qed.
  Local Instance obor_itok_ne {i α' α q} :
    NonExpansive (obor_itok i α' α q).
  Proof. solve_proper. Qed.
  #[export] Instance obor_tok_ne {α q} : NonExpansive (obor_tok α q).
  Proof. rewrite obor_tok_unseal. solve_proper. Qed.
  #[export] Instance obor_tok_proper {α q} :
    Proper ((≡) ==> (⊣⊢)) (obor_tok α q).
  Proof. apply ne_proper, _. Qed.
  Local Instance lend_ktok_ne {i k α} : NonExpansive (lend_ktok i k α).
  Proof.
    unfold lend_ktok=> ????. do 2 f_equiv. apply singleton_ne.
    apply pair_ne=>//. apply singleton_ne. by f_equiv.
  Qed.
  Local Instance lend_itok_ne {i α} : NonExpansive (lend_itok i α).
  Proof. solve_proper. Qed.
  #[export] Instance lend_tok_ne {α} : NonExpansive (lend_tok α).
  Proof. rewrite lend_tok_unseal. solve_proper. Qed.
  #[export] Instance lend_tok_proper {α} : Proper ((≡) ==> (⊣⊢)) (lend_tok α).
  Proof. apply ne_proper, _. Qed.

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
    iDestruct "b" as (???) "[#? b]". iRight. iExists _, _, _. iFrame "b".
    by iApply lft_sincl_trans.
  Qed.
  Lemma obor_tok_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor_tok α q Px -∗ obor_tok β r Px.
  Proof.
    rewrite obor_tok_unseal. iIntros "#? →β".
    iDestruct 1 as (? α' ??) "[#?[→α o]]". iExists _, _, _, _. iFrame "o".
    iSplit; [by iApply lft_sincl_trans|]. iIntros "α'". iApply "→β".
    by iApply "→α".
  Qed.
  Lemma lend_tok_lft {α β Px} : α ⊑□ β -∗ lend_tok α Px -∗ lend_tok β Px.
  Proof.
    rewrite lend_tok_unseal. iIntros "#? [%α'[#? l]]". iExists _. iFrame "l".
    by iApply lft_sincl_trans.
  Qed.

  (** Lemma for [to_bor_itoks] *)
  Local Lemma bor_insert_op {i j α B Bm} :
    Bm !! j = None →
    (◯ {[i := (to_agree α, Excl <$> <[j:=B]> Bm, ε)]} : borrowRF_def _ $ri _) ≡
      ◯ {[i := (to_agree α, {[j:=Excl B]}, ε)]} ⋅
      ◯ {[i := (to_agree α, Excl <$> Bm, ε)]}.
  Proof.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp| |done].
    rewrite insert_singleton_op; [done|]. by rewrite lookup_fmap eq.
  Qed.
  (** Get [bor_jtok]s out of [own] *)
  Local Lemma to_bor_jtoks {i α Bm} :
    own borrow_name (◯ {[i := (to_agree α, Excl <$> Bm, ε)]}) ⊢
      [∗ map] j ↦ B ∈ Bm, bor_jtok i j α B.
  Proof.
    induction Bm as [|j B Bl' ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH bor_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** Lemma for [to_lend_ktoks] *)
  Local Lemma lend_insert_op {i k α Px Lm} :
    Lm !! k = None →
    (◯ {[i := (to_agree α, ε, Excl <$> <[k:=Px]> Lm)]} : borrowRF_def _ $ri _) ≡
      ◯ {[i := (to_agree α, ε, {[k:=Excl Px]})]} ⋅
      ◯ {[i := (to_agree α, ε, Excl <$> Lm)]}.
    move=> eq. rewrite fmap_insert -auth_frag_op. f_equiv. rewrite singleton_op.
    apply: singletonM_proper.
    split; [split|]=>/=; [by rewrite agree_idemp|done|].
    rewrite insert_singleton_op; [done|]. by rewrite lookup_fmap eq.
  Qed.
  (** Get [lend_ktok]s out of [own] *)
  Local Lemma to_lend_ktoks {i α Lm} :
    own borrow_name (◯ {[i := (to_agree α, ε, Excl <$> Lm)]}) ⊢
      [∗ map] k ↦ Px ∈ Lm, lend_ktok i k α Px.
  Proof.
    induction (Lm : gmap _ _) as [|k Px Lm' ? IH] using map_ind.
    { rewrite big_sepM_empty. by iIntros. }
    rewrite big_sepM_insert; [|done]. rewrite -IH lend_insert_op; [|done].
    iIntros "[$$]".
  Qed.

  (** [depo_st] to [depoRF] *)
  Local Definition of_depo_st (D : depo_st FML Σ) : depoRF FML $ri Σ :=
    let '(α, Bl, Lm)' := D in
    (to_agree α, Excl <$> list_to_gmap Bl, Excl <$> Lm).
  (** Auxiliary definition for performance *)
  Local Definition depoR FML Σ : cmra :=
    (agreeR lftO *
      gmapR bor_id (borRF FML $ri Σ) * gmapR lend_id (lendRF FML $ri Σ))%type.
  Local Definition of_depo_st' : depo_st FML Σ → depoR FML Σ := of_depo_st.

  (** [depo_stk] to [gmap] over [depoRF] *)
  Local Definition of_depo_stl (Dl : depo_stl FML Σ)
    : gmapR depo_id (depoRF FML $ri Σ) := list_to_gmap (of_depo_st <$> Dl).
  (** Token for [depo_stl] *)
  Local Definition depo_stl_tok Dl : iProp Σ :=
    own borrow_name (● of_depo_stl Dl).

  (** [!!] over [of_depo_stl] *)
  Local Lemma lookup_of_depo_stl {Dl i} :
    of_depo_stl Dl !! i = of_depo_st <$> (Dl !! i).
  Proof. by rewrite lookup_list_to_gmap list_lookup_fmap. Qed.
  (** [of_depo_stl] over [insert] *)
  Local Lemma of_depo_stl_insert {Dl i D} : i < length Dl →
    of_depo_stl (<[i := D]> Dl) = <[i := of_depo_st D]> (of_depo_stl Dl).
  Proof.
    move=> ?. rewrite /of_depo_stl list_fmap_insert.
    rewrite list_to_gmap_insert; by [|rewrite length_fmap].
  Qed.

  (** Create [bor_jtok]s and [lend_itok]s w.r.t. [depo_stl_tok] *)
  Local Lemma depo_stl_bor_lend_new {Dl α} Pxl Qxl :
    let i := length Dl in let Bl := (λ Px, (Px, Clsd)) <$> Pxl in
    depo_stl_tok Dl -∗ |==>
      depo_stl_tok (Dl ++ [(α, Bl, map_by _ Qxl)']) ∗
      ([∗ list] B ∈ Bl, ∃ j, bor_jtok i j α B) ∗
      [∗ list] Qx ∈ Qxl, lend_itok i α Qx.
  Proof.
    move=> ? Bl. iIntros "●".
    iMod (own_update with "●") as "[$[b l]]"; last first.
    { iModIntro. iSplitL "b".
      - erewrite to_bor_jtoks, (big_sepM_list_to_gmap Bl). iStopProof.
        do 3 f_equiv. iIntros "$".
      - iStopProof. erewrite to_lend_ktoks. apply big_sepM_map_by'. }
    rewrite -auth_frag_op singleton_op.
    have <- : ∀ x y, ((to_agree α, x, y) : depoRF _ $ri _) ≡
      ((to_agree α, x, ε) : depoRF _ $ri _) ⋅ (to_agree α, ε, y).
    { split; [split|]=>/=; by
        [rewrite agree_idemp|rewrite left_id|rewrite right_id]. }
    rewrite /of_depo_stl fmap_snoc list_to_gmap_snoc length_fmap.
    apply auth_update_alloc, alloc_singleton_local_update.
    - by rewrite lookup_of_depo_stl fmap_None lookup_ge_None.
    - split; [split|]=>/=; [done|by apply: gmap_fmap_valid..].
  Qed.

  (** Lemmas for [depo_stl_lend_agree] and [depo_stl_bor_agree] *)
  Local Lemma depo_stl_own_agree {Dl i α Bxm Pxm n} :
    ✓{n} (● of_depo_stl Dl ⋅ ◯ {[i := (to_agree α, Bxm, Pxm)]}
      : borrowRF_def _ $ri _) →
    ∃ Bl Lm, Dl !! i = Some (α, Bl, Lm)' ∧
      Bxm ≼{n} Excl <$> list_to_gmap Bl ∧ Pxm ≼{n} Excl <$> Lm.
  Proof.
    move=> /auth_both_validN/proj1/singleton_includedN_l.
    move=> [?[/Some_equiv_eq[?[++]] /Some_includedN_total +]].
    rewrite lookup_of_depo_stl=> /fmap_Some[[?[??]][? ->]]<-.
    move=> /prod_includedN[/prod_includedN/=[+ ?] ?].
    move=> /to_agree_includedN/leibniz_equiv_iff ?. subst. by eexists _, _.
  Qed.

  (** Agreement between [depo_stl_tok] and [lend_itok] *)
  Local Lemma depo_stl_lend_agree' {Dl i k α Px n} :
    ✓{n} (● of_depo_stl Dl ⋅ ◯ {[i := (to_agree α, ε, {[k := Excl Px]})]}
      : borrowRF_def _ $ri _) → ∃ Bl Lm Px',
      Dl !! i = Some (α, Bl, Lm)' ∧ Lm !! k = Some Px' ∧ Px' ≡{n}≡ Px.
  Proof.
    move=> /depo_stl_own_agree[?[?[?[_ +]]]].
    move=> /singleton_includedN_l
      [?[/Some_equiv_eq[?[/lookup_fmap_Some[Px'[<-?]]<-]]/Excl_includedN ?]].
    by eexists _, _, _.
  Qed.
  Local Lemma depo_stl_lend_agree {Dl i k α Px} :
    depo_stl_tok Dl -∗ lend_ktok i k α Px -∗ ∃ Bl Lm Px',
      ⌜Dl !! i = Some (α, Bl, Lm)'⌝ ∧ ⌜Lm !! k = Some Px'⌝ ∧ Px' ≡ Px.
  Proof.
    iIntros "● l". iDestruct (own_valid_2 with "● l") as "?". iStopProof.
    uPred.unseal. by split=> ?? _ /depo_stl_lend_agree'.
  Qed.

  (** Delete a lender w.r.t. [depo_stl_tok] *)
  Local Lemma depo_stl_lend_delete {Dl i k α Bl Lm Px} :
    Dl !! i = Some (α, Bl, Lm)' →
    depo_stl_tok Dl -∗ lend_ktok i k α Px ==∗
      depo_stl_tok (<[i := (α, Bl, delete k Lm)']> Dl).
  Proof.
    move=> eq. iIntros "● l". iMod (own_update_2 with "● l") as "[$_]"; [|done].
    apply auth_update. rewrite of_depo_stl_insert; [|by apply: lookup_lt_Some].
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { by rewrite lookup_of_depo_stl eq. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_delete. apply: delete_local_update; last first.
    { by rewrite lookup_singleton. } exact _.
  Qed.

  (** Add lenders w.r.t. [depo_stl_tok] *)
  Local Lemma depo_stl_lend_add' {α Bl Lm Qxl} :
    (Some (of_depo_st' (α, Bl, Lm)'), None) ~l~>
      (Some (of_depo_st' (α, Bl, map_with Lm Qxl)'),
        Some (to_agree α, ε, Excl <$> map_without Lm Qxl)).
  Proof.
    apply local_update_unital=> n ?[/=??]. rewrite (left_id None)=> <-. split.
    { split; [done|]. by apply: gmap_fmap_valid. }
    rewrite -Some_op. f_equiv.
    split; [split|]=>/=; [by rewrite agree_idemp|by rewrite left_id|].
    rewrite gmap_op_disj; [|by apply map_disjoint_fmap, map_without_disj].
    by rewrite -map_fmap_union -map_with_without.
  Qed.
  Local Lemma depo_stl_lend_add {Dl i α Bl Lm} Qxl :
    Dl !! i = Some (α, Bl, Lm)' →
    depo_stl_tok Dl ==∗
      depo_stl_tok (<[i := (α, Bl, map_with Lm Qxl)']> Dl) ∗
      [∗ map] k ↦ Qx ∈ map_without Lm Qxl, lend_ktok i k α Qx.
  Proof.
    move=> eq. iIntros "●". iMod (own_update with "●") as "[$ ?]"; last first.
    { iModIntro. by iApply to_lend_ktoks. }
    rewrite of_depo_stl_insert; [|by apply: lookup_lt_Some].
    apply auth_update_alloc, gmap_local_update. move=> i'.
    case: (decide (i = i'))=> [<-|?]; last first.
    { rewrite lookup_insert_ne; [|done]. by rewrite lookup_singleton_ne. }
    rewrite lookup_empty lookup_of_depo_stl eq !lookup_insert.
    exact depo_stl_lend_add'.
  Qed.

  (** Agreement between [depo_stl_tok] and [bor_jtok] *)
  Local Lemma depo_stl_bor_agree' {Dl i j α B n} :
    ✓{n} (● of_depo_stl Dl ⋅ ◯ {[i := (to_agree α, {[j := Excl B]}, ε)]}
      : borrowRF_def _ $ri _) → ∃ Bl Lm B',
      Dl !! i = Some (α, Bl, Lm)' ∧ Bl !! j = Some B' ∧ B' ≡{n}≡ B.
  Proof.
    move=> /depo_stl_own_agree[?[?[?[+ _]]]].
    move=> /singleton_includedN_l[?
      [/Some_equiv_eq[?[/lookup_fmap_Some[B'[<- +]]<-]]/Excl_includedN incl]].
    rewrite lookup_list_to_gmap=> ?. by eexists _, _, _.
  Qed.
  Local Lemma depo_stl_bor_agree {Dl i j α B} :
    depo_stl_tok Dl -∗ bor_jtok i j α B -∗ ∃ Bl Lm B',
      ⌜Dl !! i = Some (α, Bl, Lm)'⌝ ∧ ⌜Bl !! j = Some B'⌝ ∧ B' ≡ B.
  Proof.
    iIntros "● B". iDestruct (own_valid_2 with "● B") as "?". iStopProof.
    uPred.unseal. by split=> n ? _ /depo_stl_bor_agree'.
  Qed.

  (** Update the borrower state w.r.t. [depo_stl_tok] *)
  Local Lemma depo_stl_bor_stupd {Dl i j α Bl Lm B B'} :
    Dl !! i = Some (α, Bl, Lm)' →
    depo_stl_tok Dl -∗ bor_jtok i j α B ==∗
      depo_stl_tok (<[i := (α, <[j := B']> Bl, Lm)']> Dl) ∗
      bor_jtok i j α B'.
  Proof.
    move=> eq. iIntros "● B".
    iDestruct (depo_stl_bor_agree with "● B") as (??? eq' eq'') "#_".
    move: eq' eq''. rewrite eq. move=> [<-_] ?.
    iMod (own_update_2 with "● B") as "[$$]"; [|done].
    apply auth_update. rewrite of_depo_stl_insert; [|by apply: lookup_lt_Some].
    eapply singleton_local_update. { by rewrite lookup_of_depo_stl eq. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    rewrite list_to_gmap_insert; [|by apply: lookup_lt_Some].
    rewrite fmap_insert. apply: singleton_local_update.
    { rewrite lookup_fmap_Some. eexists _.
      split; by [|rewrite lookup_list_to_gmap]. }
    by apply exclusive_local_update.
  Qed.

  (** ** World satisfactions *)

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat sm i α B : iProp Σ :=
    let '(Qx, b) := B in match b with
    | Clsd => sm Qx | Open q => q.[α]
    | Rebor β => ⌜β ⊑ α⌝ ∗ ∃ i', ⌜i < i'⌝ ∗ lend_itok i' β Qx
    end.

  (** World satisfaction for a deposit, borrowed or retrieved *)
  Local Definition depo_wsat_bor M sm i α Bl Lm : iProp Σ :=
    ([∗ list] B ∈ Bl, bor_wsat sm i α B) ∗
    ([†α] -∗ ([∗ list] '(Qx, _) ∈ Bl, sm Qx) -∗ M ([∗ map] Px ∈ Lm, sm Px)%I).
  Local Definition depo_wsat_ret M sm α Lm : iProp Σ :=
    [†α] ∗ M ([∗ map] Px ∈ Lm, sm Px)%I.
  Local Definition depo_wsat M sm i α Bl Lm : iProp Σ :=
    depo_wsat_bor M sm i α Bl Lm ∨ depo_wsat_ret M sm α Lm.

  (** Constraint on [sm] *)
  Local Definition sem_ne sm : iProp Σ :=
    □ (∀ Px Qx, Px ≡ Qx -∗ sm Px -∗ sm Qx).

  (** World satisfaction for the borrowing machinery *)
  Local Definition borrow_lwsat M sm Dl : iProp Σ :=
    sem_ne sm ∗ depo_stl_tok Dl ∗
      [∗ list] i ↦ '(α, Bl, Lm)' ∈ Dl, depo_wsat M sm i α Bl Lm.
  Local Definition borrow_wsat_def M sm : iProp Σ :=
    ∃ Dl, borrow_lwsat M sm Dl.
  Local Definition borrow_wsat_aux : seal borrow_wsat_def.
  Proof. by eexists. Qed.
  Definition borrow_wsat := borrow_wsat_aux.(unseal).
  Local Lemma borrow_wsat_unseal : borrow_wsat = borrow_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [borrow_wsat] is non-expansive *)
  Local Instance sem_ne_ne : NonExpansive sem_ne.
  Proof. solve_proper. Qed.
  Local Instance bor_wsat_ne {n} :
    Proper ((≡{n}≡) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) bor_wsat.
  Proof. solve_proper. Qed.
  Local Instance depo_wsat_ne {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (=) ==> (=) ==> (=) ==>
      (=) ==> (≡{n}≡)) depo_wsat.
  Proof.
    move=> ?? eqv ?????<-??<-??<-??<-.
    unfold depo_wsat, depo_wsat_bor, depo_wsat_ret.
    (repeat f_equiv); [done|..]; apply eqv; solve_proper.
  Qed.
  #[export] Instance borrow_wsat_ne {n} :
    Proper (((≡{n}≡) ==> (≡{n}≡)) ==> (≡{n}≡) ==> (≡{n}≡)) borrow_wsat.
  Proof.
    rewrite borrow_wsat_unseal /borrow_wsat_def /borrow_lwsat. move=> ??????.
    repeat f_equiv=>//. by apply depo_wsat_ne.
  Qed.
  #[export] Instance borrow_wsat_proper `{!NonExpansive M} :
    Proper ((≡) ==> (≡)) (borrow_wsat M).
  Proof. apply ne_proper=> ????. apply borrow_wsat_ne=>//. solve_proper. Qed.

  (** [borrow_wsat] is monotone over the modality *)
  Local Instance depo_wsat_mono :
    Mono (OT:=_-p>_ : bi) (OT':=_-p>_-p>_-p>_-p>_-p>_ : bi) depo_wsat.
  Proof.
    move=> ?? to ?????. unfold depo_wsat, depo_wsat_bor, depo_wsat_ret.
    repeat f_equiv; exact: to.
  Qed.
  #[export] Instance borrow_wsat_mono :
    Mono (OT:=_-p>_ : bi) (OT':=_-p>_ : bi) borrow_wsat.
  Proof.
    rewrite borrow_wsat_unseal /borrow_wsat_def /borrow_lwsat. move=> ????.
    repeat f_equiv. by apply: depo_wsat_mono.
  Qed.

  (** ** Proof rules *)

  Context `{!GenUpd M, !FromBUpd M}.

  (** Create new borrowers and lenders *)
  Local Lemma bor_lend_tok_new_list' {sm Dl} α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, sm Px) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, sm Px) -∗ M ([∗ list] Qx ∈ Qxl, sm Qx)%I) -∗
    borrow_lwsat M sm Dl ==∗ ∃ D,
      borrow_lwsat M sm (Dl ++ [D]) ∗ ([∗ list] Px ∈ Pxl, bor_tok α Px) ∗
      [∗ list] Qx ∈ Qxl, lend_itok (length Dl) α Qx.
  Proof.
    rewrite bor_tok_unseal. iIntros "Pxl →Qxl ($ & ● & Dl)".
    iMod (depo_stl_bor_lend_new Pxl Qxl with "●") as "($ & b & $)".
    iModIntro. iSplitR "b"; last first.
    { iStopProof. rewrite big_sepL_fmap. do 3 f_equiv.
      iIntros "[% b]". iRight. iExists _, _, _.
      iSplitR; by [iApply lft_sincl_refl|iLeft]. }
    rewrite big_sepL_snoc /=. iFrame "Dl". iLeft.
    iSplitL "Pxl"; [|rewrite ?big_sepM_map_by]; by rewrite big_sepL_fmap.
  Qed.

  (** Create new borrowers and lenders *)
  Lemma bor_lend_tok_new_list {sm} α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, sm Px) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, sm Px) -∗ M ([∗ list] Qx ∈ Qxl, sm Qx)%I)
      =[borrow_wsat M sm]=∗
      ([∗ list] Px ∈ Pxl, bor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, lend_tok α Qx.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "Pxl →Qxl [% W]".
    iMod (bor_lend_tok_new_list' with "Pxl →Qxl W") as (?) "($ & $ & ?)".
    iModIntro. iStopProof. do 3 f_equiv. iIntros "l". rewrite lend_tok_unseal.
    iExists _. iSplit; [by iApply lft_sincl_refl|]. by iExists _.
  Qed.
  (** Simply create a new borrower and a new lender *)
  Lemma bor_lend_tok_new {sm} α Px :
    sm Px =[borrow_wsat M sm]=∗ bor_tok α Px ∗ lend_tok α Px.
  Proof.
    iIntros "Px". iMod (bor_lend_tok_new_list α [Px] [Px] with "[Px] []")
      as "[[$_][$_]]"; by [iFrame|iIntros|].
  Qed.

  (** Split a lender *)
  Lemma lend_tok_split {sm α Px} Qxl :
    lend_tok α Px -∗ (sm Px -∗ M ([∗ list] Qx ∈ Qxl, sm Qx))
      =[borrow_wsat M sm]=∗ [∗ list] Qx ∈ Qxl, lend_tok α Qx.
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "(%α' & #? & %i & %k & l) PQ (%Dl & #Ne & ● & Dl)". iFrame "Ne".
    iDestruct (depo_stl_lend_agree with "● l") as (??? eq ?) "#eqv".
    iMod (depo_stl_lend_delete with "● l") as "●"; [done|].
    iMod (depo_stl_lend_add Qxl with "●") as "[● ls]".
    { apply list_lookup_insert. by apply: lookup_lt_Some. }
    iModIntro. iSplitR "ls"; last first.
    { rewrite big_sepM_map_without'. iApply (big_sepL_impl with "ls").
      iIntros "!> %% ⊑ [% ?]". iExists _. iSplit; [done|]. by iExists _, _. }
    iExists _. iFrame "●". rewrite list_insert_insert.
    iDestruct (big_sepL_insert_acc with "Dl") as "[D →Dl]"; [done|]=>/=.
    iApply "→Dl". clear eq. iDestruct "D" as "[[Bl →Lm]|[† Lm]]".
    - iLeft. iFrame "Bl". iIntros "† Bl".
      iMod ("→Lm" with "† Bl") as "Lm". rewrite big_sepM_map_with.
      iDestruct (big_sepM_delete with "Lm") as "[Px $]"; [done|]. iApply "PQ".
      iApply ("Ne" with "eqv Px").
    - iRight. iFrame "†". iMod "Lm". rewrite big_sepM_map_with.
      iDestruct (big_sepM_delete with "Lm") as "[Px $]"; [done|]. iApply "PQ".
      iApply ("Ne" with "eqv Px").
  Qed.

  (** [depo_wsat] with deposits under [α] retrieved *)
  Local Definition depo_wsat_ret' M sm α i β Bl Lm : iProp Σ :=
    if decide (β ⊑ α)
      then depo_wsat_ret M sm β Lm else depo_wsat M sm i β Bl Lm.
  (** [borrow_wsat] with deposits after [Dl], retrieved under [α] *)
  Local Definition borrow_wsat_ret M sm α Dl : iProp Σ :=
    ∃ Dl', sem_ne sm ∗ depo_stl_tok (Dl ++ Dl') ∗
      [∗ list] i ↦ '(β, Bl, Lm)' ∈ Dl',
        depo_wsat_ret' M sm α (length Dl + i) β Bl Lm.

  (** Retrieve using [lend_itok] under [borrow_wsat_ret] *)
  Local Lemma lend_itok_ret_retrieve {sm i Dl α β Px} : length Dl ≤ i → β ⊑ α →
    lend_itok i β Px -∗ modw M (borrow_wsat_ret M sm α Dl) (sm Px).
  Proof.
    move=> ??. iIntros "[% l] (%Dl' & #Ne & ● & Dl')". iFrame "Ne".
    iDestruct (depo_stl_lend_agree with "● l") as (??? eq ?) "#eqv". move: (eq).
    rewrite lookup_app_r; [|done]=> ?.
    iDestruct (big_sepL_insert_acc with "Dl'") as "[D →Dl']"; [done|]=>/=.
    iMod (depo_stl_lend_delete with "● l") as "●"; [done|].
    rewrite insert_app_r_alt; [|done]. iFrame "●".
    rewrite /depo_wsat_ret' decide_True; [|done].
    iDestruct "D" as "[† >Lm]". iModIntro.
    iDestruct (big_sepM_delete with "Lm") as "[Px Lm]"; [done|].
    iDestruct ("Ne" with "eqv Px") as "$". iApply "→Dl'".
    rewrite decide_True; [|done]. by iFrame.
  Qed.

  (** Retrieve from [bor_wsat] under [borrow_wsat_ret] *)
  Local Lemma bor_wsat_retrieve {sm Dl D α β Px b} : β ⊑ α →
    [†β] -∗ bor_wsat sm (length Dl) β (Px, b) -∗
      modw M (borrow_wsat_ret M sm α (Dl ++ [D])) (sm Px).
  Proof.
    move=> ?. iIntros "† B". case b=> [|q|?]/=. { done. }
    { iDestruct (lft_live_dead with "B †") as %[]. }
    iDestruct "B" as (???) "l".
    iApply (lend_itok_ret_retrieve with "l"); [|by etrans].
    rewrite length_app /=. lia.
  Qed.
  (** Retrieve from [bor_wsat]s *)
  Local Lemma bor_wsatl_retrieve {sm Dl D α β Bl} : β ⊑ α →
    [†β] -∗ ([∗ list] B ∈ Bl, bor_wsat sm (length Dl) β B) -∗
      modw M (borrow_wsat_ret M sm α (Dl ++ [D]))
        ([∗ list] '(Px, _) ∈ Bl, sm Px)%I.
  Proof.
    move=> ?. elim: Bl; [by iIntros|]. move=>/= [??] Bl IH. iIntros "#† [B Bl]".
    iMod (IH with "† Bl") as "$". by iApply bor_wsat_retrieve.
  Qed.

  (** Retrieve from [depo_wsat] and enrich [borrow_wsat_ret] *)
  Local Lemma depo_wsat_retrieve' {sm Dl α β Bl Lm} :
    [†α] -∗ depo_wsat M sm (length Dl) β Bl Lm -∗
      modw M (borrow_wsat_ret M sm α (Dl ++ [(β, Bl, Lm)']))
        (depo_wsat_ret' M sm α (length Dl) β Bl Lm).
  Proof.
    unfold depo_wsat_ret'. case (decide (β ⊑ α)); [|by iIntros "_ _ ?"]=> ?.
    iIntros "#† [[Bl →Lm]|?]"; [|done]. rewrite lft_incl_dead; [|done].
    iFrame "†". iApply modw_fold. iDestruct ("→Lm" with "†") as "→Lm".
    iMod (bor_wsatl_retrieve with "† Bl") as "Bl"; [done|].
    iMod ("→Lm" with "Bl") as "$". by iIntros "$".
  Qed.
  Local Lemma depo_wsat_retrieve {sm Dl α β Bl Lm} :
    [†α] -∗ depo_wsat M sm (length Dl) β Bl Lm -∗
    borrow_wsat_ret M sm α (Dl ++ [(β, Bl, Lm)']) -∗
      M (borrow_wsat_ret M sm α Dl).
  Proof.
    iIntros "† W D".
    iMod (depo_wsat_retrieve' with "† W D") as "[(% & $ & ● & Dl') D]".
    iModIntro. setoid_rewrite length_app. setoid_rewrite <-Nat.add_assoc.
    rewrite -app_assoc /=. iFrame "● Dl'". by rewrite (right_id 0).
  Qed.

  (** Retrieve from [depo_wsat]s *)
  Local Lemma depo_wsatl_retrieve {sm α Dl} : [†α] -∗
    ([∗ list] i ↦ '(β, Bl, Lm)' ∈ Dl, depo_wsat M sm i β Bl Lm) -∗
    borrow_wsat_ret M sm α Dl -∗
      M (borrow_wsat_ret M sm α []).
  Proof.
    rewrite /= -(reverse_involutive Dl). move: (reverse Dl)=> Dl'.
    iIntros "#†". iInduction Dl' as [|[?[??]] Dl'] "IH"; [by iIntros|]=>/=.
    rewrite reverse_cons. rewrite big_sepL_snoc. iIntros "[Dl D] ret".
    iMod (depo_wsat_retrieve with "† D ret") as "ret".
    iApply ("IH" with "Dl ret").
  Qed.
  (** Retrieve from [borrow_wsat] *)
  Local Lemma borrow_wsat_retrieve {sm α} :
    [†α] -∗ borrow_wsat M sm -∗ M (borrow_wsat_ret M sm α []).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "† (%Dl & Ne & ● & Dl)".
    iApply (depo_wsatl_retrieve with "† Dl"). iFrame "Ne". iExists [].
    rewrite app_nil_r. by iFrame.
  Qed.

  (** Retrive using [lend_itok] *)
  Local Lemma lend_itok_retrieve {sm i α Px} :
    [†α] -∗ lend_itok i α Px -∗ modw M (borrow_wsat M sm) (sm Px).
  Proof.
    iIntros "† l W". rewrite {2}borrow_wsat_unseal.
    iMod (borrow_wsat_retrieve with "† W") as "ret".
    iMod (lend_itok_ret_retrieve with "l ret") as "[ret $]"=>/=; [lia|done|].
    iModIntro. iDestruct "ret" as (?) "($ & $ & ?)"=>/=. iStopProof.
    do 2 f_equiv. move=> [β ?]. unfold depo_wsat_ret'.
    case (decide (β ⊑ α)); [|done]. iIntros. by iRight.
  Qed.
  (** Retrive using [lend_tok] *)
  Lemma lend_tok_retrieve {sm α Px} :
    [†α] -∗ lend_tok α Px -∗ modw M (borrow_wsat M sm) (sm Px).
  Proof.
    rewrite lend_tok_unseal. iIntros "† [%α'[⊑[%i l]]]".
    iDestruct (lft_sincl_dead with "⊑ †") as "†".
    by iApply (lend_itok_retrieve with "† l").
  Qed.

  (** [depo_wsat] with a live lifetime token *)
  Local Lemma depo_wsat_tok {sm i α Bl Lm q} :
    q.[α] -∗ depo_wsat M sm i α Bl Lm -∗ q.[α] ∗ depo_wsat_bor M sm i α Bl Lm.
  Proof.
    iIntros "α [$|[† _]]"; [done|].
    iDestruct (lft_live_dead with "α †") as %[].
  Qed.

  (** [bor_wsat] is non-expansive over the borrower state *)
  Local Lemma bor_wsat_ne_st {sm i α} :
    sem_ne sm ⊢ □ ∀ B B', B ≡ B' -∗ bor_wsat sm i α B -∗ bor_wsat sm i α B'.
  Proof.
    iIntros "#Ne !> /=" ([? b][??]). rewrite prod_equivI /=. iIntros "[eqv <-]".
    iIntros "B". case: b=>//= >. { iApply ("Ne" with "eqv B"). }
    iDestruct "B" as "[$[%[$ ?]]]". by iRewrite -"eqv".
  Qed.

  (** Update the borrower state to [Open q] *)
  Local Lemma bor_open_core {sm i j α Px b q} :
    q.[α] -∗ bor_jtok i j α (Px, b) =[borrow_wsat M sm]=∗
      obor_tok α q Px ∗ bor_wsat sm i α (Px, b).
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[α α'] b (%Dl & #Ne & ● & Dl)".
    iFrame "Ne".
    iDestruct (depo_stl_bor_agree with "● b") as (Bl Lm [??]? eq) "#eqv".
    iDestruct (big_sepL_insert_acc with "Dl") as "[D →Dl]"; [done|].
    iDestruct (depo_wsat_tok with "α D") as "[α [Bl →Qm]]".
    iMod (depo_stl_bor_stupd with "● b") as "[● o]"; [done..|]. iModIntro.
    iDestruct (big_sepL_insert_acc with "Bl") as "[B →Bl]"; [done|].
    iDestruct (bor_wsat_ne_st with "Ne eqv B") as "$".
    iSplitR "α o"; last first.
    { rewrite obor_tok_unseal. iExists _, _, _, _.
      iSplitR; [iApply lft_sincl_refl|]. iSplitR; [by iIntros|]. iFrame. }
    iExists _. iFrame "●". iApply "→Dl". iLeft.
    iSplitR "→Qm"=>/=; [by iApply "→Bl"|]. iIntros "† big".
    iApply ("→Qm" with "†"). rewrite -{2}(list_insert_id _ _ _ eq).
    iDestruct (big_sepL_insert_acc _ _ j with "big") as "[Px big]".
    { apply list_lookup_insert. by apply: lookup_lt_Some. }
    setoid_rewrite list_insert_insert. iApply "big". rewrite prod_equivI /=.
    iDestruct "eqv" as "[eqv _]". iApply ("Ne" with "[] Px").
    by iApply internal_eq_sym.
  Qed.
  (** Open a borrower *)
  Lemma bor_tok_open {sm α q Px} :
    q.[α] -∗ bor_tok α Px -∗
      modw M (borrow_wsat M sm) (obor_tok α q Px ∗ sm Px).
  Proof.
    rewrite bor_tok_unseal. iIntros "α [†|b]".
    { by iDestruct (lft_live_dead with "α †") as %[]. }
    iDestruct "b" as (???) "[#⊑ b]".
    iMod (lft_sincl_live_acc with "⊑ α") as (r) "[α' →α]".
    iDestruct "b" as "[b|[%β[#† r]]]".
    - iMod (bor_open_core with "α' b") as "[o $]". iApply modw_fold.
      iApply (obor_tok_lft with "⊑ →α o").
    - iMod (bor_open_core with "α' r") as "[o [%[%[_ l]]]]".
      iDestruct (obor_tok_lft with "⊑ →α o") as "$". iApply modw_fold.
      iApply (lend_itok_retrieve with "† l").
  Qed.

  (** Turn [obor_itok] to a reborrower using [lend_itok] *)
  Local Lemma obor_itok_reborrow {sm i α' α q Px β i'} : i < i' → β ⊑ α' →
    obor_itok i α' α q Px -∗ lend_itok i' β Px =[borrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α Px).
  Proof.
    rewrite borrow_wsat_unseal=> ??.
    iIntros "(%j & %r & #⊑ & →α & α' & o) [%k l] (%Dl & #Ne & ● & Dl)".
    iFrame "Ne".
    iDestruct (depo_stl_bor_agree with "● o") as (Bl Lm B' ? eq) "#eqv".
    iDestruct (big_sepL_insert_acc with "Dl") as "[D →Dl]"; [done|]=>/=.
    iMod (depo_stl_bor_stupd (B':=(_, Rebor β)) with "● o") as "[● r]";
      [done..|]. iModIntro.
    iDestruct (depo_wsat_tok with "α' D") as "[α'[Bl →Lm]]".
    iDestruct (big_sepL_insert_acc with "Bl") as "/=[B' →Bl]"; [done|].
    iDestruct (bor_wsat_ne_st with "Ne eqv B'") as "B'".
    iDestruct ("→α" with "[$α' $B' //]") as "$". iSplitR "r"; last first.
    { iIntros "†". rewrite bor_tok_unseal. iRight. iExists _, _, _.
      iFrame "⊑". iRight. iExists _. by iSplit. }
    iExists _. iFrame "●". iApply "→Dl". iLeft. iSplitR "→Lm".
    { iApply "→Bl". iSplit; [done|]. iExists _. iSplit; by [|iExists _]. }
    iIntros "† big". iApply ("→Lm" with "†").
    rewrite -{2}(list_insert_id _ _ _ eq).
    iDestruct (big_sepL_insert_acc _ _ j with "big") as "[Px big]".
    { apply list_lookup_insert. by apply: lookup_lt_Some. }
    setoid_rewrite list_insert_insert. iApply "big".
    rewrite prod_equivI /=. iDestruct "eqv" as "[eqv _]". case B'=>/= ??.
    iApply ("Ne" with "[] Px"). by iApply internal_eq_sym.
  Qed.

  (** Lemmas for [obor_tok_merge_subdiv] *)
  Local Lemma obor_itok_lft_sincl {i α α' q Px} :
    obor_itok i α α' q Px ⊢ α' ⊑□ α.
  Proof. iDestruct 1 as (??) "[$ _]". Qed.
  Local Lemma obor_itok_lt {sm i α α' q Px Dl} :
    obor_itok i α α' q Px -∗ borrow_lwsat M sm Dl -∗ ⌜i < length Dl⌝.
  Proof.
    iIntros "(% & % & _ & _ & _ & o) (_ & ● & _)".
    iDestruct (depo_stl_bor_agree with "● o") as (?????) "_". iPureIntro.
    by apply: lookup_lt_Some.
  Qed.
  Local Lemma obor_toks_itoks {sm αqPxl β Dl} :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ obor_tok α q Px) -∗
    borrow_lwsat M sm Dl -∗ ∃ γ, ⌜γ ⊑ β⌝ ∗ β ⊑□ γ ∗
      borrow_lwsat M sm Dl ∗
      [∗ list] '(α, q, Px)' ∈ αqPxl, ∃ i α',
        ⌜i < length Dl ∧ γ ⊑ α'⌝ ∗ obor_itok i α' α q Px.
  Proof.
    elim: αqPxl=>/=.
    { iIntros "_ $". iExists β. iSplit; [done|]. iApply lft_sincl_refl. }
    rewrite obor_tok_unseal. move=> [α[Px q]] αqPxl IH.
    iIntros "[[#βα (%i' & %α' & o)] big] W".
    iDestruct (obor_itok_lt with "o W") as %?.
    iDestruct (IH with "big W") as (γ ?) "(#βγ & $ & big)".
    iDestruct (obor_itok_lft_sincl with "o") as "#?". iExists (γ ⊓ α').
    iSplit. { iPureIntro. etrans; [|done]. exact lft_incl_meet_l. }
    iSplit.
    { iApply (lft_sincl_meet_intro with "βγ").
      by iApply (lft_sincl_trans with "βα"). }
    iSplitL "o".
    { iExists _, _. iFrame "o". iPureIntro. split; [lia|].
      exact lft_incl_meet_r. }
    iClear "#". iStopProof. do 3 f_equiv.
    iDestruct 1 as (??[??]) "o". iExists _, _. iFrame "o". iPureIntro.
    split; [lia|]. etrans; [|done]. exact lft_incl_meet_l.
  Qed.
  (** Merge and subdivide/reborrow borrowers *)
  Lemma obor_tok_merge_subdiv {sm} αqPxl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ obor_tok α q Px) -∗
    ([∗ list] Qx ∈ Qxl, sm Qx) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗
      M ([∗ list] '(_, _, Px)' ∈ αqPxl, sm Px)%I)
      =[borrow_wsat M sm]=∗
      ([∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ bor_tok α Px)) ∗
      [∗ list] Qx ∈ Qxl, bor_tok β Qx.
  Proof.
    rewrite borrow_wsat_unseal. iIntros "big Qxl →Px [%Dl W]".
    iDestruct (obor_toks_itoks with "big W") as (??) "(#⊑ & W & αqPxl)".
    iMod (bor_lend_tok_new_list' γ Qxl ((λ '(_, _, Px)', Px) <$> αqPxl)
      with "Qxl [→Px] W") as (?) "(W & bl & ll)"=>/=.
    { iIntros "† Qxl". iDestruct (lft_sincl_dead with "⊑ †") as "†".
      rewrite big_sepL_fmap. iApply ("→Px" with "† Qxl"). }
    rewrite assoc. iSplitR "bl"; last first.
    { iModIntro. iApply (big_sepL_impl with "bl"). iIntros "!> %% _".
      by iApply bor_tok_lft. }
    iInduction αqPxl as [|[α[q Px]]αqPxl] "IH"=>/=; [by iFrame|].
    iDestruct "αqPxl" as "[big αqPxl]". iDestruct "big" as (??[??]) "o".
    iDestruct "ll" as "[l ll]". iMod ("IH" with "αqPxl W ll") as "[W $]".
    rewrite -borrow_wsat_unseal.
    iMod (obor_itok_reborrow with "o l W") as "[$[$ →b]]"; [lia|done|].
    iModIntro. iIntros "†". iApply "→b". by iApply (lft_incl_dead with "†").
  Qed.
  (** Subdivide/reborrow a borrower *)
  Lemma obor_tok_subdiv {sm α q Px} Qxl β :
    β ⊑□ α -∗ obor_tok α q Px -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, sm Qx) -∗ M (sm Px))
      =[borrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α Px) ∗ [∗ list] Qx ∈ Qxl, bor_tok β Qx.
  Proof.
    iIntros "⊑ o Qxl →Px".
    iMod (obor_tok_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→Px]")
      as "[[[$$]_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.

  (** Reborrow a borrower *)
  Lemma obor_tok_reborrow {sm α q Px} β :
    β ⊑□ α -∗ obor_tok α q Px -∗ sm Px =[borrow_wsat M sm]=∗
      q.[α] ∗ ([†β] -∗ bor_tok α Px) ∗ bor_tok β Px.
  Proof.
    iIntros "⊑ o Px".
    iMod (obor_tok_subdiv [Px] with "⊑ o [Px] []") as "($ & $ & $ & _)"=>/=;
      by [iFrame|iIntros "_ [$ _]"|].
  Qed.
  Lemma bor_tok_reborrow {sm α q Px} β :
    β ⊑□ α -∗ q.[α] -∗ bor_tok α Px -∗ modw M (borrow_wsat M sm)
      (q.[α] ∗ ([†β] -∗ bor_tok α Px) ∗ bor_tok β Px).
  Proof.
    iIntros "⊑ α b". iMod (bor_tok_open with "α b") as "[o Px]".
    by iMod (obor_tok_reborrow with "⊑ o Px").
  Qed.
  (** Simply close a borrower *)
  Lemma obor_tok_close {sm α q Px} :
    obor_tok α q Px -∗ sm Px =[borrow_wsat M sm]=∗ q.[α] ∗ bor_tok α Px.
  Proof.
    iIntros "o Px".
    iMod (obor_tok_reborrow with "[] o Px") as "($ & _ & $)";
      by [iApply lft_sincl_refl|].
  Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc' `{!borrowGpreS FML Σ} :
  ⊢ |==> ∃ _ : borrowGS FML Σ,
    ∀ M sm, □ (∀ Px Qx, Px ≡ Qx -∗ sm Px -∗ sm Qx) -∗ borrow_wsat M sm.
Proof.
  iMod (own_alloc (● ∅ : borrowRF_def _ $ri _)) as (γ) "●";
    [by apply auth_auth_valid|].
  iModIntro. iExists (BorrowGS _ _ _ _ γ). rewrite borrow_wsat_unseal.
  iIntros (??) "$". iExists []. by iFrame.
Qed.
Lemma borrow_wsat_alloc `{!borrowGpreS FML Σ} :
  ⊢ |==> ∃ _ : borrowGS FML Σ, ∀ M sm, ⌜NonExpansive sm⌝ -∗ borrow_wsat M sm.
Proof.
  iMod borrow_wsat_alloc' as (?) "W". iModIntro. iExists _. iIntros (???).
  iApply "W". iIntros "!> %% eqv ?". by iRewrite -"eqv".
Qed.
