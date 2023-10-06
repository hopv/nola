(** * Borrowing machinery *)

From nola.util Require Export prod.
From nola.iris Require Export lft upd.
From iris.algebra Require Import numbers excl agree gmap auth.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : Type.
Implicit Type (α : lft) (q : Qp).

(** ** Ghost state *)

(** Algebra for the depth bounding *)
Definition depthR := authR max_natR.
Implicit Type d g : nat.

(** ID for a borrower/lender *)
Local Definition bor_id := positive.
Local Definition lend_id := positive.
Implicit Type (j : bor_id) (i : lend_id).

(** Kind of a borrower *)
Variant bor_kind :=
| #[local] Clsd (* Closed *)
| #[local] Open (q : Qp) (* Open with a fraction *)
| #[local] Rebor (α : lft) (* Reborrowed *).
Implicit Type b : bor_kind.
(** State of a borrower *)
Local Definition bor_st PROP : Type :=
  PROP *' bor_kind (* Deposited fraction *).
(** State of the borrowers *)
Local Definition bor_stm PROP : Type := gmap bor_id (bor_st PROP).

(** Kind of a lender *)
Variant lend_kind :=
| #[local] Lend (* Lending *)
| #[local] Dead (* Dead *).
Implicit Type l : lend_kind.
(** Core state of a lender *)
Local Definition lend_cst PROP : Type := nat (* Depth *) *' PROP *' lend_kind.
(** State of a lender *)
Local Definition lend_st PROP : Type :=
  lft *' lend_cst PROP *' bor_stm PROP.
(** State of the lenders *)
Local Definition lend_stm PROP : Type := gmap lend_id (lend_st PROP).

(** Algebra for a borrower *)
Local Definition borR PROP := exclR (leibnizO (bor_st PROP)).

(** Algebra for a lender *)
Local Definition lendR PROP := prodR
  (prodR (agreeR (leibnizO lft)) (optionR (exclR (leibnizO (lend_cst PROP)))))
  (gmapR bor_id (borR PROP)).

(** Algebra for the borrowing machinery *)
Local Definition borrowR_def PROP := authR (gmapR lend_id (lendR PROP)).
Local Lemma borrowR_aux : seal borrowR_def. Proof. by eexists. Qed.
Definition borrowR := borrowR_aux.(unseal).
Local Lemma borrowR_unseal : borrowR = borrowR_def.
Proof. exact: borrowR_aux.(seal_eq). Qed.

(** Ghost state for the borrowing machinery *)
Class borrowGS PROP Σ := BorrowGS {
  borrowGS_lft :: lftG Σ;
  borrowGS_depth :: inG Σ depthR;
  borrowGS_borrow :: inG Σ (borrowR PROP);
  depth_name : gname; borrow_name : gname;
}.
Local Existing Instance borrowGS_depth.
Local Existing Instance borrowGS_borrow.
Local Instance inG_borrow_def `{!inG Σ (borrowR PROP)} :
  inG Σ (borrowR_def PROP).
Proof. rewrite -borrowR_unseal. apply _. Qed.
Class borrowGpreS PROP Σ := BorrowGpreS {
  borrowGpreS_lft :: lftG Σ;
  borrowGpreS_depth :: inG Σ depthR;
  borrowGpreS_borrow :: inG Σ (borrowR PROP);
}.
Definition borrowΣ PROP : gFunctors :=
  #[GFunctor lftR; GFunctor depthR; GFunctor (borrowR PROP)].
#[export] Instance subG_borrow `{!subG (borrowΣ PROP) Σ} : borrowGpreS PROP Σ.
Proof. solve_inG. Qed.

(** ** Tokens *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (P Q : PROP)
    (B : bor_st PROP) (L : lend_st PROP) (Lm : lend_stm PROP).

  (** Witness of a depth *)
  Local Definition depth d : iProp Σ := own depth_name (◯ (MaxNat d)).
  (** Global bound of the depths *)
  Local Definition gdepth g : iProp Σ := own depth_name (● (MaxNat g)).

  (** Get [depth 0] *)
  Local Lemma depth_0 : ⊢ |==> depth 0. Proof. apply own_unit. Qed.
  (** Introduce a new depth *)
  Local Lemma depth_alloc {g d} : gdepth g ==∗ ∃ g', gdepth g' ∗ depth d.
  Proof.
    iIntros "g". iMod (own_update with "g") as "[? $]"; [|by iExists _].
    apply auth_update_alloc, local_update_unital_discrete=> ? _.
    by rewrite left_id=> <-.
  Qed.

  (** Bounding by [gdepth] *)
  Local Lemma depth_bound {g d} : gdepth g -∗ depth d -∗ ⌜d ≤ g⌝.
  Proof.
    iIntros "g d". iDestruct (own_valid_2 with "g d") as %v. iPureIntro.
    by move: v=> /auth_both_valid_discrete [/max_nat_included ? _].
  Qed.

  (** General borrower token *)
  Local Definition bor_itok i j α B : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, ε, {[j := Excl B]})]}).

  (** Closed borrower token *)
  Local Definition bor_ctok_def α P : iProp Σ :=
    [†α] ∨ ∃ α', α ⊑s α' ∗ (∃ i j, bor_itok i j α' (P, Clsd)').
  Local Lemma bor_ctok_aux : seal bor_ctok_def. Proof. by eexists. Qed.
  Definition bor_ctok := bor_ctok_aux.(unseal).
  Local Lemma bor_ctok_unseal : bor_ctok = bor_ctok_def.
  Proof. exact: bor_ctok_aux.(seal_eq). Qed.
  (** Borrower token

    It may be a dead lifetime token, a closed borrower,
    or an retrieving reborrower *)
  Local Definition bor_tok_def α P : iProp Σ :=
    bor_ctok α P ∨
    ∃ α', α ⊑s α' ∗ ∃ i j β, [†β] ∗ bor_itok i j α' (P, Rebor β)'.
  Local Lemma bor_tok_aux : seal bor_tok_def. Proof. by eexists. Qed.
  Definition bor_tok := bor_tok_aux.(unseal).
  Local Lemma bor_tok_unseal : bor_tok = bor_tok_def.
  Proof. exact: bor_tok_aux.(seal_eq). Qed.

  (** Open borrower token

    It keeps a lifetime token at hand *)
  Local Definition bor_otok_def α P q : iProp Σ :=
    ∃ α' r, α ⊑s α' ∗ (r.[α'] -∗ q.[α]) ∗
      (r/2).[α'] ∗ ∃ i j, bor_itok i j α' (P, Open (r/2))'.
  Local Lemma bor_otok_aux : seal bor_otok_def. Proof. by eexists. Qed.
  Definition bor_otok := bor_otok_aux.(unseal).
  Local Lemma bor_otok_unseal : bor_otok = bor_otok_def.
  Proof. exact: bor_otok_aux.(seal_eq). Qed.

  (** Lender token *)
  Local Definition lend_itok i α d P : iProp Σ :=
    own borrow_name (◯ {[i := (to_agree α, Excl' (d, P, Lend)', ε)]}).
  Local Definition lend_dtok α d P : iProp Σ :=
    depth d ∗ ∃ i, lend_itok i α d P.
  Local Definition lend_tok_def α P : iProp Σ :=
    ∃ α', α' ⊑s α ∗ ∃ d, lend_dtok α' d P.
  Local Lemma lend_tok_aux : seal lend_tok_def. Proof. by eexists. Qed.
  Definition lend_tok := lend_tok_aux.(unseal).
  Local Lemma lend_tok_unseal : lend_tok = lend_tok_def.
  Proof. exact: lend_tok_aux.(seal_eq). Qed.

  (** Convert a closed borrower token into a borrower token *)
  Lemma bor_ctok_tok {α P} : bor_ctok α P ⊢ bor_tok α P.
  Proof. rewrite bor_tok_unseal. iIntros. by iLeft. Qed.
  (** Fake a closed borrower from the dead lifetime token *)
  Lemma bor_ctok_fake {α P} : [†α] ⊢ bor_ctok α P.
  Proof. rewrite bor_ctok_unseal. iIntros. by iLeft. Qed.
  (** Fake a borrower from the dead lifetime token *)
  Lemma bor_tok_fake {α P} : [†α] ⊢ bor_tok α P.
  Proof. by rewrite bor_ctok_fake bor_ctok_tok. Qed.

  (** Modify the lifetime of borrower and lender tokens *)
  Lemma bor_ctok_lft {α α' P} : α' ⊑s α -∗ bor_ctok α P -∗ bor_ctok α' P.
  Proof.
    rewrite bor_ctok_unseal. iIntros "#? [#?|[%α''[? c]]]".
    { iLeft. by iApply lft_sincl_dead_acc. }
    iRight. iExists _. iFrame "c". by iApply lft_sincl_trans.
  Qed.
  Lemma bor_tok_lft {α α' P} : α' ⊑s α -∗ bor_tok α P -∗ bor_tok α' P.
    rewrite bor_tok_unseal. iIntros "#? [c|[%α''[#? r]]]".
    { iLeft. by iApply bor_ctok_lft. }
    iRight. iExists _. iFrame "r". by iApply lft_sincl_trans.
  Qed.
  Lemma bor_otok_lft {α α' P q r} :
    α' ⊑s α -∗ (q.[α] -∗ r.[α']) -∗ bor_otok α P q -∗ bor_otok α' P r.
  Proof.
    rewrite bor_otok_unseal. iIntros "#? →α' [%α''[%s[#?[→α o]]]]".
    iExists _, _. iFrame "o". iSplit; [by iApply lft_sincl_trans|].
    iIntros "α''". iApply "→α'". by iApply "→α".
  Qed.
  Lemma lend_tok_lft {α α' P} : α ⊑s α' -∗ lend_tok α P -∗ lend_tok α' P.
  Proof.
    rewrite lend_tok_unseal. iIntros "#? [%α''[#? l]]". iExists _. iFrame "l".
    by iApply lft_sincl_trans.
  Qed.

  (** Token for [lend_stm] *)
  Local Definition lend_st_to_lendR L : lendR PROP :=
    let '(α, C, Bm)' := L in
    (to_agree α, Excl' C, (Excl : bor_st _ → _) <$> Bm).
  Local Definition lend_stm_tok Lm : iProp Σ :=
    own borrow_name (● (lend_st_to_lendR <$> Lm : gmapR _ _)).

  (** Create [bor_itok] and [lend_itok] w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_create {Lm} d α P :
    lend_stm_tok Lm -∗ |==> ∃ i j,
      lend_stm_tok (<[i := (α, (d, P, Lend)', {[j := (P, Clsd)']})']> Lm) ∗
      bor_itok i j α (P, Clsd)' ∗ lend_itok i α d P.
  Proof.
    iIntros "●". iExists (fresh (dom Lm)), 1%positive.
    iMod (own_update with "●") as "[$[$$]]"; [|done].
    rewrite -auth_frag_op singleton_op fmap_insert. apply auth_update_alloc.
    have <- :
      lend_st_to_lendR (α, (d, P, Lend)', {[1%positive := (P, Clsd)']})' ≡
      ((to_agree α, ε, {[1%positive := Excl (P, Clsd)']}) : lendR _) ⋅
        (to_agree α, Excl' (d, P, Lend)', ε).
    { split; [split|]=>/=; by [rewrite agree_idemp|]. }
    apply alloc_singleton_local_update.
    - rewrite lookup_fmap. apply fmap_None, not_elem_of_dom_1, is_fresh.
    - split; [split|]=>/=; by [|rewrite map_fmap_singleton singleton_valid].
  Qed.

  (** Agreement between [lend_stm_tok] and [lend_itok] *)
  Local Lemma lend_stm_lend_agree {Lm i α d P} :
    lend_stm_tok Lm -∗ lend_itok i α d P -∗
      ⌜∃ Bm, Lm !! i = Some (α, (d, P, Lend)', Bm)'⌝.
  Proof.
    iIntros "● l". iDestruct (own_valid_2 with "● l") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[
      /Some_equiv_eq[[[??]?][/lookup_fmap_Some[[?[? Bm]][[<-<-<-]?]<-]]]
      /Some_included_total/prod_included[/prod_included/=[
        /to_agree_included/leibniz_equiv_iff?
        /Excl_included/leibniz_equiv_iff?]_]]]_].
    subst. by eexists _.
  Qed.
  (** Extend a lender w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_lend_extend {Lm i α d P Bm Q} :
    Lm !! i = Some (α, (d, P, Lend)', Bm)' →
    lend_stm_tok Lm -∗ lend_itok i α d P ==∗
      lend_stm_tok (<[i := (α, (d, Q, Lend)', Bm)']> Lm) ∗ lend_itok i α d Q.
  Proof.
    move=> ?. iIntros "● l". iMod (own_update_2 with "● l") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    apply: option_local_update. by apply exclusive_local_update.
  Qed.
  (** Retrieve for a lender w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_lend_retrieve {Lm i α d P Bm} :
    Lm !! i = Some (α, (d, P, Lend)', Bm)' →
    lend_stm_tok Lm -∗ lend_itok i α d P ==∗
      lend_stm_tok (<[i := (α, (d, P, Dead)', Bm)']> Lm).
  Proof.
    move=> ?. iIntros "● l". iMod (own_update_2 with "● l") as "[$_]"; [|done].
    apply auth_update. rewrite fmap_insert.
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done| |done].
    apply: option_local_update. by apply exclusive_local_update.
  Qed.

  (** Agreement between [lend_stm_tok] and [bor_itok] *)
  Local Lemma lend_stm_bor_agree {Lm i j α B} :
    lend_stm_tok Lm -∗ bor_itok i j α B -∗
      ⌜∃ C Bm, Lm !! i = Some (α, C, Bm)' ∧ Bm !! j = Some B⌝.
  Proof.
    iIntros "● B". iDestruct (own_valid_2 with "● B") as %v. iPureIntro.
    move: v=> /auth_both_valid_discrete[/singleton_included_l[?[
      /Some_equiv_eq[?[/lookup_fmap_Some[[?[C Bm]][<-+]]<-]]
      /Some_included_total/prod_included[/prod_included/=
        [/to_agree_included/leibniz_equiv_iff ? _]incl]]]_]=> ?.
    apply singleton_included_exclusive_l in incl; [|apply _| ]; last first.
    { move=> j'. rewrite lookup_fmap. by case: (Bm !! j'). }
    move: incl. rewrite lookup_fmap leibniz_equiv_iff fmap_Some.
    move=> [?[?[?]]]. subst. by eexists _, _.
  Qed.
  (** Update the borrower state w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_bor_stupd {Lm i j α C Bm B B'} :
    Lm !! i = Some (α, C, Bm)' → Bm !! j = Some B →
    lend_stm_tok Lm -∗ bor_itok i j α B ==∗
      lend_stm_tok (<[i := (α, C, <[j := B']> Bm)']> Lm) ∗
      bor_itok i j α B'.
  Proof.
    move=> ??. iIntros "● B". iMod (own_update_2 with "● B") as "[$$]"; [|done].
    apply auth_update. rewrite fmap_insert. eapply singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_insert. apply: singleton_local_update.
    { rewrite lookup_fmap_Some. by eexists _. } by apply exclusive_local_update.
  Qed.
  (** Delete the borrower w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_bor_delete {Lm i j α C Bm B} :
    Lm !! i = Some (α, C, Bm)' → Bm !! j = Some B →
    lend_stm_tok Lm -∗ bor_itok i j α B ==∗ ∃ Bm',
      lend_stm_tok (<[i := (α, C, Bm')']> Lm) ∗
      ⌜∀ Φ : _ → iProp Σ, ([∗ map] B ∈ Bm, Φ B) ⊣⊢ Φ B ∗ [∗ map] B ∈ Bm', Φ B⌝.
  Proof.
    move=> ??. iIntros "● B". iExists (delete j Bm).
    iMod (own_update_2 with "● B") as "[$_]"; last first.
    { iPureIntro=> ?. by apply big_sepM_delete. }
    apply auth_update. rewrite fmap_insert.
    eapply (singleton_local_update _ _ _ _ _ (_,_,_)).
    { rewrite lookup_fmap_Some. by eexists _. }
    apply prod_local_update; [apply prod_local_update|]=>/=; [done..|].
    rewrite fmap_delete.
    apply: delete_local_update; [|by rewrite lookup_singleton]. apply _.
  Qed.
  (** Create a new borrower w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_new_bor {Lm i α C Bm B} :
    Lm !! i = Some (α, C, Bm)' →
    lend_stm_tok Lm ==∗ ∃ Bm', lend_stm_tok (<[i := (α, C, Bm')']> Lm) ∗
      (∃ j, bor_itok i j α B) ∗
      ⌜∀ Φ : _ → iProp Σ, ([∗ map] B ∈ Bm', Φ B) ⊣⊢ Φ B ∗ [∗ map] B ∈ Bm, Φ B⌝.
  Proof.
    move=> Lmi. iIntros "●". iExists (<[fresh (dom Bm) := B]> Bm).
    iMod (own_update with "●") as "[$ b]"; last first.
    { iModIntro. iSplit; [by iExists _|]. iPureIntro=> Φ.
      apply big_sepM_insert, not_elem_of_dom_1, is_fresh. }
    apply auth_update_alloc. rewrite !fmap_insert.
    apply gmap_local_update=> j. case: (decide (i = j))=> [<-|?];
      [|by rewrite !lookup_insert_ne].
    rewrite !lookup_insert lookup_fmap Lmi lookup_empty.
    apply local_update_unital_discrete=>/= L _ eq. split.
    { split; [done|]=>/= ?. rewrite lookup_fmap. by case: (_ !! _). }
    rewrite left_id in eq. rewrite -eq. apply Some_proper.
    split; [split|]=>/=; [by rewrite agree_idemp|done|].
    rewrite fmap_insert. rewrite -insert_singleton_op; [done|].
    rewrite lookup_fmap. apply fmap_None, not_elem_of_dom_1, is_fresh.
  Qed.
  (** Create new borrowers w.r.t. [lend_stm_tok] *)
  Local Lemma lend_stm_new_bors {Lm i α C Bm Bl} :
    Lm !! i = Some (α, C, Bm)' →
    lend_stm_tok Lm ==∗ ∃ Bm', lend_stm_tok (<[i := (α, C, Bm')']> Lm) ∗
      ([∗ list] B ∈ Bl, ∃ j, bor_itok i j α B) ∗
      ⌜∀ Φ : _ → iProp Σ,
        ([∗ map] B ∈ Bm', Φ B) ⊣⊢ ([∗ list] B ∈ Bl, Φ B) ∗ [∗ map] B ∈ Bm, Φ B⌝.
  Proof.
    move=> ?. elim: Bl=> /=[|B Bl IH].
    { iIntros "●". iModIntro. iExists Bm. rewrite insert_id; [|done].
      iFrame "●". iSplit; [done|]. iPureIntro=> ?. by rewrite left_id. }
    iIntros "●". iMod (IH with "●") as (Bm') "[●[$ %eq]]".
    iMod (lend_stm_new_bor with "●") as (Bm'') "[●[$ %eq']]";
      [by rewrite lookup_insert|].
    rewrite insert_insert. iModIntro. iExists _. iSplit; [done|].
    iPureIntro=> ?. by rewrite -assoc -eq.
  Qed.
End borrow.

(** ** World satisfactions *)

Section borrow.
  Context `{!borrowGS PROP Σ}.
  Implicit Type (M : iProp Σ → iProp Σ) (intp : PROP → iProp Σ)
    (P Q : PROP) (B : bor_st PROP) (Bm : bor_stm PROP) (C : lend_cst PROP).

  (** World satisfaction for a borrower *)
  Local Definition bor_wsat M intp α d B : iProp Σ :=
    let '(Q, b)' := B in match b with
    | Clsd => intp Q | Open q => q.[α]
    | Rebor β => lend_dtok (α ⊓ β) (S d) Q
    end.

  (** World satisfaction for a lender *)
  Local Definition lend_wsat' M intp α d P Bm : iProp Σ :=
    ([∗ map] B ∈ Bm, bor_wsat M intp α d B) ∗
    ([†α] -∗ ([∗ map] '(Q, _)' ∈ Bm, intp Q) -∗ M (intp P)).
  Local Definition lend_wsat M intp α C Bm : iProp Σ :=
    let '(d, P, l)' := C in match l with
    | Lend => lend_wsat' M intp α d P Bm | Dead => [†α]%I
    end.

  (** World satisfaction for the borrowing machinery *)
  Local Definition borrow_wsat' M intp g : iProp Σ :=
    gdepth g ∗ ∃ Lm, lend_stm_tok Lm ∗
      [∗ map] '(α, C, Bm)' ∈ Lm, lend_wsat M intp α C Bm.
  Local Definition borrow_wsat_def M intp : iProp Σ :=
    ∃ g, borrow_wsat' M intp g.
  Local Definition borrow_wsat_aux : seal borrow_wsat_def.
  Proof. by eexists. Qed.
  Definition borrow_wsat := borrow_wsat_aux.(unseal).
  Local Lemma borrow_wsat_unseal : borrow_wsat = borrow_wsat_def.
  Proof. exact: borrow_wsat_aux.(seal_eq). Qed.

  (** Non-expansiveness *)
  #[export] Instance bor_wsat_ne `{!GenUpd _ M} :
    Proper (pointwise_relation _ (⊣⊢) ==> (=) ==> (=) ==> (=) ==> (⊣⊢))
      (bor_wsat M).
  Proof. move=> ?? eq ??<-??<-[?[|?|?]]?<-; by rewrite /bor_wsat/= ?eq. Qed.
  #[export] Instance lend_wsat'_ne `{!GenUpd _ M} :
    Proper (pointwise_relation _ (⊣⊢) ==> (=) ==> (=) ==> (=) ==> (=) ==> (⊣⊢))
      (lend_wsat' M).
  Proof. move=> ?????<-??<-??<-??<-. rewrite /lend_wsat'. repeat f_equiv. Qed.
  #[export] Instance lend_wsat_ne `{!GenUpd _ M} :
    Proper (pointwise_relation _ (⊣⊢) ==> (=) ==> (=) ==> (=) ==> (⊣⊢))
      (lend_wsat M).
  Proof.
    move=> ?????<-[?[?[|]]]?<-??<-; rewrite /lend_wsat/=; repeat f_equiv.
  Qed.
  #[export] Instance borrow_wsat'_ne `{!GenUpd _ M} :
    Proper (pointwise_relation _ (⊣⊢) ==> (=) ==> (⊣⊢)) (borrow_wsat' M).
  Proof. move=> ?????<-. rewrite /borrow_wsat'. repeat f_equiv. Qed.
  #[export] Instance borrow_wsat_ne `{!GenUpd _ M} :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (borrow_wsat M).
  Proof.
    move=> ???. rewrite borrow_wsat_unseal /borrow_wsat_def/=. repeat f_equiv.
  Qed.

  (** Create a borrower and a lender *)
  Lemma bor_lend_create' `{!GenUpd _ M} {intp} α P :
    intp P =[borrow_wsat M intp]=∗ bor_ctok α P ∗ lend_tok α P.
  Proof.
    rewrite borrow_wsat_unseal bor_ctok_unseal lend_tok_unseal.
    iIntros "P [%g[g[%Lm[● Lm]]]]". iMod depth_0 as "d".
    iMod (lend_stm_create with "●") as (??) "[●[c l]]"; [done..|]. iModIntro.
    iSplitR "c l d"; last first.
    { iSplitL "c".
      { iRight. iExists _. iSplitR; [iApply lft_sincl_refl|]. by iExists _, _. }
      iExists _. iSplitR; [iApply lft_sincl_refl|]. iExists _. iFrame "d".
      by iExists _. }
    iExists _. iFrame "g". iExists _. iFrame "●".
    iApply (big_sepM_insert_2 with "[P] Lm")=>/=.
    iSplitL; rewrite big_sepM_singleton /=; by [iLeft|iIntros].
  Qed.
  Lemma bor_lend_create `{!GenUpd _ M} {intp} α P :
    intp P =[borrow_wsat M intp]=∗ bor_tok α P ∗ lend_tok α P.
  Proof. rewrite -bor_ctok_tok. by apply bor_lend_create'. Qed.

  (** Extend the lender token *)
  Lemma lend_extend `{!GenUpd _ M} {intp α P} Q :
    lend_tok α P -∗ (intp P -∗ M (intp Q)) =[borrow_wsat M intp]=∗
      lend_tok α Q.
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "[%α'[#?[%d[d[%i l]]]]] PQ [%g[g[%Lm[● Lm]]]]".
    iDestruct (lend_stm_lend_agree with "● l") as %[Bm ?].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iMod (lend_stm_lend_extend with "● l") as "[● l]"; [done|]. iModIntro.
    iSplitR "d l"; last first.
    { iExists _. iSplitR; [done|]. iExists _. iFrame "d". by iExists _. }
    iExists _. iFrame "g". iExists _. iFrame "●". iApply "→Lm"=>/=.
    iDestruct "L" as "[$ →P]"=>/=. iIntros "#† Bm".
    iMod ("→P" with "† Bm") as "P". iApply ("PQ" with "P").
  Qed.

  (** [bor_wsat] with the dead lifetime token *)
  Local Lemma bor_wsat_dead {M intp α d Q b} :
    [†α] -∗ bor_wsat M intp α d (Q, b)' -∗
      intp Q ∨ ∃ β, lend_dtok (α ⊓ β) (S d) Q.
  Proof.
    case b=> [|q|?]; [iIntros; by iLeft| |iIntros; iRight; by iExists _].
    iIntros "† q". iDestruct (lft_tok_dead with "q †") as "[]".
  Qed.
  Local Lemma bor_wsat_list_dead `{!GenUpd _ M} {intp α d Bl} {p q : iProp _} :
    [†α] -∗ ([∗ list] B ∈ Bl, bor_wsat M intp α d B) -∗
    (([∗ list] '(Q, _)' ∈ Bl, intp Q) -∗ p -∗ M q) -∗ ∃ Ql,
      ([∗ list] Q ∈ Ql, ∃ β, lend_dtok (α ⊓ β) (S d) Q) ∗
      (([∗ list] Q ∈ Ql, intp Q) -∗ p -∗ M q).
  Proof.
    move: p. elim: Bl=>/= [|[Q b] Bl IH p].
    { iIntros. iExists []. by iSplit. } iIntros "#† [B Bl] →q".
    iDestruct (IH (_∗_)%I with "† Bl [→q]") as (Ql) "[Ql →q]".
    { iIntros "Bl [Q p]". by iApply ("→q" with "[$Bl Q] p"). }
    iDestruct (bor_wsat_dead with "† B") as "[Q|l]";
      [iExists Ql|iExists (Q :: Ql)]=>/=; iFrame "Ql"; [|iFrame "l"];
      [iIntros "Ql p"|iIntros "[Q Ql] p"]; iApply ("→q" with "Ql [$Q $p]").
  Qed.
  (** [lend_wsat'] with the dead lifetime token *)
  Local Lemma big_sepM_map_to_list_snd (Φ : _ → iProp Σ) Bm :
    ([∗ map] B ∈ Bm, Φ B) ⊣⊢ [∗ list] B ∈ (map_to_list Bm).*2, Φ B.
  Proof. by rewrite big_sepM_map_to_list big_sepL_fmap. Qed.
  Local Lemma lend_wsat'_dead `{!GenUpd _ M} {intp α d P Bm} :
    [†α] -∗ lend_wsat' M intp α d P Bm -∗ ∃ Ql,
      ([∗ list] Q ∈ Ql, ∃ β, lend_dtok (α ⊓ β) (S d) Q) ∗
      (([∗ list] Q ∈ Ql, intp Q) -∗ M (intp P)).
  Proof.
    iIntros "#† [Bl →P]". iDestruct ("→P" with "†") as "→P".
    rewrite !big_sepM_map_to_list_snd. move: (map_to_list Bm).*2=> Bl.
    iDestruct (bor_wsat_list_dead (p:=True) with "† Bl [→P]") as (Ql) "[Ql →P]".
    { iIntros "Bl _".  by iApply ("→P" with "Bl"). }
    iExists _. iFrame "Ql". iIntros "Ql". by iApply ("→P" with "Ql").
  Qed.
  (** Retrieve from the lender token with remaining lender tokens *)
  Local Lemma lend_pre_retrieve `{!GenUpd _ M} {intp g α d P} :
    [†α] -∗ lend_dtok α d P =[borrow_wsat' M intp g]=∗ ∃ Ql,
      ([∗ list] Q ∈ Ql, ∃ β, lend_dtok (α ⊓ β) (S d) Q) ∗
      (([∗ list] Q ∈ Ql, intp Q) -∗ M (intp P)).
  Proof.
    iIntros "#† [d[%i l]] [$[%Lm[● Lm]]]".
    iDestruct (lend_stm_lend_agree with "● l") as %[Bm ?].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat'_dead with "† L") as "$". iExists _.
    iMod (lend_stm_lend_retrieve with "● l") as "$"; by [|iApply "→Lm"].
  Qed.
  (** Retrieve from the lender token,
    by induction on (the maximum depth minus) the depth *)
  Local Lemma lend_retrieve' `{!GenUpd _ M} {intp k α d P} :
    [†α] -∗ lend_dtok α d P =[borrow_wsat' M intp (d + k)]=∗ M (intp P).
  Proof.
    move: α d P. elim: k=> [|k IH] α d P; iIntros "#† l";
      iMod (lend_pre_retrieve with "† l") as (Ql) "[Ql →P]".
    { case: Ql=> /=[|??]. { by iDestruct ("→P" with "[//]") as "$". }
      iDestruct "Ql" as "[[%[Sd _]]_]". iIntros "[g _]".
      iDestruct (depth_bound with "g Sd") as %?. lia. }
    have -> : d + S k = S d + k by lia. iInduction Ql as [|Q Ql] "IH"=>/=.
    { by iDestruct ("→P" with "[//]") as "$". }
    iDestruct "Ql" as "[[%β l] Ql]".
    iMod (IH with "[†] l") as "Q"; [by rewrite lft_dead_meet_l|].
    iApply ("IH" with "Ql"). iIntros "Ql". iMod "Q". iApply "→P". iFrame.
  Qed.
  Lemma lend_retrieve `{!GenUpd _ M} {intp α P} :
    [†α] -∗ lend_tok α P =[borrow_wsat M intp]=∗ M (intp P).
  Proof.
    rewrite lend_tok_unseal borrow_wsat_unseal.
    iIntros "#† [%α'[#?[%d[d l]]]] [%g[g W]]".
    iDestruct (depth_bound with "g d") as %le. move: le=> /Nat.le_sum[?->].
    iMod (lend_retrieve' with "[†] [$d $l] [$g $W]") as "[W $]";
      [by iApply lft_sincl_dead_acc|by iExists _].
  Qed.

  (** [lend_wsat] with a lifetime token *)
  Local Lemma lend_wsat_tok {M intp α d Q l Bm q} :
    q.[α] -∗ lend_wsat M intp α (d, Q, l)' Bm -∗ ⌜l = Lend⌝.
  Proof.
    iIntros "α †". case: l; by [|iDestruct (lft_tok_dead with "α †") as "[]"].
  Qed.
  (** Update the borrower state to [Open q] *)
  Local Lemma bor_open_core {M intp i j α P b q} :
    q.[α] -∗ bor_itok i j α (P, b)' =[borrow_wsat M intp]=∗
      bor_otok α P q ∗ (∃ d, bor_wsat M intp α d (P, b)').
  Proof.
    rewrite borrow_wsat_unseal. iIntros "[α α'] b [%g[g[%Lm[● Lm]]]]".
    iDestruct (lend_stm_bor_agree with "● b") as %[[d[Q l]][Bm[??]]].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat_tok with "α L") as %->. iDestruct "L" as "[Bm →Q]"=>/=.
    iDestruct (big_sepM_insert_acc with "Bm") as "[B →Bm]"; [done|].
    iMod (lend_stm_bor_stupd with "● b") as "[● o]"; [done..|]. iModIntro.
    iSplitR "α o B"; last first.
    { iSplitR "B"; [|by iExists _]. rewrite bor_otok_unseal.
      iExists α, q. iSplitR; [iApply lft_sincl_refl|]. iSplitR; [by iIntros|].
      iFrame "α". by iExists _, _. }
    iExists _. iFrame "g". iExists _. iFrame "●". iApply "→Lm".
    iSplitR "→Q"=>/=; [by iApply "→Bm"|]. iStopProof.  do 2 f_equiv.
    apply bi.equiv_entails_1_1. by apply: big_sepM_insert_override.
  Qed.
  (** Open a closed borrower *)
  Lemma bor_open' {M intp q α P} :
    q.[α] -∗ bor_ctok α P =[borrow_wsat M intp]=∗ bor_otok α P q ∗ intp P.
  Proof.
    rewrite bor_ctok_unseal. iIntros "α [†|[%α'[#?[%i[%j c]]]]]".
    { by iDestruct (lft_tok_dead with "α †") as "[]". }
    iMod (lft_sincl_tok_acc with "[//] α") as (r) "[α' →α]".
    iMod (bor_open_core with "α' c") as "[o[%d $]]".
    iApply (bor_otok_lft with "[//] →α o").
  Qed.
  (** Open a borrower, possibly retrieving reborrowing *)
  Lemma bor_open `{!GenUpd _ M} {intp q α P} :
    q.[α] -∗ bor_tok α P =[borrow_wsat M intp]=∗ bor_otok α P q ∗ M (intp P).
  Proof.
    rewrite bor_tok_unseal. iIntros "α [c|[%α'[#?[%i[%j[%β[† r]]]]]]]".
    { by iMod (bor_open' with "α c") as "[$$]". }
    iMod (lft_sincl_tok_acc with "[//] α") as (r') "[α' →α]".
    iMod (bor_open_core with "α' r") as "[o[%d l]]".
    iDestruct (bor_otok_lft with "[//] →α o") as "$". rewrite lft_dead_meet_r.
    iApply (lend_retrieve with "† [l]"). rewrite lend_tok_unseal. iExists _.
    iSplitR; by [iApply lft_sincl_refl|iExists _].
  Qed.

  (** Close a borrower with subdivision *)
  Lemma bor_subdiv' `{!GenUpd _ M} {intp q α P} Ql :
    bor_otok α P q -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗ M (intp P)) =[borrow_wsat M intp]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, bor_ctok α Q).
  Proof.
    rewrite bor_otok_unseal borrow_wsat_unseal.
    iIntros "[%α'[%r[#?[→α[α'[%i[%j o]]]]]]] Ql →P [%g[g[%Lm[● Lm]]]]".
    iDestruct (lend_stm_bor_agree with "● o") as %[[d[R l]][Bm[??]]].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat_tok with "α' L") as %->=>/=.
    iMod (lend_stm_bor_delete with "● o") as (Bm') "[● %eq]"; [done..|].
    iMod (lend_stm_new_bors (i:=i) (Bl:=(λ Q,(Q,Clsd)') <$> Ql) with "●") as
      (Bm'') "[● [bl %eq']]"; [by rewrite lookup_insert|]. iModIntro.
    rewrite insert_insert big_sepL_fmap. iDestruct "L" as "[Bm →R]".
    rewrite !eq. iDestruct "Bm" as "[+α' Bm']".
    iDestruct ("→α" with "[$α' $+α'//]") as "$". iSplitR "bl"; last first.
    { iApply (big_sepL_impl with "bl"). iIntros "!> %% _ [%j' ?]".
      rewrite bor_ctok_unseal. iRight. iExists _. iSplit; [done|].
      by iExists _, _. }
    iExists _. iFrame "g". iExists _. iFrame "●". iApply "→Lm"=>/=.
    iSplitL "Bm' Ql"; rewrite !eq' !big_sepL_fmap /=; [by iFrame|].
    iIntros "#† [Ql Bm]". iMod ("→P" with "[†] Ql") as "P".
    { by iApply lft_sincl_dead_acc. } iApply ("→R" with "†"). iFrame.
  Qed.
  Lemma bor_subdiv `{!GenUpd _ M} {intp q α P} Ql :
    bor_otok α P q -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗ M (intp P)) =[borrow_wsat M intp]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, bor_tok α Q).
  Proof.
    iIntros "o Ql →P". iMod (bor_subdiv' with "o Ql →P") as "[$ Ql]".
    iModIntro. iStopProof. do 3 f_equiv. exact bor_ctok_tok.
  Qed.

  (** Simply close the borrower *)
  Lemma bor_close' `{!GenUpd _ M} {intp q α P} :
    bor_otok α P q -∗ intp P =[borrow_wsat M intp]=∗ q.[α] ∗ bor_ctok α P.
  Proof.
    iIntros "o P". iMod (bor_subdiv' [P] with "o [P] []") as "[$[$_]]"=>/=;
      by [iFrame|iIntros "_[$_]"|].
  Qed.
  Lemma bor_close `{!GenUpd _ M} {intp q α P} :
    bor_otok α P q -∗ intp P =[borrow_wsat M intp]=∗ q.[α] ∗ bor_tok α P.
  Proof. rewrite -bor_ctok_tok. by exact bor_close'. Qed.

  (** Reborrow a borrower *)
  Lemma bor_reborrow' `{!GenUpd _ M} {intp β R r} α :
    bor_otok β R r -∗ intp R =[borrow_wsat M intp]=∗
      r.[β] ∗ bor_ctok (α ⊓ β) R ∗ ([†α] -∗ bor_tok β R).
  Proof.
    rewrite bor_otok_unseal borrow_wsat_unseal.
    iIntros "[%β'[%s[#?[→β[β'[%i[%j o]]]]]]] R [%g[g[%Lm[● Lm]]]]".
    iDestruct (lend_stm_bor_agree with "● o") as %[[d[Q l]][Bm[??]]].
    iDestruct (big_sepM_insert_acc with "Lm") as "[L →Lm]"; [done|]=>/=.
    iDestruct (lend_wsat_tok with "β' L") as %->.
    iMod (lend_stm_bor_stupd (B':=(_,Rebor α)') with "● o") as "[● r]";
      [done..|].
    iMod (lend_stm_create with "●") as (i' j') "[● [c l]]"; [done..|].
    iMod (depth_alloc with "g") as (g') "[g d]". iModIntro.
    iDestruct "L" as "[Bm →Q]"=>/=.
    iDestruct (big_sepM_insert_acc with "Bm") as "[B →Bm]"; [done|].
    iDestruct ("→β" with "[$β' $B//]") as "$". iSplitR "c r"; last first.
    { rewrite bor_tok_unseal bor_ctok_unseal. iSplitL "c"; last first.
      { iIntros "?". iRight. iExists _. iSplit; [done|]. iExists _, _, _.
        iFrame. }
      iRight. iExists _. iSplit; by [iApply lft_sincl_meet_mono_r|iExists _, _].
    }
    iExists _. iFrame "g". iExists _. iFrame "●".
    iApply (big_sepM_insert_2 with "[R]")=>/=.
    { iSplitL; rewrite big_sepM_singleton /=; by [|iIntros]. }
    iApply "→Lm". iSplitR "→Q"=>/=.
    { iApply "→Bm". iFrame "d". rewrite comm. by iExists _. }
    iClear "#". iStopProof. do 2 f_equiv. apply bi.equiv_entails_1_1.
    by apply: big_sepM_insert_override.
  Qed.
  Lemma bor_reborrow `{!GenUpd _ M} {intp β R r} α :
    bor_otok β R r -∗ intp R =[borrow_wsat M intp]=∗
      r.[β] ∗ bor_tok (α ⊓ β) R ∗ ([†α] -∗ bor_tok β R).
  Proof. rewrite -bor_ctok_tok. by apply bor_reborrow'. Qed.
End borrow.

(** Allocate [borrow_wsat] *)
Lemma borrow_wsat_alloc `{!borrowGpreS PROP Σ} :
  ⊢ |==> ∃ _ : borrowGS PROP Σ, ∀ M intp, borrow_wsat M intp.
Proof.
  iMod (own_alloc (● (MaxNat 0))) as (γ) "g"; [by apply auth_auth_valid|].
  iMod (own_alloc (● (∅ : gmapR _ _))) as (γ') "●";
    [by apply auth_auth_valid|]. iModIntro.
  iExists (BorrowGS _ _ _ _ _ γ γ'). iIntros (M intp).
  rewrite borrow_wsat_unseal. iExists _. iFrame "g". iExists ∅. by iFrame.
Qed.

(** ** Fractured borrowing *)

(** State of a fractured borrower *)
Local Definition fbor_st PROP : Type := lft *' (Qp → PROP).
(** State of all the fractured borrowers *)
Local Definition fbor_stm PROP : Type := gmap positive (fbor_st PROP).

(** Ghost state for fractured borrowing *)
Class fborrowGS PROP Σ := FborrowGS {
  fborrowGS_in :: ghost_mapG Σ positive (fbor_st PROP);
  fborrow_name : gname;
}.
Class fborrowGpreS PROP Σ :=
  fborrowGpreS_in :: ghost_mapG Σ positive (fbor_st PROP).
Definition fborrowΣ PROP : gFunctors := ghost_mapΣ positive (fbor_st PROP).
#[export] Instance subG_fborrow `{!subG (fborrowΣ PROP) Σ} :
  fborrowGpreS PROP Σ.
Proof. solve_inG. Qed.

Section fborrow.
  Context `{!fborrowGS PROP Σ, !borrowGS PROP Σ}.
  Implicit Type (Φ : Qp → PROP) (F : fbor_stm PROP).

  (** Fractional borrower token *)
  Definition fbor_tok_def α Φ : iProp Σ :=
    ∃ α', α ⊑s α' ∗ ∃ i, i ↪[fborrow_name]□ (α', Φ)'.
  Lemma fbor_tok_aux : seal (@fbor_tok_def). Proof. by eexists. Qed.
  Definition fbor_tok := fbor_tok_aux.(unseal).
  Lemma fbor_tok_unseal : @fbor_tok = @fbor_tok_def.
  Proof. exact: fbor_tok_aux.(seal_eq). Qed.

  (** [fbor_tok] is persistent *)
  #[export] Instance fbor_tok_persistent α Φ : Persistent (fbor_tok α Φ).
  Proof. rewrite fbor_tok_unseal. apply _. Qed.

  (** Modify the lifetime of [fbor_tok] *)
  Lemma fbor_tok_lft {α α' Φ} : α' ⊑s α -∗ fbor_tok α Φ -∗ fbor_tok α' Φ.
  Proof.
    rewrite fbor_tok_unseal. iIntros "#? [%α''[#? f]]". iExists _. iFrame "f".
    by iApply lft_sincl_trans.
  Qed.

  (** World satisfaction for the fractional borrowing machinery *)
  Definition fborrow_wsat_def : iProp Σ :=
    ∃ F, ghost_map_auth fborrow_name 1 F ∗
      ([∗ map] '(α, Φ)' ∈ F, ∃ q, bor_ctok α (Φ q)).
  Lemma fborrow_wsat_aux : seal fborrow_wsat_def. Proof. by eexists. Qed.
  Definition fborrow_wsat := fborrow_wsat_aux.(unseal).
  Lemma fborrow_wsat_unseal : fborrow_wsat = fborrow_wsat_def.
  Proof. exact: fborrow_wsat_aux.(seal_eq). Qed.

  (** Turn [bor_ctok] into [fbor_tok] *)
  Lemma bor_fbor' {α Φ q} : bor_ctok α (Φ q) =[fborrow_wsat]=∗ fbor_tok α Φ.
  Proof.
    rewrite fborrow_wsat_unseal. iIntros "c [%F[● F]]".
    iMod (ghost_map_insert_persist with "●") as "[● i]";
      [apply not_elem_of_dom_1, is_fresh|]. iModIntro.
    iDestruct (big_sepM_insert_2 _ _ _ (_,_)' with "[c] F") as "F";
      [by iExists q|].
    iSplitR "i"; [iExists _; iFrame|]. rewrite fbor_tok_unseal. iExists _.
    iSplit; by [iApply lft_sincl_refl|iExists _].
  Qed.
  Lemma bor_fbor `{!GenUpd _ M} {intp α Φ q r} :
    bor_otok α (Φ q) r -∗ intp (Φ q) =[fborrow_wsat ∗ borrow_wsat M intp]=∗
      fbor_tok α Φ ∗ r.[α].
  Proof.
    iIntros "o Φ". iMod (bor_close' with "o Φ") as "[$ c]".
    by iMod (bor_fbor' with "c") as "$".
  Qed.

  (** Get [fbor_tok] from borrow subdivision *)
  Lemma bor_subdivf' `{!GenUpd _ M} {intp q α P} Ql Φrl :
    bor_otok α P q -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([∗ list] '(Φ, r)' ∈ Φrl, intp (Φ r)) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
      ([∗ list] '(Φ, r)' ∈ Φrl, intp (Φ r)) -∗ M (intp P))
      =[fborrow_wsat ∗ borrow_wsat M intp]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, bor_ctok α Q) ∗
      [∗ list] '(Φ, r)' ∈ Φrl, fbor_tok α Φ.
  Proof.
    iIntros "o Ql Φrl →P".
    iMod (bor_subdiv' (Ql ++ ((λ '(Φ, r)', Φ r) <$> Φrl))
      with "o [$Ql Φrl] [→P]") as "[$[$ cl]]"; [by rewrite big_sepL_fmap| |].
    { iIntros "† [Ql Φrl]". rewrite big_sepL_fmap.
      iApply ("→P" with "† Ql Φrl"). }
    iStopProof. elim: Φrl=> [|[Φ r] Φrl IH]/=; [by iIntros|].
    iIntros "[b bl]". iMod (IH with "bl") as "$". by iMod (bor_fbor' with "b").
  Qed.
  Lemma bor_subdivf `{!GenUpd _ M} {intp q α P} Ql Φrl :
    bor_otok α P q -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
    ([∗ list] '(Φ, r)' ∈ Φrl, intp (Φ r)) -∗
    ([†α] -∗ ([∗ list] Q ∈ Ql, intp Q) -∗
      ([∗ list] '(Φ, r)' ∈ Φrl, intp (Φ r)) -∗ M (intp P))
      =[fborrow_wsat ∗ borrow_wsat M intp]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, bor_tok α Q) ∗
      [∗ list] '(Φ, r)' ∈ Φrl, fbor_tok α Φ.
  Proof.
    iIntros "o Ql Φrl →P". iMod (bor_subdivf' with "o Ql Φrl →P") as "[$[? $]]".
    iModIntro. iStopProof. do 3 f_equiv. exact bor_ctok_tok.
  Qed.

  (** Open [fbor_tok] *)
  Lemma fbor_open `{!GenUpd _ M} {intp α q} `(Fractional _ (intp ∘ Φ)) :
    q.[α] -∗ fbor_tok α Φ =[fborrow_wsat ∗ borrow_wsat M intp]=∗
      ∃ r, bor_otok α (Φ r) q ∗ intp (Φ r).
  Proof.
    rewrite fbor_tok_unseal fborrow_wsat_unseal.
    iIntros "α [%α'[#?[%i i]]] [[%F[● F]]W]".
    iMod (lft_sincl_tok_acc with "[//] α") as (s) "[α' →α]".
    iDestruct (ghost_map_lookup with "● i") as %?.
    iDestruct (big_sepM_lookup_acc with "F") as "[[%r c]→F]"; [done|]=>/=.
    iMod (bor_open' with "α' c W") as "[W[o Φ]]".
    have eq : intp (Φ r) ⊣⊢ intp (Φ (r/2)%Qp) ∗ intp (Φ (r/2)%Qp).
    { by erewrite fractional_half; [|apply: fractional_as_fractional]. }
    rewrite eq. iDestruct "Φ" as "[Φ Φ']".
    iMod (bor_subdiv' [_;_] with "o [Φ Φ'] [] W") as "[W[α'[c[c' _]]]]".
    { by iFrame. } { rewrite eq. by iIntros "_ [$[$ _]]". }
    iMod (bor_open' with "α' c' W") as "[$[o Φ]]". iModIntro.
    iDestruct (bor_otok_lft with "[//] →α o") as "o".
    iSplitR "o Φ"; [|iExists _; by iFrame]. iExists _. iFrame "●". iApply "→F".
    by iExists _.
  Qed.
End fborrow.

(** Allocate [fborrow_wsat] *)
Lemma fborrow_wsat_alloc `{!fborrowGpreS PROP Σ, !borrowGS PROP Σ} :
  ⊢ |==> ∃ _ : fborrowGS PROP Σ, fborrow_wsat.
Proof.
  iMod ghost_map_alloc_empty as (γ) "●". iModIntro. iExists (FborrowGS _ _ _ γ).
  rewrite fborrow_wsat_unseal. iExists ∅. by iFrame.
Qed.
