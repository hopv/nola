(** * Borrowing machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export borrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation FunNPNotation iPropAppNotation UpdwNotation LftNotation
  DsemNotation.

Implicit Type FM : ofe.

(** ** [borrow_judgty]: Judgment type for [borrow] *)
Variant borrow_judg_id FM := .
Definition borrow_judgty (FM : ofe) : ofe :=
  (** Accessor judgment *) tagged (borrow_judg_id FM) (FM * FM).

(** ** [BorrowJudg]: Judgment structure for [borrow] *)
Notation BorrowJudg FM JUDG := (Ejudg (borrow_judgty FM) JUDG).

Section borrow_deriv.
  Context `{!borrowGS FML Σ, borrow_judg : !BorrowJudg (FML $oi Σ) JUDG}.
  Implicit Type δ : JUDG -n> iProp Σ.

  (** Accessor judgment *)
  Local Definition borrow_jto Px Qx : JUDG := borrow_judg (Tagged (Px, Qx)).
  Local Instance borrow_jto_ne : NonExpansive2 borrow_jto.
  Proof. solve_proper. Qed.

  (** [bor]: Relaxed borrower *)
  Local Definition bor_def δ α Px : iProp Σ :=
    ∃ Qx, □ δ (borrow_jto Px Qx) ∗ □ δ (borrow_jto Qx Px) ∗
      bor_tok α Qx.
  Local Lemma bor_aux : seal bor_def. Proof. by eexists. Qed.
  Definition bor := bor_aux.(unseal).
  Local Lemma bor_unseal : bor = bor_def. Proof. exact: seal_eq. Qed.
  (** [obor]: Relaxed open borrower *)
  Local Definition obor_def δ α q Px : iProp Σ :=
    ∃ Qx, □ δ (borrow_jto Px Qx) ∗ □ δ (borrow_jto Qx Px) ∗
      obor_tok α q Qx.
  Local Lemma obor_aux : seal obor_def. Proof. by eexists. Qed.
  Definition obor := obor_aux.(unseal).
  Local Lemma obor_unseal : obor = obor_def. Proof. exact: seal_eq. Qed.
  (** [lend]: Relaxed lender *)
  Local Definition lend_def δ α Px : iProp Σ :=
    ∃ Qx, □ δ (borrow_jto Qx Px) ∗ lend_tok α Qx.
  Local Lemma lend_aux : seal lend_def. Proof. by eexists. Qed.
  Definition lend := lend_aux.(unseal).
  Local Lemma lend_unseal : lend = lend_def. Proof. exact: seal_eq. Qed.

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance bor_ne {δ α} : NonExpansive (bor δ α).
  Proof. rewrite bor_unseal. solve_proper. Qed.
  #[export] Instance bor_proper {δ α} : Proper ((≡) ==> (⊣⊢)) (bor δ α).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance obor_ne {δ α q} : NonExpansive (obor δ α q).
  Proof. rewrite obor_unseal. solve_proper. Qed.
  #[export] Instance obor_proper {δ α q} : Proper ((≡) ==> (⊣⊢)) (obor δ α q).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance lend_ne {δ α} : NonExpansive (lend δ α).
  Proof. rewrite lend_unseal. solve_proper. Qed.
  #[export] Instance lend_proper {δ α} : Proper ((≡) ==> (⊣⊢)) (lend δ α).
  Proof. apply ne_proper, _. Qed.
End borrow_deriv.

(** Notation *)
Notation bord := (bor der). Notation obord := (obor der).
Notation lendd := (lend der).

Section borrow_deriv.
  Context `{!BorrowJudg (FML $oi Σ) JUDG, !Jsem JUDG (iProp Σ),
    !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : FML $oi Σ).

  (** ** [borrow_judg_sem]: Semantics of [borrow_judgty] *)
  Definition borrow_judg_sem δ (PQx : borrow_judgty (FML $oi Σ)) : iProp Σ :=
    ⟦ PQx.(untag).1 ⟧(δ) ==∗ ⟦ PQx.(untag).2 ⟧(δ).
  (** [borrow_judg_sem] is non-expansive *)
  #[export] Instance borrow_judg_sem_ne {δ} : NonExpansive (borrow_judg_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [borrow_judgty] *)
  #[export] Instance borrow_judg_dsem
    : Dsem JUDG (borrow_judgty (FML $oi Σ)) (iProp Σ) := DSEM borrow_judg_sem _.
End borrow_deriv.

(** ** [BorrowJsem]: Judgment semantics for [borrow] *)
Notation BorrowJsem FML Σ JUDG :=
  (Ejsem (borrow_judgty (FML $oi Σ)) JUDG (iProp Σ)).

Section borrow_deriv.
  Context `{!borrowGS FML Σ, !BorrowJudg (FML $oi Σ) JUDG, !Jsem JUDG (iProp Σ),
    !Dsem JUDG (FML $oi Σ) (iProp Σ), !BorrowJsem FML Σ JUDG,
    !Deriv (JUDG:=JUDG) ih δ}.
  Implicit Type (Px Qx : FML $oi Σ) (δ : JUDG -n> iProp Σ).

  (** Lemmas for [borrow_judg] *)
  Local Lemma borrow_jto_refl {Px} : ⊢ δ (borrow_jto Px Px).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite sem_ejudg. by iIntros "$".
  Qed.
  Local Lemma borrow_jto_trans {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    δ (borrow_jto Qx Rx) -∗ δ (borrow_jto Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !sem_ejudg.
    iIntros "QR Px". iMod ("big" with "[//] [//] [//] Px"). by iApply "QR".
  Qed.
  Local Lemma borrow_jto_trans' {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Qx ⟧(δ') ==∗ ⟦ Rx ⟧(δ'))
      -∗ δ (borrow_jto Px Qx) -∗ δ (borrow_jto Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !sem_ejudg.
    iIntros "PQ Px". iMod ("PQ" with "Px"). by iApply "big".
  Qed.
  Local Lemma der_borrow_jto {Px Qx} :
    der (borrow_jto Px Qx) ⊢ (⟦ Px ⟧ ==∗ ⟦ Qx ⟧).
  Proof. by rewrite der_sound sem_ejudg. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma bor_to {α Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    bor δ α Px -∗ bor δ α Qx.
  Proof.
    rewrite bor_unseal. iIntros "#PQ #QP (%Rx & #PR & #RP & $)".
    iSplit; [iApply (borrow_jto_trans with "QP PR")|
      iApply (borrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma obor_to {α q Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    obor δ α q Px -∗ obor δ α q Qx.
  Proof.
    rewrite obor_unseal. iIntros "#PQ #QP (%Rx & #PR & #RP & $)".
    iSplit; [iApply (borrow_jto_trans with "QP PR")|
      iApply (borrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma lend_to {α Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    lend δ α Px -∗ lend δ α Qx.
  Proof.
    rewrite lend_unseal. iIntros "#PQ (%Rx & #RP & $)".
    iApply (borrow_jto_trans' with "PQ RP").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma bor_lft {α β Px} : β ⊑□ α -∗ bor δ α Px -∗ bor δ β Px.
  Proof.
    rewrite bor_unseal. iIntros "⊑ (% & #? & #? & b)".
    iDestruct (bor_tok_lft with "⊑ b") as "$". by iSplit.
  Qed.
  Lemma obor_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor δ α q Px -∗ obor δ β r Px.
  Proof.
    rewrite obor_unseal. iIntros "⊑ → (% & #? & #? & o)".
    iDestruct (obor_tok_lft with "⊑ → o") as "$". by iSplit.
  Qed.
  Lemma lend_lft {α β Px} : α ⊑□ β -∗ lend δ α Px -∗ lend δ β Px.
  Proof.
    rewrite lend_unseal. iIntros "⊑ (% & #? & l)".
    by iDestruct (lend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma bor_tok_bor {α Px} : bor_tok α Px ⊢ bor δ α Px.
  Proof. rewrite bor_unseal. iIntros "$". iSplit; iApply borrow_jto_refl. Qed.
  Lemma obor_tok_obor {α q Px} : obor_tok α q Px ⊢ obor δ α q Px.
  Proof. rewrite obor_unseal. iIntros "$". iSplit; iApply borrow_jto_refl. Qed.
  Lemma lend_tok_lend {α Px} : lend_tok α Px ⊢ lend δ α Px.
  Proof. rewrite lend_unseal. iIntros "$". iApply borrow_jto_refl. Qed.

  (** Fake a borrower *)
  Lemma bor_fake {α} Px : [†α] ⊢ bor δ α Px.
  Proof. by rewrite bor_tok_fake bor_tok_bor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !FromBUpd M}.

  (** Create borrowers and lenders *)
  Lemma bor_lend_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧(δ)))
      =[borrow_wsat M ⟦⟧(δ)]=∗
      ([∗ list] Px ∈ Pxl, bor δ α Px) ∗ [∗ list] Qx ∈ Qxl, lend δ α Qx.
  Proof.
    setoid_rewrite <-bor_tok_bor. setoid_rewrite <-lend_tok_lend.
    exact: bor_lend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma bor_lend_new α Px :
    ⟦ Px ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗ bor δ α Px ∗ lend δ α Px.
  Proof. rewrite -bor_tok_bor -lend_tok_lend. exact: bor_lend_tok_new. Qed.
End borrow_deriv.

Section borrow_deriv.
  Context `{!borrowGS FML Σ, !BorrowJudg (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !BorrowJsem FML Σ JUDG, !GenUpd (PROP:=iProp Σ) M, !FromBUpd M}.
  Implicit Type (Px Qx : FML $oi Σ).

  (** Split a lender *)
  Lemma lendd_split {α Px} Qxl :
    lendd α Px -∗ (⟦ Px ⟧ -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧))
      =[borrow_wsat M ⟦⟧]=∗ [∗ list] Qx ∈ Qxl, lendd α Qx.
  Proof.
    rewrite {1}lend_unseal. setoid_rewrite <-lend_tok_lend.
    iIntros "(%Rx & #RP & l) →Qxl".
    iApply (lend_tok_split (M:=M) with "l [RP →Qxl]"). iIntros "Rx".
    iMod (der_borrow_jto with "RP Rx"). by iApply "→Qxl".
  Qed.

  (** Retrive from [lendd] *)
  Lemma lendd_retrieve {α Px} :
    [†α] -∗ lendd α Px -∗ modw M (borrow_wsat M ⟦⟧) ⟦ Px ⟧.
  Proof.
    rewrite lend_unseal. iIntros "† (%Qx & #QP & l)".
    iMod (lend_tok_retrieve (M:=M) with "† l") as "Qx".
    iMod (der_borrow_jto with "QP Qx") as "$". by iIntros.
  Qed.

  (** Open a borrower *)
  Lemma bord_open {α q Px} :
    q.[α] -∗ bord α Px -∗ modw M (borrow_wsat M ⟦⟧) (obord α q Px ∗ ⟦ Px ⟧).
  Proof.
    rewrite bor_unseal obor_unseal. iIntros "α (%Qx & $ & #QP & b)".
    iMod (bor_tok_open (M:=M) with "α b") as "[$ Qx]".
    iMod (der_borrow_jto with "QP Qx") as "$". by iIntros "$".
  Qed.

  (** Lemma for [obord_merge_subdiv] *)
  Local Lemma from_sincl_obords {αqPxl β} :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ obord α q Px) ⊢
    ∃ αqRxl,
      □ (([∗ list] '(_, _, Px)' ∈ αqPxl, ⟦ Px ⟧) ==∗
        [∗ list] '(_, _, Rx)' ∈ αqRxl, ⟦ Rx ⟧) ∗
      □ (([∗ list] '(α, q, Rx)' ∈ αqRxl, q.[α] ∗ ([†β] -∗ bor_tok α Rx)) -∗
        [∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ bord α Px)) ∗
      ([∗ list] '(α, q, Rx)' ∈ αqRxl, β ⊑□ α ∗ obor_tok α q Rx).
  Proof.
    rewrite obor_unseal /=. elim: αqPxl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q Px]] αqPxl ->).
    iIntros "[[⊑(%Rx & #PR & #RP & o)] (%αqRxl & #→Rxl & #→αbdl & ol)]".
    iExists ((α, q, Rx)' :: αqRxl)=>/=. iFrame "⊑ o ol". iSplit.
    - iIntros "!> [Px Pxl]". iMod ("→Rxl" with "Pxl") as "$".
      iApply (der_borrow_jto with "PR Px").
    - iIntros "!> [[$ →b]αbl]". iDestruct ("→αbdl" with "αbl") as "$".
      iIntros "†". rewrite bor_unseal. iDestruct ("→b" with "†") as "$".
      by iSplit.
  Qed.
  (** Merge and subdivide/reborrow borrowers *)
  Lemma obord_merge_subdiv αqPxl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ obord α q Px) -∗
    ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M
      ([∗ list] '(_, _, Px)' ∈ αqPxl, ⟦ Px ⟧)) =[borrow_wsat M ⟦⟧]=∗
      ([∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ bord α Px)) ∗
      ([∗ list] Qx ∈ Qxl, bord β Qx).
  Proof.
    iIntros "big Qxl →Pxl". rewrite from_sincl_obords /=.
    iDestruct "big" as (αqRxl) "(#→Rxl & #→αbdl & ol)".
    setoid_rewrite <-(bor_tok_bor (α:=β)).
    iMod (obor_tok_merge_subdiv (M:=M) with "ol Qxl [→Pxl]") as "[αbl $]".
    - iIntros "† Qxl". iMod ("→Pxl" with "† Qxl") as "Pxl".
      by iMod ("→Rxl" with "Pxl").
    - iModIntro. by iApply "→αbdl".
  Qed.
  (** Subdivide/reborrow a borrower *)
  Lemma obord_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ obord α q Px -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M ⟦ Px ⟧) =[borrow_wsat M ⟦⟧]=∗
      q.[α] ∗ ([†β] -∗ bord α Px) ∗ ([∗ list] Qx ∈ Qxl, bord β Qx).
  Proof.
    iIntros "⊑ o Qxl →Px".
    iMod (obord_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→Px]")
      as "[[[$$]_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.

  (** Reborrow a borrower *)
  Lemma obord_reborrow {α q Px} β :
    β ⊑□ α -∗ obord α q Px -∗ ⟦ Px ⟧ =[borrow_wsat M ⟦⟧]=∗
      q.[α] ∗ ([†β] -∗ bord α Px) ∗ bord β Px.
  Proof.
    iIntros "⊑ o Px".
    iMod (obord_subdiv [Px] with "⊑ o [Px] []") as "($ & $ & $ & _)"=>/=;
      by [iFrame|iIntros "_ [$ _]"|].
  Qed.
  Lemma bord_reborrow {α q Px} β :
    β ⊑□ α -∗ q.[α] -∗ bord α Px -∗ modw M (borrow_wsat M ⟦⟧)
      (q.[α] ∗ ([†β] -∗ bord α Px) ∗ bord β Px).
  Proof.
    iIntros "⊑ α b". iMod (bord_open with "α b") as "[o Px]".
    by iMod (obord_reborrow with "⊑ o Px").
  Qed.
  (** Simply close a borrower *)
  Lemma obord_close {α q Px} :
    obord α q Px -∗ ⟦ Px ⟧ =[borrow_wsat M ⟦⟧]=∗ q.[α] ∗ bord α Px.
  Proof.
    iIntros "o Px".
    iMod (obord_reborrow with "[] o Px") as "($ & _ & $)";
      by [iApply lft_sincl_refl|].
  Qed.
End borrow_deriv.
