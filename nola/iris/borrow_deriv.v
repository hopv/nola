(** * Borrowing machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.iris Require Export borrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation PsemNotation SemNotation UpdwNotation
  LftNotation.

(** Notation *)
Notation borrow_wsati M δ := (borrow_wsat M ⟦⟧(δ)).
Notation borrow_wsatid M := (borrow_wsati M der).

(** Derivability pre-data for [borrow] *)
Class BorrowPreDeriv (FM JUDG : ofe) := BORROW_PRE_DERIV {
  (** Conversion judgment *)
  borrow_jto : FM → FM → JUDG;
  (** [borrow_jto] is non-expansive *)
  borrow_jto_ne :: NonExpansive2 borrow_jto;
}.
Hint Mode BorrowPreDeriv ! - : typeclass_instances.
Arguments BORROW_PRE_DERIV {_ _} _ {_}.

Section borrow_deriv.
  Context `{!borrowGS FML Σ, !BorrowPreDeriv (FML $oi Σ) JUDG}.
  Implicit Type δ : JUDG → iProp Σ.

  (** [bor]: Relaxed borrower *)
  Local Definition bor_def δ α Px : iProp Σ :=
    ∃ Qx, δ (borrow_jto Px Qx) ∗ δ (borrow_jto Qx Px) ∗ bor_tok α Qx.
  Local Lemma bor_aux : seal bor_def. Proof. by eexists. Qed.
  Definition bor := bor_aux.(unseal).
  Local Lemma bor_unseal : bor = bor_def. Proof. exact: seal_eq. Qed.
  (** [obor]: Relaxed open borrower *)
  Local Definition obor_def δ α q Px : iProp Σ :=
    ∃ Qx, δ (borrow_jto Px Qx) ∗ obor_tok α q Qx.
  Local Lemma obor_aux : seal obor_def. Proof. by eexists. Qed.
  Definition obor := obor_aux.(unseal).
  Local Lemma obor_unseal : obor = obor_def. Proof. exact: seal_eq. Qed.
  (** [lend]: Relaxed lender *)
  Local Definition lend_def δ α Px : iProp Σ :=
    ∃ Qx, δ (borrow_jto Qx Px) ∗ lend_tok α Qx.
  Local Lemma lend_aux : seal lend_def. Proof. by eexists. Qed.
  Definition lend := lend_aux.(unseal).
  Local Lemma lend_unseal : lend = lend_def. Proof. exact: seal_eq. Qed.

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance bor_ne `{!NonExpansive δ} {α} : NonExpansive (bor δ α).
  Proof. rewrite bor_unseal. solve_proper. Qed.
  #[export] Instance obor_ne `{!NonExpansive δ} {α q} :
    NonExpansive (obor δ α q).
  Proof. rewrite obor_unseal. solve_proper. Qed.
  #[export] Instance lend_ne `{!NonExpansive δ} {α} : NonExpansive (lend δ α).
  Proof. rewrite lend_unseal. solve_proper. Qed.
End borrow_deriv.
Notation bord := (bor der). Notation obord := (obor der).
Notation lendd := (lend der).

Section borrow_deriv.
  Context `{!BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dsem JUDGI (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (Px Qx : FML $oi Σ).

  (** Derivability data for [borrow] *)
  Class BorrowDeriv :=
    (** Interpreting [borrow_jto] *)
    borrow_jto_sem : ∀{δ Px Qx},
      ⟦ borrow_jto Px Qx ⟧(δ) ⊣⊢ (⟦ Px ⟧(δ) ==∗ ⟦ Qx ⟧(δ)).
End borrow_deriv.
Arguments BorrowDeriv FML Σ JUDGI {_ _}.
Hint Mode BorrowDeriv ! - - - - : typeclass_instances.

Section borrow_deriv.
  Context `{!borrowGS FML Σ,
  !BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dsem JUDGI (FML $oi Σ) (iProp Σ), !BorrowDeriv FML Σ JUDGI,
  !Deriv (JUDGI:=JUDGI) ih δ}.
  Implicit Type (Px Qx : FML $oi Σ) (δ : JUDGI → iProp Σ).

  (** Lemmas for [borrow_jto] *)
  Lemma borrow_jto_refl {Px} : ⊢ δ (borrow_jto Px Px).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite borrow_jto_sem.
    by iIntros "$".
  Qed.
  Lemma borrow_jto_trans {Px Qx R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    δ (borrow_jto Qx R) -∗ δ (borrow_jto Px R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !borrow_jto_sem.
    iIntros "QR Px". iMod ("big" with "[//] [//] [//] Px"). by iApply "QR".
  Qed.
  Lemma borrow_jto_trans' {Px Qx R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Qx ⟧(δ') ==∗ ⟦ R ⟧(δ')) -∗
    δ (borrow_jto Px Qx) -∗ δ (borrow_jto Px R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !borrow_jto_sem.
    iIntros "PQ Px". iMod ("PQ" with "Px"). by iApply "big".
  Qed.
  Lemma der_borrow_jto {Px Qx} :
    der (borrow_jto Px Qx) ⊢ (⟦ Px ⟧ ==∗ ⟦ Qx ⟧).
  Proof. by rewrite der_sound borrow_jto_sem. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma bor_to {α Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    bor δ α Px -∗ bor δ α Qx.
  Proof.
    rewrite bor_unseal. iIntros "PQ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (borrow_jto_trans with "QP PR")|
      iApply (borrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma obor_to {α q Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    obor δ α q Px -∗ obor δ α q Qx.
  Proof.
    rewrite obor_unseal. iIntros "QP [%R[PR $]]".
    iApply (borrow_jto_trans with "QP PR").
  Qed.
  Lemma lend_to {α Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    lend δ α Px -∗ lend δ α Qx.
  Proof.
    rewrite lend_unseal. iIntros "PQ [%R[RP $]]".
    iApply (borrow_jto_trans' with "PQ RP").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma bor_lft {α β Px} : β ⊑□ α -∗ bor δ α Px -∗ bor δ β Px.
  Proof.
    rewrite bor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (bor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma obor_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor δ α q Px -∗ obor δ β r Px.
  Proof.
    rewrite obor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (obor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma lend_lft {α β Px} : α ⊑□ β -∗ lend δ α Px -∗ lend δ β Px.
  Proof.
    rewrite lend_unseal. iIntros "⊑ [%[? l]]".
    by iDestruct (lend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma bor_tok_bor {α Px} : bor_tok α Px ⊢ bor δ α Px.
  Proof. rewrite bor_unseal. iIntros "$". iSplitL; iApply borrow_jto_refl. Qed.
  Lemma obor_tok_obor {α q Px} : obor_tok α q Px ⊢ obor δ α q Px.
  Proof. rewrite obor_unseal. iIntros "$". iApply borrow_jto_refl. Qed.
  Lemma lend_tok_lend {α Px} : lend_tok α Px ⊢ lend δ α Px.
  Proof. rewrite lend_unseal. iIntros "$". iApply borrow_jto_refl. Qed.

  (** Fake a borrower *)
  Lemma bor_fake {α} Px : [†α] ⊢ bor δ α Px.
  Proof. by rewrite bor_tok_fake bor_tok_bor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.

  (** Create borrowers and lenders *)
  Lemma bor_lend_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧(δ)))
      =[borrow_wsati M δ]=∗
      ([∗ list] Px ∈ Pxl, bor δ α Px) ∗ [∗ list] Qx ∈ Qxl, lend δ α Qx.
  Proof.
    setoid_rewrite <-bor_tok_bor. setoid_rewrite <-lend_tok_lend.
    exact: bor_lend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma bor_lend_new α Px :
    ⟦ Px ⟧(δ) =[borrow_wsati M δ]=∗ bor δ α Px ∗ lend δ α Px.
  Proof. rewrite -bor_tok_bor -lend_tok_lend. exact: bor_lend_tok_new. Qed.
End borrow_deriv.

Section borrow_deriv.
  Context `{!borrowGS FML Σ,
  !BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dsem JUDGI (FML $oi Σ) (iProp Σ), !BorrowDeriv FML Σ JUDGI,
  !GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.
  Implicit Type (Px Qx : FML $oi Σ).

  (** Split a lender *)
  Lemma lendd_split {α Px} Qxl :
    lendd α Px -∗ (⟦ Px ⟧ -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧)) =[borrow_wsatid M]=∗
      [∗ list] Qx ∈ Qxl, lendd α Qx.
  Proof.
    rewrite {1}lend_unseal. setoid_rewrite <-lend_tok_lend.
    iIntros "[%R[RP l]] →Qxl".
    iApply (lend_tok_split (M:=M) (sm:=⟦⟧) with "l [RP →Qxl]").
    iIntros "R". rewrite der_borrow_jto. iMod ("RP" with "R"). by iApply "→Qxl".
  Qed.

  (** Retrive from [lendd] *)
  Lemma lendd_retrieve {α Px} :
    [†α] -∗ lendd α Px -∗ modw M (borrow_wsatid M) ⟦ Px ⟧.
  Proof.
    rewrite lend_unseal. iIntros "† [%Qx[QP l]]". rewrite der_borrow_jto.
    iMod (lend_tok_retrieve (M:=M) (sm:=⟦⟧) with "† l") as "Qx".
    iMod ("QP" with "Qx") as "$". by iIntros.
  Qed.

  (** Open a borrower *)
  Lemma bord_open {α q Px} :
    q.[α] -∗ bord α Px -∗ modw M (borrow_wsatid M) (obord α q Px ∗ ⟦ Px ⟧).
  Proof.
    rewrite bor_unseal obor_unseal. iIntros "α [%Qx[$[QP c]]]".
    iMod (bor_tok_open (M:=M) (sm:=⟦⟧) with "α c") as "[$ Qx]".
    rewrite der_borrow_jto. iMod ("QP" with "Qx") as "$". by iIntros.
  Qed.

  (** Lemma for [obord_merge_subdiv] *)
  Local Lemma obord_list {αqPl β} :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ obord α q Px) ⊢
    ∃ αqRl,
      ⌜([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ⊣⊢
        [∗ list] '(α, q, _)' ∈ αqRl, q.[α]⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ obor_tok α q R) ∗
      (([∗ list] '(_, _, Px)' ∈ αqPl, ⟦ Px ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    rewrite obor_unseal /=. elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q Px]] αqPl ->) "[[⊑[%R[PR o]]][%αqRl[%[ol →']]]]".
    iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol".
    iSplit; [iPureIntro; by f_equiv|]. iIntros "[Px Pxl]".
    rewrite der_borrow_jto. iMod ("PR" with "Px") as "$".
    iApply ("→'" with "Pxl").
  Qed.
  (** Merge and subdivide open borrowers *)
  Lemma obord_merge_subdiv αqPl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ obord α q Px) -∗
    ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M
      ([∗ list] '(_, _, Px)' ∈ αqPl, ⟦ Px ⟧)) =[borrow_wsatid M]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Qx ∈ Qxl, bord β Qx).
  Proof.
    rewrite obord_list /=. iIntros "[%[->[ol →]]] Qxl →Pl".
    setoid_rewrite <-bor_tok_bor.
    iApply (obor_tok_merge_subdiv (M:=M) with "ol Qxl [→ →Pl]").
    iIntros "† Qxl". iMod ("→Pl" with "† Qxl") as "Pxl".
    iMod ("→" with "Pxl") as "$". by iIntros.
  Qed.
  (** Subdivide open borrowers *)
  Lemma obord_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ obord α q Px -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M ⟦ Px ⟧) =[borrow_wsatid M]=∗
      q.[α] ∗ ([∗ list] Qx ∈ Qxl, bord β Qx).
  Proof.
    iIntros "⊑ o Qxl →P".
    iMod (obord_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→P]")
      as "[[$ _]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obord_close {α q Px} :
    obord α q Px -∗ ⟦ Px ⟧ =[borrow_wsatid M]=∗ q.[α] ∗ bord α Px.
  Proof.
    iIntros "o Px".
    iMod (obord_subdiv [Px] with "[] o [Px] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Turn [obord] to [obor_tok] *)
  Lemma obord_obor_tok {α q Px} :
    obord α q Px -∗ ⟦ Px ⟧ -∗ modw M (borrow_wsatid M)
      (obor_tok α q Px ∗ ⟦ Px ⟧).
  Proof.
    rewrite obor_unseal. iIntros "[%[PQ o]] Px".
    iMod (obor_tok_subdiv (M:=M) (sm:=⟦⟧) [_] with "[] o [$Px //] [PQ]")
      as "[α[c _]]".
    { iApply lft_sincl_refl. }
    { rewrite der_borrow_jto /=. iIntros "_ [Px _]". by iMod ("PQ" with "Px"). }
    iApply (bor_tok_open (M:=M) (sm:=⟦⟧) with "α c").
  Qed.

  (** Reborrow a borrower *)
  Lemma obord_reborrow {α q Px} β :
    obord α q Px -∗ ⟦ Px ⟧ -∗ modw M (borrow_wsatid M)
      (q.[α] ∗ bord (α ⊓ β) Px ∗ ([†β] -∗ bord α Px)).
  Proof.
    iIntros "o Px". iMod (obord_obor_tok with "o Px") as "[o Px]".
    rewrite -bor_tok_bor -bor_tok_bor.
    iMod (obor_tok_reborrow (M:=M) (sm:=⟦⟧) with "o Px") as "$". by iIntros "$".
  Qed.
  Lemma bord_reborrow {α q Px} β :
    q.[α] -∗ bord α Px -∗ modw M (borrow_wsatid M)
      (q.[α] ∗ bord (α ⊓ β) Px ∗ ([†β] -∗ bord α Px)).
  Proof.
    iIntros "α b". iMod (bord_open with "α b") as "[o Px]".
    by iMod (obord_reborrow with "o Px").
  Qed.
End borrow_deriv.
