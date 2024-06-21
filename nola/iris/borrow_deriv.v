(** * Borrowing machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.bi Require Import list.
From nola.iris Require Export borrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation PintpNotation IntpNotation UpdwNotation
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

  (** [borc]: Relaxed closed borrower *)
  Local Definition borc_def δ α P : iProp Σ :=
    ∃ Q, δ (borrow_jto P Q) ∗ δ (borrow_jto Q P) ∗ borc_tok α Q.
  Local Lemma borc_aux : seal borc_def. Proof. by eexists. Qed.
  Definition borc := borc_aux.(unseal).
  Local Lemma borc_unseal : borc = borc_def. Proof. exact: seal_eq. Qed.
  (** [bor]: Relaxed borrower *)
  Local Definition bor_def δ α P : iProp Σ :=
    ∃ Q, δ (borrow_jto P Q) ∗ δ (borrow_jto Q P) ∗ bor_tok α Q.
  Local Lemma bor_aux : seal bor_def. Proof. by eexists. Qed.
  Definition bor := bor_aux.(unseal).
  Local Lemma bor_unseal : bor = bor_def. Proof. exact: seal_eq. Qed.
  (** [obor]: Relaxed open borrower *)
  Local Definition obor_def δ α q P : iProp Σ :=
    ∃ Q, δ (borrow_jto P Q) ∗ obor_tok α q Q.
  Local Lemma obor_aux : seal obor_def. Proof. by eexists. Qed.
  Definition obor := obor_aux.(unseal).
  Local Lemma obor_unseal : obor = obor_def. Proof. exact: seal_eq. Qed.
  (** [lend]: Relaxed lender *)
  Local Definition lend_def δ α P : iProp Σ :=
    ∃ Q, δ (borrow_jto Q P) ∗ lend_tok α Q.
  Local Lemma lend_aux : seal lend_def. Proof. by eexists. Qed.
  Definition lend := lend_aux.(unseal).
  Local Lemma lend_unseal : lend = lend_def. Proof. exact: seal_eq. Qed.

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance borc_ne `{!NonExpansive δ} {α} : NonExpansive (borc δ α).
  Proof. rewrite borc_unseal. solve_proper. Qed.
  #[export] Instance bor_ne `{!NonExpansive δ} {α} : NonExpansive (bor δ α).
  Proof. rewrite bor_unseal. solve_proper. Qed.
  #[export] Instance obor_ne `{!NonExpansive δ} {α q} :
    NonExpansive (obor δ α q).
  Proof. rewrite obor_unseal. solve_proper. Qed.
  #[export] Instance lend_ne `{!NonExpansive δ} {α} : NonExpansive (lend δ α).
  Proof. rewrite lend_unseal. solve_proper. Qed.
End borrow_deriv.
Notation borcd := (borc der). Notation bord := (bor der).
Notation obord := (obor der). Notation lendd := (lend der).

Section borrow_deriv.
  Context `{!BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dintp JUDGI (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (P Q : FML $oi Σ).

  (** Derivability data for [borrow] *)
  Class BorrowDeriv :=
    (** Interpreting [borrow_jto] *)
    borrow_jto_intp : ∀{δ P Q},
      ⟦ borrow_jto P Q ⟧(δ) ⊣⊢ (⟦ P ⟧(δ) ==∗ ⟦ Q ⟧(δ)).
End borrow_deriv.
Arguments BorrowDeriv FML Σ JUDGI {_ _}.
Hint Mode BorrowDeriv ! - - - - : typeclass_instances.

Section borrow_deriv.
  Context `{!borrowGS FML Σ,
  !BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dintp JUDGI (FML $oi Σ) (iProp Σ), !BorrowDeriv FML Σ JUDGI,
  !Deriv (JUDGI:=JUDGI) ih δ}.
  Implicit Type (P Q : FML $oi Σ) (δ : JUDGI → iProp Σ).

  (** Lemmas for [borrow_jto] *)
  Lemma borrow_jto_refl {P} : ⊢ δ (borrow_jto P P).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite borrow_jto_intp.
    by iIntros "$".
  Qed.
  Lemma borrow_jto_trans {P Q R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    δ (borrow_jto Q R) -∗ δ (borrow_jto P R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !borrow_jto_intp.
    iIntros "QR P". iMod ("big" with "[//] [//] [//] P"). by iApply "QR".
  Qed.
  Lemma borrow_jto_trans' {P Q R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ R ⟧(δ')) -∗
    δ (borrow_jto P Q) -∗ δ (borrow_jto P R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !borrow_jto_intp.
    iIntros "PQ P". iMod ("PQ" with "P"). by iApply "big".
  Qed.
  Lemma der_borrow_jto {P Q} :
    der (borrow_jto P Q) ⊢ (⟦ P ⟧ ==∗ ⟦ Q ⟧).
  Proof. by rewrite der_sound borrow_jto_intp. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma borc_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    borc δ α P -∗ borc δ α Q.
  Proof.
    rewrite borc_unseal. iIntros "PQ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (borrow_jto_trans with "QP PR")|
      iApply (borrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma bor_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    bor δ α P -∗ bor δ α Q.
  Proof.
    rewrite bor_unseal. iIntros "PQ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (borrow_jto_trans with "QP PR")|
      iApply (borrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma obor_to {α q P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    obor δ α q P -∗ obor δ α q Q.
  Proof.
    rewrite obor_unseal. iIntros "QP [%R[PR $]]".
    iApply (borrow_jto_trans with "QP PR").
  Qed.
  Lemma lend_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    lend δ α P -∗ lend δ α Q.
  Proof.
    rewrite lend_unseal. iIntros "PQ [%R[RP $]]".
    iApply (borrow_jto_trans' with "PQ RP").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma borc_lft {α β P} : β ⊑□ α -∗ borc δ α P -∗ borc δ β P.
  Proof.
    rewrite borc_unseal. iIntros "⊑ [%[?[? c]]]".
    iDestruct (borc_tok_lft with "⊑ c") as "$". iFrame.
  Qed.
  Lemma bor_lft {α β P} : β ⊑□ α -∗ bor δ α P -∗ bor δ β P.
  Proof.
    rewrite bor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (bor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma obor_lft {α β q r P} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ obor δ α q P -∗ obor δ β r P.
  Proof.
    rewrite obor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (obor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma lend_lft {α β P} : α ⊑□ β -∗ lend δ α P -∗ lend δ β P.
  Proof.
    rewrite lend_unseal. iIntros "⊑ [%[? l]]".
    by iDestruct (lend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma borc_tok_borc {α P} : borc_tok α P ⊢ borc δ α P.
  Proof. rewrite borc_unseal. iIntros "$". iSplitL; iApply borrow_jto_refl. Qed.
  Lemma bor_tok_bor {α P} : bor_tok α P ⊢ bor δ α P.
  Proof. rewrite bor_unseal. iIntros "$". iSplitL; iApply borrow_jto_refl. Qed.
  Lemma obor_tok_obor {α q P} : obor_tok α q P ⊢ obor δ α q P.
  Proof. rewrite obor_unseal. iIntros "$". iApply borrow_jto_refl. Qed.
  Lemma lend_tok_lend {α P} : lend_tok α P ⊢ lend δ α P.
  Proof. rewrite lend_unseal. iIntros "$". iApply borrow_jto_refl. Qed.

  (** Other conversions *)
  Lemma borc_bor {α P} : borc δ α P ⊢ bor δ α P.
  Proof.
    rewrite borc_unseal bor_unseal. iIntros "[%[$[$?]]]".
    by rewrite borc_tok_bor_tok.
  Qed.
  Lemma borc_fake {α} P : [†α] ⊢ borc δ α P.
  Proof. by rewrite borc_tok_fake borc_tok_borc. Qed.
  Lemma bor_fake {α} P : [†α] ⊢ bor δ α P.
  Proof. by rewrite borc_fake borc_bor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.

  (** Create borrowers and lenders *)
  Lemma borc_lend_new_list α Pl Ql :
    ([∗ list] P ∈ Pl, ⟦ P ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ⟦ P ⟧(δ)) -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧(δ)))
      =[borrow_wsati M δ]=∗
      ([∗ list] P ∈ Pl, borc δ α P) ∗ [∗ list] Q ∈ Ql, lend δ α Q.
  Proof.
    setoid_rewrite <-borc_tok_borc. setoid_rewrite <-lend_tok_lend.
    exact: borc_lend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma borc_lend_new α P :
    ⟦ P ⟧(δ) =[borrow_wsati M δ]=∗ borc δ α P ∗ lend δ α P.
  Proof. rewrite -borc_tok_borc -lend_tok_lend. exact: borc_lend_tok_new. Qed.
End borrow_deriv.

Section borrow_deriv.
  Context `{!borrowGS FML Σ,
  !BorrowPreDeriv (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dintp JUDGI (FML $oi Σ) (iProp Σ), !BorrowDeriv FML Σ JUDGI,
  !GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.
  Implicit Type (P Q : FML $oi Σ).

  (** Split a lender *)
  Lemma lendd_split {α P} Ql :
    lendd α P -∗ (⟦ P ⟧ -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧)) =[borrow_wsatid M]=∗
      [∗ list] Q ∈ Ql, lendd α Q.
  Proof.
    rewrite {1}lend_unseal. setoid_rewrite <-lend_tok_lend.
    iIntros "[%R[RP l]] →Ql".
    iApply (lend_tok_split (M:=M) (ip:=⟦⟧) with "l [RP →Ql]").
    iIntros "R". rewrite der_borrow_jto. iMod ("RP" with "R"). by iApply "→Ql".
  Qed.

  (** Retrive from [lendd] *)
  Lemma lendd_retrieve {α P} :
    [†α] -∗ lendd α P -∗ modw M (borrow_wsatid M) ⟦ P ⟧.
  Proof.
    rewrite lend_unseal. iIntros "† [%Q[QP l]]". rewrite der_borrow_jto.
    iMod (lend_tok_retrieve (M:=M) (ip:=⟦⟧) with "† l") as "Q".
    iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Open a closed borrower *)
  Lemma borcd_open {α q P} :
    q.[α] -∗ borcd α P =[borrow_wsatid M]=∗ obord α q P ∗ ⟦ P ⟧.
  Proof.
    rewrite borc_unseal obor_unseal. iIntros "α [%Q[$[QP c]]]".
    iMod (borc_tok_open (ip:=⟦⟧) with "α c") as "[$ Q]".
    rewrite der_borrow_jto. by iMod ("QP" with "Q").
  Qed.
  (** Open a borrower *)
  Lemma bord_open {α q P} :
    q.[α] -∗ bord α P -∗ modw M (borrow_wsatid M) (obord α q P ∗ ⟦ P ⟧).
  Proof.
    rewrite bor_unseal obor_unseal. iIntros "α [%Q[$[QP c]]]".
    iMod (bor_tok_open (M:=M) (ip:=⟦⟧) with "α c") as "[$ Q]".
    rewrite der_borrow_jto. iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Lemma for [obord_merge_subdiv] *)
  Local Lemma obord_list {αqPl β} :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) ⊢
    ∃ αqRl,
      ⌜([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ⊣⊢
        [∗ list] '(α, q, _)' ∈ αqRl, q.[α]⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ obor_tok α q R) ∗
      (([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    rewrite obor_unseal /=. elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q P]] αqPl ->) "[[⊑[%R[PR o]]][%αqRl[%[ol →']]]]".
    iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol".
    iSplit; [iPureIntro; by f_equiv|]. iIntros "[P Pl]".
    rewrite der_borrow_jto. iMod ("PR" with "P") as "$".
    iApply ("→'" with "Pl").
  Qed.
  (** Merge and subdivide open borrowers *)
  Lemma obord_merge_subdiv αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ obord α q P) -∗
    ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M
      ([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧)) =[borrow_wsatid M]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    rewrite obord_list /=. iIntros "[%[->[ol →]]] Ql →Pl".
    setoid_rewrite <-borc_tok_borc.
    iApply (obor_tok_merge_subdiv (M:=M) with "ol Ql [→ →Pl]"). iIntros "† Ql".
    iMod ("→Pl" with "† Ql") as "Pl". iMod ("→" with "Pl") as "$". by iIntros.
  Qed.
  (** Subdivide open borrowers *)
  Lemma obord_subdiv {α q P} Ql β :
    β ⊑□ α -∗ obord α q P -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M ⟦ P ⟧) =[borrow_wsatid M]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, borcd β Q).
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (obord_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]") as "[[$ _]$]"=>/=;
      by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma obord_close {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatid M]=∗ q.[α] ∗ borcd α P.
  Proof.
    iIntros "o P".
    iMod (obord_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Turn [obord] to [obor_tok] *)
  Lemma obord_obor_tok {α q P} :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatid M]=∗ obor_tok α q P ∗ ⟦ P ⟧.
  Proof.
    rewrite obor_unseal. iIntros "[%[PQ o]] P".
    iMod (obor_tok_subdiv (M:=M) (ip:=⟦⟧) [_] with "[] o [$P //] [PQ]")
      as "[α[c _]]".
    { iApply lft_sincl_refl. }
    { rewrite der_borrow_jto /=. iIntros "_ [P _]". by iMod ("PQ" with "P"). }
    iApply (borc_tok_open (ip:=⟦⟧) with "α c").
  Qed.

  (** Reborrow a borrower *)
  Lemma obord_reborrow {α q P} β :
    obord α q P -∗ ⟦ P ⟧ =[borrow_wsatid M]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "o P". iMod (obord_obor_tok with "o P") as "[o P]".
    rewrite -borc_tok_borc -bor_tok_bor.
    iApply (obor_tok_reborrow (M:=M) (ip:=⟦⟧) with "o P").
  Qed.
  Lemma borcd_reborrow {α q P} β :
    q.[α] -∗ borcd α P =[borrow_wsatid M]=∗
      q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P).
  Proof.
    iIntros "α c". iMod (borcd_open with "α c") as "[o P]".
    by iMod (obord_reborrow with "o P").
  Qed.
  Lemma bord_reborrow {α q P} β :
    q.[α] -∗ bord α P -∗ modw M (borrow_wsatid M)
      (q.[α] ∗ borcd (α ⊓ β) P ∗ ([†β] -∗ bord α P)).
  Proof.
    iIntros "α b". iMod (bord_open with "α b") as "[o P]".
    by iMod (obord_reborrow with "o P").
  Qed.
End borrow_deriv.
