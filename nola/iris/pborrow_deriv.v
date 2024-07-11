(** * Prophetic borrowing machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.iris Require Export pborrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation iPropAppNotation PsemNotation SemNotation
  UpdwNotation LftNotation ProphNotation.

Implicit Type (TY : synty).

(** ** Preliminaries *)

(** Notation *)
Notation pborrow_wsati M δ := (pborrow_wsat M ⟦⟧(δ)).
Notation pborrow_wsatid M := (pborrow_wsati M der).
Notation plend_bodyi δ := (plend_body ⟦⟧(δ)).
Notation plend_bodyid := (plend_bodyi der).
Notation plend_body_vari δ := (plend_body_var ⟦⟧(δ)).
Notation plend_body_varid := (plend_body_vari der).

(** Derivability pre-data for [pborrow] *)
Class PborrowPreDeriv TY (FM JUDG : ofe) := PBORROW_PRE_DERIV {
  (** Basic conversion judgment *)
  pborrow_jto : FM → FM → JUDG;
  (** Conversion judgment for [lend_body] *)
  pborrow_jlto {X Y : TY} : clair TY X → clair TY Y →
    (X -d> FM) → (Y -d> FM) → JUDG;
  (** [pborrow_jto] is non-expansive *)
  pborrow_jto_ne :: NonExpansive2 pborrow_jto;
  (** [pborrow_jto] is non-expansive *)
  pborrow_jlto_ne {X Y xπ yπ} :: NonExpansive2 (@pborrow_jlto X Y xπ yπ);
}.
Hint Mode PborrowPreDeriv - ! - : typeclass_instances.
Arguments PBORROW_PRE_DERIV {_ _ _} _ _ {_ _}.

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ, !PborrowPreDeriv TY (FML $oi Σ) JUDG}.
  Implicit Type (δ : JUDG → iProp Σ) (X Y : TY).

  (** [nborc]: Relaxed non-prophetic closed borrower *)
  Local Definition nborc_def δ α Px : iProp Σ :=
    ∃ Qx, δ (pborrow_jto Px Qx) ∗ δ (pborrow_jto Qx Px) ∗ nborc_tok α Qx.
  Local Lemma nborc_aux : seal nborc_def. Proof. by eexists. Qed.
  Definition nborc := nborc_aux.(unseal).
  Local Lemma nborc_unseal : nborc = nborc_def. Proof. exact: seal_eq. Qed.
  (** [nbor]: Relaxed non-prophetic borrower *)
  Local Definition nbor_def δ α Px : iProp Σ :=
    ∃ Qx, δ (pborrow_jto Px Qx) ∗ δ (pborrow_jto Qx Px) ∗ nbor_tok α Qx.
  Local Lemma nbor_aux : seal nbor_def. Proof. by eexists. Qed.
  Definition nbor := nbor_aux.(unseal).
  Local Lemma nbor_unseal : nbor = nbor_def. Proof. exact: seal_eq. Qed.
  (** [nobor]: Relaxed non-prophetic open borrower *)
  Local Definition nobor_def δ α q Px : iProp Σ :=
    ∃ Qx, δ (pborrow_jto Px Qx) ∗ nobor_tok α q Qx.
  Local Lemma nobor_aux : seal nobor_def. Proof. by eexists. Qed.
  Definition nobor := nobor_aux.(unseal).
  Local Lemma nobor_unseal : nobor = nobor_def. Proof. exact: seal_eq. Qed.
  (** [nlend]: Relaxed non-prophetic lender *)
  Local Definition nlend_def δ α Px : iProp Σ :=
    ∃ Qx, δ (pborrow_jto Qx Px) ∗ nlend_tok α Qx.
  Local Lemma nlend_aux : seal nlend_def. Proof. by eexists. Qed.
  Definition nlend := nlend_aux.(unseal).
  Local Lemma nlend_unseal : nlend = nlend_def. Proof. exact: seal_eq. Qed.

  (** [pborc]: Relaxed prophetic closed borrower *)
  Local Definition pborc_def {X} δ α x ξ (Φx : X -d> _) : iProp Σ :=
    ∃ Ψx, (∀ x, δ (pborrow_jto (Φx x) (Ψx x))) ∗
      (∀ x, δ (pborrow_jto (Ψx x) (Φx x))) ∗ pborc_tok α x ξ Ψx.
  Local Lemma pborc_aux : seal (@pborc_def). Proof. by eexists. Qed.
  Definition pborc {X} := pborc_aux.(unseal) X.
  Local Lemma pborc_unseal : @pborc = @pborc_def. Proof. exact: seal_eq. Qed.
  (** [pbor]: Relaxed prophetic borrower *)
  Local Definition pbor_def {X} δ α x ξ (Φx : X -d> _) : iProp Σ :=
    ∃ Ψx, (∀ x, δ (pborrow_jto (Φx x) (Ψx x))) ∗
      (∀ x, δ (pborrow_jto (Ψx x) (Φx x))) ∗ pbor_tok α x ξ Ψx.
  Local Lemma pbor_aux : seal (@pbor_def). Proof. by eexists. Qed.
  Definition pbor {X} := pbor_aux.(unseal) X.
  Local Lemma pbor_unseal : @pbor = @pbor_def. Proof. exact: seal_eq. Qed.
  (** [pobor]: Relaxed prophetic open borrower *)
  Local Definition pobor_def {X} δ α q ξ (Φx : X -d> _) : iProp Σ :=
    ∃ Ψx, (∀ x, δ (pborrow_jto (Φx x) (Ψx x))) ∗ pobor_tok α q ξ Ψx.
  Local Lemma pobor_aux : seal (@pobor_def). Proof. by eexists. Qed.
  Definition pobor {X} := pobor_aux.(unseal) X.
  Local Lemma pobor_unseal : @pobor = @pobor_def. Proof. exact: seal_eq. Qed.
  (** [plend]: Relaxed prophetic lender *)
  Local Definition plend_def {X} δ α xπ (Φx : X -d> _) : iProp Σ :=
    ∃ Y yπ Ψx, δ (pborrow_jlto yπ xπ Ψx Φx) ∗ plend_tok (X:=Y) α yπ Ψx.
  Local Lemma plend_aux : seal (@plend_def). Proof. by eexists. Qed.
  Definition plend {X} := plend_aux.(unseal) X.
  Local Lemma plend_unseal : @plend = @plend_def. Proof. exact: seal_eq. Qed.

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance nborc_ne `{!NonExpansive δ} {α} : NonExpansive (nborc δ α).
  Proof. rewrite nborc_unseal. solve_proper. Qed.
  #[export] Instance nbor_ne `{!NonExpansive δ} {α} : NonExpansive (nbor δ α).
  Proof. rewrite nbor_unseal. solve_proper. Qed.
  #[export] Instance nobor_ne `{!NonExpansive δ} {α q} :
    NonExpansive (nobor δ α q).
  Proof. rewrite nobor_unseal. solve_proper. Qed.
  #[export] Instance nlend_ne `{!NonExpansive δ} {α} : NonExpansive (nlend δ α).
  Proof. rewrite nlend_unseal. solve_proper. Qed.
  #[export] Instance pborc_ne `{!NonExpansive δ} {X α x ξ} :
    NonExpansive (pborc (X:=X) δ α x ξ).
  Proof. rewrite pborc_unseal. solve_proper. Qed.
  #[export] Instance pbor_ne `{!NonExpansive δ} {X α x ξ} :
    NonExpansive (pbor (X:=X) δ α x ξ).
  Proof. rewrite pbor_unseal. solve_proper. Qed.
  #[export] Instance pobor_ne `{!NonExpansive δ} {X α q ξ} :
    NonExpansive (pobor (X:=X) δ α q ξ).
  Proof. rewrite pobor_unseal. solve_proper. Qed.
  #[export] Instance plend_ne `{!NonExpansive δ} {X α xπ} :
    NonExpansive (plend (X:=X) δ α xπ).
  Proof. rewrite plend_unseal. solve_proper. Qed.
End pborrow_deriv.
Notation nborcd := (nborc der). Notation nbord := (nbor der).
Notation nobord := (nobor der). Notation nlendd := (nlend der).
Notation pborcd := (pborc der). Notation pbord := (pbor der).
Notation pobord := (pobor der). Notation plendd := (plend der).

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ,
    !PborrowPreDeriv TY (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dsem JUDGI (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (Px Qx : FML $oi Σ).

  (** Derivability data for [pborrow] *)
  Class PborrowDeriv := PBORROW_DERIV {
    (** Interpreting [pborrow_jto] *)
    pborrow_jto_sem : ∀{δ Px Qx},
      ⟦ pborrow_jto Px Qx ⟧(δ) ⊣⊢ (⟦ Px ⟧(δ) ==∗ ⟦ Qx ⟧(δ));
    (** Interpreting [pborrow_jlto] *)
    pborrow_jlto_sem : ∀{δ X Y xπ yπ} {Φx Ψx : _ -d> FML $oi Σ},
      ⟦ pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx ⟧(δ) ⊣⊢
        (plend_body ⟦ ⟧(δ) xπ Φx ==∗ plend_body ⟦ ⟧(δ) yπ Ψx);
  }.
End pborrow_deriv.
Arguments PborrowDeriv TY FML Σ {_} JUDGI {_ _}.
Hint Mode PborrowDeriv - ! - - - - - : typeclass_instances.

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ,
  !PborrowPreDeriv TY (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dsem JUDGI (FML $oi Σ) (iProp Σ), !PborrowDeriv TY FML Σ JUDGI,
  !Deriv (JUDGI:=JUDGI) ih δ}.
  Implicit Type (X Y Z : TY) (Px Qx R : FML $oi Σ) (δ : JUDGI → iProp Σ).

  (** ** Conversion *)

  (** Lemmas for [pborrow_jto] *)
  Lemma pborrow_jto_refl {Px} : ⊢ δ (pborrow_jto Px Px).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite pborrow_jto_sem.
    by iIntros "$".
  Qed.
  Lemma pborrow_jto_trans {Px Qx R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    δ (pborrow_jto Qx R) -∗ δ (pborrow_jto Px R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !pborrow_jto_sem.
    iIntros "QR Px". iMod ("big" with "[//] [//] [//] Px"). by iApply "QR".
  Qed.
  Lemma pborrow_jto_trans' {Px Qx R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Qx ⟧(δ') ==∗ ⟦ R ⟧(δ')) -∗
    δ (pborrow_jto Px Qx) -∗ δ (pborrow_jto Px R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !pborrow_jto_sem.
    iIntros "ΦΨ Px". iMod ("ΦΨ" with "Px"). by iApply "big".
  Qed.
  Lemma der_pborrow_jto {Px Qx} :
    der (pborrow_jto Px Qx) ⊢ (⟦ Px ⟧ ==∗ ⟦ Qx ⟧).
  Proof. by rewrite der_sound pborrow_jto_sem. Qed.

  (** Lemmas for [pborrow_jlto] *)
  Lemma pborrow_jlto_refl {X xπ Φx} :
    ⊢ δ (pborrow_jlto (FM:=FML $oi Σ) (X:=X) xπ xπ Φx Φx).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite pborrow_jlto_sem.
    by iIntros "$".
  Qed.
  Lemma pborrow_jlto_trans {X Y Z xπ yπ zπ Φx Ψx Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φx ==∗ plend_body ⟦ ⟧(δ') yπ Ψx) -∗
    δ (pborrow_jlto (X:=Y) (Y:=Z) yπ zπ Ψx Ω) -∗
    δ (pborrow_jlto (X:=X) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !pborrow_jlto_sem. iIntros "ΨΩ Φx".
    iMod ("big" with "[//] [//] [//] Φx"). by iApply "ΨΩ".
  Qed.
  Lemma pborrow_jlto_trans' {X Y Z xπ yπ zπ Φx Ψx Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') yπ Ψx ==∗ plend_body ⟦ ⟧(δ') zπ Ω) -∗
    δ (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) -∗
    δ (pborrow_jlto (Y:=Z) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !pborrow_jlto_sem. iIntros "ΦΨ Φx". iMod ("ΦΨ" with "Φx").
    by iApply "big".
  Qed.
  Lemma der_pborrow_jlto {X Y xπ yπ Φx Ψx} :
    der (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) ⊢
      (plend_bodyid xπ Φx ==∗ plend_bodyid yπ Ψx).
  Proof. by rewrite der_sound pborrow_jlto_sem. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma nborc_to {α Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    nborc δ α Px -∗ nborc δ α Qx.
  Proof.
    rewrite nborc_unseal. iIntros "ΦΨ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "ΦΨ RP")].
  Qed.
  Lemma nbor_to {α Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    nbor δ α Px -∗ nbor δ α Qx.
  Proof.
    rewrite nbor_unseal. iIntros "ΦΨ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "ΦΨ RP")].
  Qed.
  Lemma nobor_to {α q Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    nobor δ α q Px -∗ nobor δ α q Qx.
  Proof.
    rewrite nobor_unseal. iIntros "QP [%R[PR $]]".
    iApply (pborrow_jto_trans with "QP PR").
  Qed.
  Lemma nlend_to {α Px Qx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    nlend δ α Px -∗ nlend δ α Qx.
  Proof.
    rewrite nlend_unseal. iIntros "ΦΨ [%R[RP $]]".
    iApply (pborrow_jto_trans' with "ΦΨ RP").
  Qed.
  Lemma pborc_to {X α x ξ Φx Ψx} :
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx x' ⟧(δ') ==∗ ⟦ Ψx x' ⟧(δ')) -∗
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx x' ⟧(δ') ==∗ ⟦ Φx x' ⟧(δ')) -∗
    pborc (X:=X) δ α x ξ Φx -∗ pborc δ α x ξ Ψx.
  Proof.
    rewrite pborc_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ $]]]".
    iSplitL "ΨΦ ΦΩ"; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma pbor_to {X α x ξ Φx Ψx} :
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx x' ⟧(δ') ==∗ ⟦ Ψx x' ⟧(δ')) -∗
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx x' ⟧(δ') ==∗ ⟦ Φx x' ⟧(δ')) -∗
    pbor (X:=X) δ α x ξ Φx -∗ pbor δ α x ξ Ψx.
  Proof.
    rewrite pbor_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ $]]]".
    iSplitL "ΨΦ ΦΩ"; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma pobor_to {X α q ξ Φx Ψx} :
    (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx x ⟧(δ') ==∗ ⟦ Ψx x ⟧(δ')) -∗
    (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx x ⟧(δ') ==∗ ⟦ Φx x ⟧(δ')) -∗
    pobor (X:=X) δ α q ξ Φx -∗ pobor δ α q ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ $]]" (?).
    iApply (pborrow_jto_trans with "ΨΦ ΦΩ").
  Qed.
  Lemma plend_to {X Y α xπ yπ Φx Ψx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φx ==∗ plend_body ⟦ ⟧(δ') yπ Ψx) -∗
    plend (X:=X) δ α xπ Φx -∗ plend (X:=Y) δ α yπ Ψx.
  Proof.
    rewrite plend_unseal. iIntros "ΦΨ (%Z & %zπ & %Ω & ΩΦ & $)".
    iApply (pborrow_jlto_trans' with "ΦΨ ΩΦ").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma nborc_lft {α β Px} : β ⊑□ α -∗ nborc δ α Px -∗ nborc δ β Px.
  Proof.
    rewrite nborc_unseal. iIntros "⊑ [%[?[? c]]]".
    iDestruct (nborc_tok_lft with "⊑ c") as "$". iFrame.
  Qed.
  Lemma nbor_lft {α β Px} : β ⊑□ α -∗ nbor δ α Px -∗ nbor δ β Px.
  Proof.
    rewrite nbor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (nbor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma nobor_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ nobor δ α q Px -∗ nobor δ β r Px.
  Proof.
    rewrite nobor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (nobor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma nlend_lft {α β Px} : α ⊑□ β -∗ nlend δ α Px -∗ nlend δ β Px.
  Proof.
    rewrite nlend_unseal. iIntros "⊑ [%[? l]]".
    by iDestruct (nlend_tok_lft with "⊑ l") as "$".
  Qed.
  Lemma pborc_lft {X α β x ξ Φx} :
    β ⊑□ α -∗ pborc (X:=X) δ α x ξ Φx -∗ pborc δ β x ξ Φx.
  Proof.
    rewrite pborc_unseal. iIntros "⊑ [%[?[? c]]]".
    iDestruct (pborc_tok_lft with "⊑ c") as "$". iFrame.
  Qed.
  Lemma pbor_lft {X α β x ξ Φx} :
    β ⊑□ α -∗ pbor (X:=X) δ α x ξ Φx -∗ pbor δ β x ξ Φx.
  Proof.
    rewrite pbor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (pbor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma pobor_lft {X α β q r ξ Φx} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ pobor (X:=X) δ α q ξ Φx -∗ pobor δ β r ξ Φx.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (pobor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma plend_lft {X α β xπ Φx} :
    α ⊑□ β -∗ plend (X:=X) δ α xπ Φx -∗ plend δ β xπ Φx.
  Proof.
    rewrite plend_unseal. iIntros "⊑ (% & % & % & ? & l)".
    by iDestruct (plend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma nborc_tok_nborc {α Px} : nborc_tok α Px ⊢ nborc δ α Px.
  Proof.
    rewrite nborc_unseal. iIntros "$". iSplitL; iApply pborrow_jto_refl.
  Qed.
  Lemma nbor_tok_nbor {α Px} : nbor_tok α Px ⊢ nbor δ α Px.
  Proof.
    rewrite nbor_unseal. iIntros "$". iSplitL; iApply pborrow_jto_refl.
  Qed.
  Lemma nobor_tok_nobor {α q Px} : nobor_tok α q Px ⊢ nobor δ α q Px.
  Proof. rewrite nobor_unseal. iIntros "$". iApply pborrow_jto_refl. Qed.
  Lemma nlend_tok_nlend {α Px} : nlend_tok α Px ⊢ nlend δ α Px.
  Proof. rewrite nlend_unseal. iIntros "$". iApply pborrow_jto_refl. Qed.
  Lemma pborc_tok_pborc {X α x ξ Φx} :
    pborc_tok (X:=X) α x ξ Φx ⊢ pborc δ α x ξ Φx.
  Proof.
    rewrite pborc_unseal. iIntros "$".
    iSplitL; iIntros; iApply pborrow_jto_refl.
  Qed.
  Lemma pbor_tok_pbor {X α x ξ Φx} :
    pbor_tok (X:=X) α x ξ Φx ⊢ pbor δ α x ξ Φx.
  Proof.
    rewrite pbor_unseal. iIntros "$".
    iSplitL; iIntros; iApply pborrow_jto_refl.
  Qed.
  Lemma pobor_tok_pobor {X α q ξ Φx} :
    pobor_tok (X:=X) α q ξ Φx ⊢ pobor δ α q ξ Φx.
  Proof. rewrite pobor_unseal. iIntros "$" (?). iApply pborrow_jto_refl. Qed.
  Lemma plend_tok_plend {X α xπ Φx} :
    plend_tok (X:=X) α xπ Φx ⊢ plend δ α xπ Φx.
  Proof. rewrite plend_unseal. iIntros "$". iApply pborrow_jlto_refl. Qed.

  (** Other types of conversion *)
  Lemma nborc_nbor {α Px} : nborc δ α Px ⊢ nbor δ α Px.
  Proof.
    rewrite nborc_unseal nbor_unseal. iIntros "[%[$[$?]]]".
    by rewrite nborc_tok_nbor_tok.
  Qed.
  Lemma nborc_fake {α} Px : [†α] ⊢ nborc δ α Px.
  Proof. by rewrite nborc_tok_fake nborc_tok_nborc. Qed.
  Lemma nbor_fake {α} Px : [†α] ⊢ nbor δ α Px.
  Proof. by rewrite nborc_fake nborc_nbor. Qed.
  Lemma pborc_pbor {X α x ξ Φx} : pborc (X:=X) δ α x ξ Φx ⊢ pbor δ α x ξ Φx.
  Proof.
    rewrite pborc_unseal pbor_unseal. iIntros "[%[$[$?]]]".
    by rewrite pborc_tok_pbor_tok.
  Qed.
  Lemma pborc_fake {X α} x ξ Φx : [†α] ⊢ pborc (X:=X) δ α x ξ Φx.
  Proof. by rewrite pborc_tok_fake pborc_tok_pborc. Qed.
  Lemma pbor_fake {X α} x ξ Φx : [†α] ⊢ pbor (X:=X) δ α x ξ Φx.
  Proof. by rewrite pborc_fake pborc_pbor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.

  (** ** Rules that work under [Deriv ih δ] *)

  (** Create borrowers and lenders *)
  Lemma nborc_nlend_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧(δ)))
      =[pborrow_wsati M δ]=∗
      ([∗ list] Px ∈ Pxl, nborc δ α Px) ∗ [∗ list] Qx ∈ Qxl, nlend δ α Qx.
  Proof.
    setoid_rewrite <-nborc_tok_nborc. setoid_rewrite <-nlend_tok_nlend.
    exact: nborc_nlend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma nborc_nlend_new α Px :
    ⟦ Px ⟧(δ) =[pborrow_wsati M δ]=∗ nborc δ α Px ∗ nlend δ α Px.
  Proof.
    rewrite -nborc_tok_nborc -nlend_tok_nlend. exact: nborc_nlend_tok_new.
  Qed.

  (** Create new prophetic borrowers and lenders *)
  Lemma pborc_plend_new_list α Xl (xΦl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φx)' ∈ xΦl, ⟦ Φx x ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦl, plend_body_vari δ ξ Φx) -∗ M
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨl, plend_bodyi δ yπ Ψx))
        =[pborrow_wsati M δ]=∗
        ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦl, pborc δ α x ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨl, plend δ α yπ Ψx).
  Proof.
    iMod (pborc_plend_tok_new_list (M:=M) (sm:=⟦⟧(_))) as (?) "big". iModIntro.
    iExists _. iIntros (??). setoid_rewrite <-pborc_tok_pborc.
    setoid_rewrite <-plend_tok_plend. iApply "big".
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pborc_plend_new α X (x : X) Φx :
    ⟦ Φx x ⟧(δ) =[pborrow_wsati M δ]=∗ ∃ ξ,
      pborc δ α x ξ Φx ∗ plend δ α (λ π, π ξ) Φx.
  Proof.
    setoid_rewrite <-pborc_tok_pborc. setoid_rewrite <-plend_tok_plend.
    exact: pborc_plend_tok_new.
  Qed.
End pborrow_deriv.

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ,
  !PborrowPreDeriv TY (FML $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dsem JUDGI (FML $oi Σ) (iProp Σ), !PborrowDeriv TY FML Σ JUDGI,
  !GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.
  Implicit Type (X Y : TY) (Px Qx : FML $oi Σ).

  (** ** On non-prophetic borrowing *)

  (** Split a lender *)
  Lemma nlendd_split {α Px} Qxl :
    nlendd α Px -∗ (⟦ Px ⟧ -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧))
      =[pborrow_wsatid M]=∗ [∗ list] Qx ∈ Qxl, nlendd α Qx.
  Proof.
    rewrite {1}nlend_unseal. setoid_rewrite <-nlend_tok_nlend.
    iIntros "[%R[RP l]] →Ql".
    iApply (nlend_tok_split (M:=M) (sm:=⟦⟧) with "l [RP →Ql]").
    iIntros "R". rewrite der_pborrow_jto. iMod ("RP" with "R"). by iApply "→Ql".
  Qed.

  (** Retrive from [nlendd] *)
  Lemma nlendd_retrieve {α Px} :
    [†α] -∗ nlendd α Px -∗ modw M (pborrow_wsatid M) ⟦ Px ⟧.
  Proof.
    rewrite nlend_unseal. iIntros "† [%Qx[QP l]]". rewrite der_pborrow_jto.
    iMod (nlend_tok_retrieve (M:=M) (sm:=⟦⟧) with "† l") as "Qx".
    iMod ("QP" with "Qx") as "$". by iIntros.
  Qed.

  (** Open a closed borrower *)
  Lemma nborcd_open {α q Px} :
    q.[α] -∗ nborcd α Px =[pborrow_wsatid M]=∗ nobord α q Px ∗ ⟦ Px ⟧.
  Proof.
    rewrite nborc_unseal nobor_unseal. iIntros "α [%Qx[$[QP c]]]".
    iMod (nborc_tok_open (sm:=⟦⟧) with "α c") as "[$ Qx]".
    rewrite der_pborrow_jto. by iMod ("QP" with "Qx").
  Qed.
  (** Open a borrower *)
  Lemma nbord_open {α q Px} :
    q.[α] -∗ nbord α Px -∗ modw M (pborrow_wsatid M) (nobord α q Px ∗ ⟦ Px ⟧).
  Proof.
    rewrite nbor_unseal nobor_unseal. iIntros "α [%Qx[$[QP c]]]".
    iMod (nbor_tok_open (M:=M) (sm:=⟦⟧) with "α c") as "[$ Qx]".
    rewrite der_pborrow_jto. iMod ("QP" with "Qx") as "$". by iIntros.
  Qed.

  (** Lemma for [nobord_merge_subdiv] *)
  Local Lemma nobord_list {αqPl β} :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ nobord α q Px) ⊢
    ∃ αqRl,
      ⌜([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ⊣⊢
        [∗ list] '(α, q, _)' ∈ αqRl, q.[α]⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ nobor_tok α q R) ∗
      (([∗ list] '(_, _, Px)' ∈ αqPl, ⟦ Px ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    rewrite nobor_unseal /=. elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q Px]] αqPl ->) "[[⊑[%R[PR o]]][%αqRl[%[ol →']]]]".
    iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol".
    iSplit; [iPureIntro; by f_equiv|]. iIntros "[Px Pxl]".
    rewrite der_pborrow_jto. iMod ("PR" with "Px") as "$".
    iApply ("→'" with "Pxl").
  Qed.
  (** Merge and subdivide open borrowers *)
  Lemma nobord_merge_subdiv αqPl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPl, β ⊑□ α ∗ nobord α q Px) -∗
    ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M
      ([∗ list] '(_, _, Px)' ∈ αqPl, ⟦ Px ⟧)) =[pborrow_wsatid M]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Qx ∈ Qxl, nborcd β Qx).
  Proof.
    rewrite nobord_list /=. iIntros "[%[->[ol →]]] Qxl →Pl".
    setoid_rewrite <-nborc_tok_nborc.
    iApply (nobor_tok_merge_subdiv (M:=M) with "ol Qxl [→ →Pl]").
    iIntros "† Qxl". iMod ("→Pl" with "† Qxl") as "Pxl".
    iMod ("→" with "Pxl") as "$". by iIntros.
  Qed.
  (** Subdivide open borrowers *)
  Lemma nobord_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ nobord α q Px -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M ⟦ Px ⟧) =[pborrow_wsatid M]=∗
      q.[α] ∗ ([∗ list] Qx ∈ Qxl, nborcd β Qx).
  Proof.
    iIntros "⊑ o Qxl →P".
    iMod (nobord_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→P]") as "[[$ _]$]"
      =>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma nobord_close {α q Px} :
    nobord α q Px -∗ ⟦ Px ⟧ =[pborrow_wsatid M]=∗ q.[α] ∗ nborcd α Px.
  Proof.
    iIntros "o Px".
    iMod (nobord_subdiv [Px] with "[] o [Px] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Turn [nobord] to [nobor_tok] *)
  Lemma nobord_nobor_tok {α q Px} :
    nobord α q Px -∗ ⟦ Px ⟧ =[pborrow_wsatid M]=∗ nobor_tok α q Px ∗ ⟦ Px ⟧.
  Proof.
    rewrite nobor_unseal. iIntros "[%[ΦΨ o]] Px".
    iMod (nobor_tok_subdiv (M:=M) (sm:=⟦⟧) [_] with "[] o [$Px //] [ΦΨ]")
      as "[α[c _]]".
    { iApply lft_sincl_refl. }
    { rewrite der_pborrow_jto /=. iIntros "_ [Px _]".
      by iMod ("ΦΨ" with "Px"). }
    iApply (nborc_tok_open (sm:=⟦⟧) with "α c").
  Qed.

  (** Reborrow a borrower *)
  Lemma nobord_reborrow {α q Px} β :
    nobord α q Px -∗ ⟦ Px ⟧ =[pborrow_wsatid M]=∗
      q.[α] ∗ nborcd (α ⊓ β) Px ∗ ([†β] -∗ nbord α Px).
  Proof.
    iIntros "o Px". iMod (nobord_nobor_tok with "o Px") as "[o Px]".
    rewrite -nborc_tok_nborc -nbor_tok_nbor.
    iApply (nobor_tok_reborrow (M:=M) (sm:=⟦⟧) with "o Px").
  Qed.
  Lemma nborcd_reborrow {α q Px} β :
    q.[α] -∗ nborcd α Px =[pborrow_wsatid M]=∗
      q.[α] ∗ nborcd (α ⊓ β) Px ∗ ([†β] -∗ nbord α Px).
  Proof.
    iIntros "α c". iMod (nborcd_open with "α c") as "[o Px]".
    by iMod (nobord_reborrow with "o Px").
  Qed.
  Lemma nbord_reborrow {α q Px} β :
    q.[α] -∗ nbord α Px -∗ modw M (pborrow_wsatid M)
      (q.[α] ∗ nborcd (α ⊓ β) Px ∗ ([†β] -∗ nbord α Px)).
  Proof.
    iIntros "α b". iMod (nbord_open with "α b") as "[o Px]".
    by iMod (nobord_reborrow with "o Px").
  Qed.

  (** ** On prophetic borrowing *)

  (** Split a prophetic lender *)
  Lemma plendd_split {X α xπ} {Φx : X → _} Yl
    (yπΨl : plist (λ Y, _ *' (Y → _)) Yl) :
    plendd α xπ Φx -∗
    (plend_bodyid xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨl, plend_bodyid yπ Ψx))
      =[pborrow_wsatid M]=∗ [∗ plist] '(yπ, Ψx)' ∈ yπΨl, plendd α yπ Ψx.
  Proof.
    rewrite {1}plend_unseal. iIntros "(%Z & %zπ & %Ω & ΩΦ & l) →Ψl".
    setoid_rewrite <-plend_tok_plend.
    iApply (plend_tok_split (M:=M) (sm:=⟦⟧) with "l [ΩΦ →Ψl]"). iIntros "lb".
    rewrite der_pborrow_jlto. iMod ("ΩΦ" with "lb") as "?". by iApply "→Ψl".
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plendd_retrieve {X α xπ} {Φx : X → _} :
    [†α] -∗ plendd α xπ Φx -∗ modw M (pborrow_wsatid M) (plend_bodyid xπ Φx).
  Proof.
    rewrite {1}plend_unseal. iIntros "† (%Y & %yπ & %Ψx & ΨΦ & l)".
    iMod (plend_tok_retrieve (M:=M) (sm:=⟦⟧) with "† l") as "lb".
    rewrite der_pborrow_jlto. iMod ("ΨΦ" with "lb") as "$". by iIntros.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pborcd_open {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pborcd α x ξ Φx =[pborrow_wsatid M]=∗ pobord α q ξ Φx ∗ ⟦ Φx x ⟧.
  Proof.
    rewrite pborc_unseal pobor_unseal. iIntros "α [%[ΦΨ[ΨΦ c]]]".
    iMod (pborc_tok_open (sm:=⟦⟧) with "α c") as "[$ Ψx]".
    by iMod (der_pborrow_jto with "ΨΦ Ψx") as "$".
  Qed.
  Lemma pbord_open {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (pborrow_wsatid M)
      (pobord α q ξ Φx ∗ ⟦ Φx x ⟧).
  Proof.
    rewrite pbor_unseal pobor_unseal. iIntros "α [%[ΦΨ[ΨΦ b]]]".
    iMod (pbor_tok_open (M:=M) (sm:=⟦⟧) with "α b") as "[$ Ψx]".
    iMod (der_pborrow_jto with "ΨΦ Ψx") as "$". by iIntros "$".
  Qed.

  (** Lemma for [pobord_merge_subdiv] *)
  Local Lemma pobord_plist {Xl A β}
    {αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl} :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobord α q ξ Φx) ⊢
      ∃ αqξΩfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl,
      ⌜([∗ plist] '(α, q, _)' ∈ αqξΦfl, q.[α]) ⊣⊢
        [∗ plist] '(α, q, _)' ∈ αqξΩfl, q.[α]⌝ ∗
      ⌜∀ aπ,
        ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
          ⟨π, π (Aprvar _ ξ) = f (aπ π)⟩) ⊣⊢
        [∗ plist] '(_, _, ξ, _, f)' ∈ αqξΩfl, ⟨π, π (Aprvar _ ξ) = f (aπ π)⟩⌝ ∗
      ([∗ plist] '(α, q, ξ, Ω, _)' ∈ αqξΩfl, β ⊑□ α ∗ pobor_tok α q ξ Ω) ∗
      (∀ a, ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦfl, ⟦ Φx (f a) ⟧) ==∗
        [∗ plist] '(_, _, _, Ω, f)' ∈ αqξΩfl, ⟦ Ω (f a) ⟧).
  Proof.
    rewrite pobor_unseal. elim: Xl αqξΦfl=>/=.
    { iIntros. iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[α[q[ξ[Φx f]]]] αqξΦfl]. rewrite IH.
    iIntros "[[⊑[%Ω[ΦΩ o]]][%αqξΩfl[%[%[ol →']]]]]".
    iExists ((α, q, ξ, Ω, f)', αqξΩfl)'. iFrame "⊑ o ol".
    do 2 (iSplit; [iPureIntro=> >; by f_equiv|]). iIntros (a) "[Φx Φxl]".
    iMod (der_pborrow_jto with "ΦΩ Φx") as "$". by iApply "→'".
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma pobord_merge_subdiv Xl Yl
    (αqξΦfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨl : plist _ Yl) Rl
    β :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦfl, β ⊑□ α ∗ pobord α q ξ Φx) -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨl, ⟦ Ψx y ⟧) -∗ ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨl, ⟦ Ψx y' ⟧) -∗
      ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗ M
        ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦfl, ⟦ Φx (f yl') ⟧))
      =[pborrow_wsatid M]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨl, pborcd β y η Ψx) ∗
      [∗ list] R ∈ Rl, nborcd β R.
  Proof.
    rewrite pobord_plist /=. iIntros "(% & %eq & %eq' & ol & →) Ψxl Rl →Φxl".
    setoid_rewrite eq. setoid_rewrite eq'. setoid_rewrite <-pborc_tok_pborc.
    setoid_rewrite <-nborc_tok_nborc.
    iApply (pobor_tok_merge_subdiv (M:=M) (sm:=⟦⟧) with "ol Ψxl Rl").
    iIntros "% † Ψxl Rl". iMod ("→Φxl" with "† Ψxl Rl") as "Φxl".
    by iMod ("→" with "Φxl").
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobord_subdiv {X α q ξ Φx} Yl (f : _ → X) (yΨl : plist _ Yl) Rl β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨl, ⟦ Ψx y ⟧) -∗ ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨl, ⟦ Ψx y' ⟧) -∗
      ([∗ list] R ∈ Rl, ⟦ R ⟧) -∗ M ⟦ Φx (f yl') ⟧) =[pborrow_wsatid M]=∗ ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨl, pborcd β y η Ψx) ∗
      [∗ list] R ∈ Rl, nborcd β R.
  Proof.
    iIntros "⊑ o Ψxl Rl →Φx".
    iMod (pobord_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψxl Rl [→Φx]") as (?) "/=[[$ _][[$ _]$]]"; [|done].
    iIntros (?). by rewrite /= bi.sep_emp.
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobord_resolve {X α q ξ Φx} (x : X) :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[pborrow_wsatid M]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborcd α (Φx x).
  Proof.
    iIntros "o Φx".
    iMod (pobord_subdiv [] (λ _, x) () [Φx x] with "[] o [//] [Φx] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pborcd_resolve {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pborcd α x ξ Φx =[pborrow_wsatid M]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborcd α (Φx x).
  Proof.
    iIntros "α c". iMod (pborcd_open with "α c") as "[o Φx]".
    iApply (pobord_resolve with "o Φx").
  Qed.
  Lemma pbord_resolve {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (pborrow_wsatid M)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nborcd α (Φx x)).
  Proof.
    iIntros "α b". iMod (pbord_open with "α b") as "[o Φx]".
    iMod (pobord_resolve with "o Φx") as "$". by iIntros.
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobord_nsubdiv {X α q ξ Φx} Ψx (x : X) β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗ ⟦ Ψx x ⟧ -∗
    (∀ x', [†β] -∗ ⟦ Ψx x' ⟧ -∗ M ⟦ Φx x' ⟧) =[pborrow_wsatid M]=∗
      q.[α] ∗ pborcd β x ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ [%Ω[ΦΩ o]] Ψx →Φx".
    rewrite -pborc_tok_pborc.
    iApply (pobor_tok_nsubdiv (M:=M) (sm:=⟦⟧) with "⊑ o Ψx [ΦΩ →Φx]").
    iIntros "% † Ψx". iMod ("→Φx" with "† Ψx") as "Φx".
    by iMod (der_pborrow_jto with "ΦΩ Φx").
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobord_close {X α q ξ Φx} (x : X) :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[pborrow_wsatid M]=∗ q.[α] ∗ pborcd α x ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobord_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Turn [pobord] into [pobor_tok] *)
  Lemma pobord_pobor_tok {X α q ξ Φx} {x : X} :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[pborrow_wsatid M]=∗
      pobor_tok α q ξ Φx ∗ ⟦ Φx x ⟧.
  Proof.
    rewrite pobor_unseal. iIntros "[%Ψx[ΦΨ o]] Φx".
    iMod (pobor_tok_nsubdiv (M:=M) (sm:=⟦⟧) with "[] o Φx [ΦΨ]") as "[β c]".
    { iApply lft_sincl_refl. }
    { iIntros (?) "_ Φx". by iMod (der_pborrow_jto with "ΦΨ Φx"). }
    iApply (pborc_tok_open (sm:=⟦⟧) with "β c").
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobord_pobord_reborrow {X Y α q ξ Φx β r η Ψx} y (f : X → Y) :
    pobord α q ξ Φx -∗ pobord β r η Ψx -∗ ⟦ Ψx y ⟧ -∗
    (∀ y', [†α] -∗ pbord β y' η Ψx -∗ M ⟦ Φx (f y') ⟧) =[pborrow_wsatid M]=∗
      ∃ η',
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pborcd (α ⊓ β) y η' Ψx.
  Proof.
    rewrite {1}pobor_unseal. iIntros "[%Φx'[ΦΦ' o]] o' Ψx →Φx".
    iMod (pobord_pobor_tok with "o' Ψx") as "[o' Ψx]".
    setoid_rewrite <-pborc_tok_pborc.
    iApply (pobor_pobor_tok_reborrow (M:=M) (sm:=⟦⟧) with "o o' Ψx").
    iIntros "% † b". rewrite pbor_tok_pbor. iMod ("→Φx" with "† b") as "Φx".
    by iMod (der_pborrow_jto with "ΦΦ' Φx").
  Qed.
  Lemma pobord_pborcd_reborrow {X Y α q ξ Φx β r y η Ψx} (f : X → Y) :
    pobord α q ξ Φx -∗ r.[β] -∗ pborcd β y η Ψx -∗
    (∀ y', [†α] -∗ pbord β y' η Ψx -∗ M ⟦ Φx (f y') ⟧) =[pborrow_wsatid M]=∗
      ∃ η',
      q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pborcd (α ⊓ β) y η' Ψx.
  Proof.
    iIntros "o r c →Φx". iMod (pborcd_open with "r c") as "[o' Ψx]".
    by iMod (pobord_pobord_reborrow with "o o' Ψx →Φx").
  Qed.
  Lemma pobord_pbord_reborrow {X Y α q ξ Φx β r y η Ψx} (f : X → Y) :
    pobord α q ξ Φx -∗ r.[β] -∗ pbord β y η Ψx -∗
    (∀ y', [†α] -∗ pbord β y' η Ψx -∗ M ⟦ Φx (f y') ⟧) -∗
      modw M (pborrow_wsatid M) (∃ η',
        q.[α] ∗ r.[β] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗
        pborcd (α ⊓ β) y η' Ψx).
  Proof.
    iIntros "o r b →Φx". iMod (pbord_open with "r b") as "[o' Ψx]".
    by iMod (pobord_pobord_reborrow with "o o' Ψx →Φx").
  Qed.
End pborrow_deriv.
