(** * Prophetic borrowing machinery relaxed with derivability *)

From nola.bi Require Export deriv.
From nola.bi Require Import list.
From nola.iris Require Export pborrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation iPropAppNotation PintpNotation IntpNotation
  UpdwNotation LftNotation.

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
Class PborrowPreDeriv TY (PRO JUDG : ofe) := PBORROW_PRE_DERIV {
  (** Basic conversion judgment *)
  pborrow_jto : PRO → PRO → JUDG;
  (** Conversion judgment for [lend_body] *)
  pborrow_jlto {X Y : TY} : clair TY X → clair TY Y →
    (X -d> PRO) → (Y -d> PRO) → JUDG;
  (** [pborrow_jto] is non-expansive *)
  pborrow_jto_ne :: NonExpansive2 pborrow_jto;
  (** [pborrow_jto] is non-expansive *)
  pborrow_jlto_ne {X Y xπ yπ} :: NonExpansive2 (@pborrow_jlto X Y xπ yπ);
}.
Hint Mode PborrowPreDeriv - ! - : typeclass_instances.
Arguments PBORROW_PRE_DERIV {_ _ _} _ _ {_ _}.

Section pborrow_deriv.
  Context `{!pborrowGS TY PROP Σ, !PborrowPreDeriv TY (PROP $oi Σ) JUDG}.
  Implicit Type (δ : JUDG → iProp Σ) (X Y : TY).

  (** [nborc]: Relaxed non-prophetic closed borrower *)
  Local Definition nborc_def δ α P : iProp Σ :=
    ∃ Q, δ (pborrow_jto P Q) ∗ δ (pborrow_jto Q P) ∗ nborc_tok α Q.
  Local Lemma nborc_aux : seal nborc_def. Proof. by eexists. Qed.
  Definition nborc := nborc_aux.(unseal).
  Local Lemma nborc_unseal : nborc = nborc_def. Proof. exact: seal_eq. Qed.
  (** [nbor]: Relaxed non-prophetic borrower *)
  Local Definition nbor_def δ α P : iProp Σ :=
    ∃ Q, δ (pborrow_jto P Q) ∗ δ (pborrow_jto Q P) ∗ nbor_tok α Q.
  Local Lemma nbor_aux : seal nbor_def. Proof. by eexists. Qed.
  Definition nbor := nbor_aux.(unseal).
  Local Lemma nbor_unseal : nbor = nbor_def. Proof. exact: seal_eq. Qed.
  (** [nobor]: Relaxed non-prophetic open borrower *)
  Local Definition nobor_def δ α q P : iProp Σ :=
    ∃ Q, δ (pborrow_jto P Q) ∗ nobor_tok α q Q.
  Local Lemma nobor_aux : seal nobor_def. Proof. by eexists. Qed.
  Definition nobor := nobor_aux.(unseal).
  Local Lemma nobor_unseal : nobor = nobor_def. Proof. exact: seal_eq. Qed.
  (** [nlend]: Relaxed non-prophetic lender *)
  Local Definition nlend_def δ α P : iProp Σ :=
    ∃ Q, δ (pborrow_jto Q P) ∗ nlend_tok α Q.
  Local Lemma nlend_aux : seal nlend_def. Proof. by eexists. Qed.
  Definition nlend := nlend_aux.(unseal).
  Local Lemma nlend_unseal : nlend = nlend_def. Proof. exact: seal_eq. Qed.

  (** [pborc]: Relaxed prophetic closed borrower *)
  Local Definition pborc_def {X} δ α x ξ (Φ : X -d> _) : iProp Σ :=
    ∃ Ψ, (∀ x, δ (pborrow_jto (Φ x) (Ψ x))) ∗
      (∀ x, δ (pborrow_jto (Ψ x) (Φ x))) ∗ pborc_tok α x ξ Ψ.
  Local Lemma pborc_aux : seal (@pborc_def). Proof. by eexists. Qed.
  Definition pborc {X} := pborc_aux.(unseal) X.
  Local Lemma pborc_unseal : @pborc = @pborc_def. Proof. exact: seal_eq. Qed.
  (** [pbor]: Relaxed prophetic borrower *)
  Local Definition pbor_def {X} δ α x ξ (Φ : X -d> _) : iProp Σ :=
    ∃ Ψ, (∀ x, δ (pborrow_jto (Φ x) (Ψ x))) ∗
      (∀ x, δ (pborrow_jto (Ψ x) (Φ x))) ∗ pbor_tok α x ξ Ψ.
  Local Lemma pbor_aux : seal (@pbor_def). Proof. by eexists. Qed.
  Definition pbor {X} := pbor_aux.(unseal) X.
  Local Lemma pbor_unseal : @pbor = @pbor_def. Proof. exact: seal_eq. Qed.
  (** [pobor]: Relaxed prophetic open borrower *)
  Local Definition pobor_def {X} δ α q ξ (Φ : X -d> _) : iProp Σ :=
    ∃ Ψ, (∀ x, δ (pborrow_jto (Φ x) (Ψ x))) ∗ pobor_tok α q ξ Ψ.
  Local Lemma pobor_aux : seal (@pobor_def). Proof. by eexists. Qed.
  Definition pobor {X} := pobor_aux.(unseal) X.
  Local Lemma pobor_unseal : @pobor = @pobor_def. Proof. exact: seal_eq. Qed.
  (** [plend]: Relaxed prophetic lender *)
  Local Definition plend_def {X} δ α xπ (Φ : X -d> _) : iProp Σ :=
    ∃ Y yπ Ψ, δ (pborrow_jlto yπ xπ Ψ Φ) ∗ plend_tok (X:=Y) α yπ Ψ.
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
  Context `{!pborrowGS TY PROP Σ,
    !PborrowPreDeriv TY (PROP $oi Σ) (JUDGI : judgi (iProp Σ)),
    !Dintp JUDGI (PROP $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDGI → iProp Σ) (P Q : PROP $oi Σ).

  (** Derivability data for [pborrow] *)
  Class PborrowDeriv := PBORROW_DERIV {
    (** Interpreting [pborrow_jto] *)
    pborrow_jto_intp : ∀{δ P Q},
      ⟦ pborrow_jto P Q ⟧(δ) ⊣⊢ (⟦ P ⟧(δ) ==∗ ⟦ Q ⟧(δ));
    (** Interpreting [pborrow_jlto] *)
    pborrow_jlto_intp : ∀{δ X Y xπ yπ} {Φ Ψ : _ -d> PROP $oi Σ},
      ⟦ pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φ Ψ ⟧(δ) ⊣⊢
        (plend_body ⟦ ⟧(δ) xπ Φ ==∗ plend_body ⟦ ⟧(δ) yπ Ψ);
  }.
End pborrow_deriv.
Arguments PborrowDeriv TY PROP Σ {_} JUDGI {_ _}.
Hint Mode PborrowDeriv - ! - - - - - : typeclass_instances.

Section pborrow_deriv.
  Context `{!pborrowGS TY PROP Σ,
  !PborrowPreDeriv TY (PROP $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dintp JUDGI (PROP $oi Σ) (iProp Σ), !PborrowDeriv TY PROP Σ JUDGI,
  !Deriv (JUDGI:=JUDGI) ih δ}.
  Implicit Type (X Y Z : TY) (P Q R : PROP $oi Σ) (δ : JUDGI → iProp Σ).

  (** ** Conversion *)

  (** Lemmas for [pborrow_jto] *)
  Lemma pborrow_jto_refl {P} : ⊢ δ (pborrow_jto P P).
  Proof.
    iApply Deriv_to. iIntros (????). rewrite pborrow_jto_intp. by iIntros "$".
  Qed.
  Lemma pborrow_jto_trans {P Q R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    δ (pborrow_jto Q R) -∗ δ (pborrow_jto P R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !pborrow_jto_intp.
    iIntros "QR P". iMod ("big" with "[//] [//] [//] P"). by iApply "QR".
  Qed.
  Lemma pborrow_jto_trans' {P Q R} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ R ⟧(δ')) -∗
    δ (pborrow_jto P Q) -∗ δ (pborrow_jto P R).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !pborrow_jto_intp.
    iIntros "ΦΨ P". iMod ("ΦΨ" with "P"). by iApply "big".
  Qed.
  Lemma der_pborrow_jto {P Q} :
    der (pborrow_jto P Q) ⊢ (⟦ P ⟧ ==∗ ⟦ Q ⟧).
  Proof. by rewrite der_sound pborrow_jto_intp. Qed.

  (** Lemmas for [pborrow_jlto] *)
  Lemma pborrow_jlto_refl {X xπ Φ} :
    ⊢ δ (pborrow_jlto (PRO:=PROP $oi Σ) (X:=X) xπ xπ Φ Φ).
  Proof.
    iApply Deriv_to. iIntros (????). rewrite pborrow_jlto_intp. by iIntros "$".
  Qed.
  Lemma pborrow_jlto_trans {X Y Z xπ yπ zπ Φ Ψ Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φ ==∗ plend_body ⟦ ⟧(δ') yπ Ψ) -∗
    δ (pborrow_jlto (X:=Y) (Y:=Z) yπ zπ Ψ Ω) -∗
    δ (pborrow_jlto (X:=X) xπ zπ Φ Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !pborrow_jlto_intp. iIntros "ΨΩ Φ".
    iMod ("big" with "[//] [//] [//] Φ"). by iApply "ΨΩ".
  Qed.
  Lemma pborrow_jlto_trans' {X Y Z xπ yπ zπ Φ Ψ Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') yπ Ψ ==∗ plend_body ⟦ ⟧(δ') zπ Ω) -∗
    δ (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φ Ψ) -∗
    δ (pborrow_jlto (Y:=Z) xπ zπ Φ Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !pborrow_jlto_intp. iIntros "ΦΨ Φ". iMod ("ΦΨ" with "Φ").
    by iApply "big".
  Qed.
  Lemma der_pborrow_jlto {X Y xπ yπ Φ Ψ} :
    der (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φ Ψ) ⊢
      (plend_bodyid xπ Φ ==∗ plend_bodyid yπ Ψ).
  Proof. by rewrite der_sound pborrow_jlto_intp. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma nborc_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    nborc δ α P -∗ nborc δ α Q.
  Proof.
    rewrite nborc_unseal. iIntros "ΦΨ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "ΦΨ RP")].
  Qed.
  Lemma nbor_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    nbor δ α P -∗ nbor δ α Q.
  Proof.
    rewrite nbor_unseal. iIntros "ΦΨ QP [%R[PR[RP $]]]".
    iSplitL "QP PR"; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "ΦΨ RP")].
  Qed.
  Lemma nobor_to {α q P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Q ⟧(δ') ==∗ ⟦ P ⟧(δ')) -∗
    nobor δ α q P -∗ nobor δ α q Q.
  Proof.
    rewrite nobor_unseal. iIntros "QP [%R[PR $]]".
    iApply (pborrow_jto_trans with "QP PR").
  Qed.
  Lemma nlend_to {α P Q} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ P ⟧(δ') ==∗ ⟦ Q ⟧(δ')) -∗
    nlend δ α P -∗ nlend δ α Q.
  Proof.
    rewrite nlend_unseal. iIntros "ΦΨ [%R[RP $]]".
    iApply (pborrow_jto_trans' with "ΦΨ RP").
  Qed.
  Lemma pborc_to {X α x ξ Φ Ψ} :
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φ x' ⟧(δ') ==∗ ⟦ Ψ x' ⟧(δ')) -∗
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψ x' ⟧(δ') ==∗ ⟦ Φ x' ⟧(δ')) -∗
    pborc (X:=X) δ α x ξ Φ -∗ pborc δ α x ξ Ψ.
  Proof.
    rewrite pborc_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ $]]]".
    iSplitL "ΨΦ ΦΩ"; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma pbor_to {X α x ξ Φ Ψ} :
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φ x' ⟧(δ') ==∗ ⟦ Ψ x' ⟧(δ')) -∗
    (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψ x' ⟧(δ') ==∗ ⟦ Φ x' ⟧(δ')) -∗
    pbor (X:=X) δ α x ξ Φ -∗ pbor δ α x ξ Ψ.
  Proof.
    rewrite pbor_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ[ΩΦ $]]]".
    iSplitL "ΨΦ ΦΩ"; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma pobor_to {X α q ξ Φ Ψ} :
    (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φ x ⟧(δ') ==∗ ⟦ Ψ x ⟧(δ')) -∗
    (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψ x ⟧(δ') ==∗ ⟦ Φ x ⟧(δ')) -∗
    pobor (X:=X) δ α q ξ Φ -∗ pobor δ α q ξ Ψ.
  Proof.
    rewrite pobor_unseal. iIntros "ΦΨ ΨΦ [%Ω[ΦΩ $]]" (?).
    iApply (pborrow_jto_trans with "ΨΦ ΦΩ").
  Qed.
  Lemma plend_to {X Y α xπ yπ Φ Ψ} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φ ==∗ plend_body ⟦ ⟧(δ') yπ Ψ) -∗
    plend (X:=X) δ α xπ Φ -∗ plend (X:=Y) δ α yπ Ψ.
  Proof.
    rewrite plend_unseal. iIntros "ΦΨ (%Z & %zπ & %Ω & ΩΦ & $)".
    iApply (pborrow_jlto_trans' with "ΦΨ ΩΦ").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma nborc_lft {α β P} : β ⊑□ α -∗ nborc δ α P -∗ nborc δ β P.
  Proof.
    rewrite nborc_unseal. iIntros "⊑ [%[?[? c]]]".
    iDestruct (nborc_tok_lft with "⊑ c") as "$". iFrame.
  Qed.
  Lemma nbor_lft {α β P} : β ⊑□ α -∗ nbor δ α P -∗ nbor δ β P.
  Proof.
    rewrite nbor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (nbor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma nobor_lft {α β q r P} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ nobor δ α q P -∗ nobor δ β r P.
  Proof.
    rewrite nobor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (nobor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma nlend_lft {α β P} : α ⊑□ β -∗ nlend δ α P -∗ nlend δ β P.
  Proof.
    rewrite nlend_unseal. iIntros "⊑ [%[? l]]".
    by iDestruct (nlend_tok_lft with "⊑ l") as "$".
  Qed.
  Lemma pborc_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pborc (X:=X) δ α x ξ Φ -∗ pborc δ β x ξ Φ.
  Proof.
    rewrite pborc_unseal. iIntros "⊑ [%[?[? c]]]".
    iDestruct (pborc_tok_lft with "⊑ c") as "$". iFrame.
  Qed.
  Lemma pbor_lft {X α β x ξ Φ} :
    β ⊑□ α -∗ pbor (X:=X) δ α x ξ Φ -∗ pbor δ β x ξ Φ.
  Proof.
    rewrite pbor_unseal. iIntros "⊑ [%[?[? b]]]".
    iDestruct (pbor_tok_lft with "⊑ b") as "$". iFrame.
  Qed.
  Lemma pobor_lft {X α β q r ξ Φ} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ pobor (X:=X) δ α q ξ Φ -∗ pobor δ β r ξ Φ.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ → [%[? o]]".
    by iDestruct (pobor_tok_lft with "⊑ → o") as "$".
  Qed.
  Lemma plend_lft {X α β xπ Φ} :
    α ⊑□ β -∗ plend (X:=X) δ α xπ Φ -∗ plend δ β xπ Φ.
  Proof.
    rewrite plend_unseal. iIntros "⊑ (% & % & % & ? & l)".
    by iDestruct (plend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma nborc_tok_nborc {α P} : nborc_tok α P ⊢ nborc δ α P.
  Proof.
    rewrite nborc_unseal. iIntros "$". iSplitL; iApply pborrow_jto_refl.
  Qed.
  Lemma nbor_tok_nbor {α P} : nbor_tok α P ⊢ nbor δ α P.
  Proof.
    rewrite nbor_unseal. iIntros "$". iSplitL; iApply pborrow_jto_refl.
  Qed.
  Lemma nobor_tok_nobor {α q P} : nobor_tok α q P ⊢ nobor δ α q P.
  Proof. rewrite nobor_unseal. iIntros "$". iApply pborrow_jto_refl. Qed.
  Lemma nlend_tok_nlend {α P} : nlend_tok α P ⊢ nlend δ α P.
  Proof. rewrite nlend_unseal. iIntros "$". iApply pborrow_jto_refl. Qed.
  Lemma pborc_tok_pborc {X α x ξ Φ} :
    pborc_tok (X:=X) α x ξ Φ ⊢ pborc δ α x ξ Φ.
  Proof.
    rewrite pborc_unseal. iIntros "$".
    iSplitL; iIntros; iApply pborrow_jto_refl.
  Qed.
  Lemma pbor_tok_pbor {X α x ξ Φ} :
    pbor_tok (X:=X) α x ξ Φ ⊢ pbor δ α x ξ Φ.
  Proof.
    rewrite pbor_unseal. iIntros "$".
    iSplitL; iIntros; iApply pborrow_jto_refl.
  Qed.
  Lemma pobor_tok_pobor {X α q ξ Φ} :
    pobor_tok (X:=X) α q ξ Φ ⊢ pobor δ α q ξ Φ.
  Proof. rewrite pobor_unseal. iIntros "$" (?). iApply pborrow_jto_refl. Qed.
  Lemma plend_tok_plend {X α xπ Φ} : plend_tok (X:=X) α xπ Φ ⊢ plend δ α xπ Φ.
  Proof. rewrite plend_unseal. iIntros "$". iApply pborrow_jlto_refl. Qed.

  (** Other types of conversion *)
  Lemma nborc_nbor {α P} : nborc δ α P ⊢ nbor δ α P.
  Proof.
    rewrite nborc_unseal nbor_unseal. iIntros "[%[$[$?]]]".
    by rewrite nborc_tok_nbor_tok.
  Qed.
  Lemma nborc_fake {α} P : [†α] ⊢ nborc δ α P.
  Proof. by rewrite nborc_tok_fake nborc_tok_nborc. Qed.
  Lemma nbor_fake {α} P : [†α] ⊢ nbor δ α P.
  Proof. by rewrite nborc_fake nborc_nbor. Qed.
  Lemma pborc_pbor {X α x ξ Φ} : pborc (X:=X) δ α x ξ Φ ⊢ pbor δ α x ξ Φ.
  Proof.
    rewrite pborc_unseal pbor_unseal. iIntros "[%[$[$?]]]".
    by rewrite pborc_tok_pbor_tok.
  Qed.
  Lemma pborc_fake {X α} x ξ Φ : [†α] ⊢ pborc (X:=X) δ α x ξ Φ.
  Proof. by rewrite pborc_tok_fake pborc_tok_pborc. Qed.
  Lemma pbor_fake {X α} x ξ Φ : [†α] ⊢ pbor (X:=X) δ α x ξ Φ.
  Proof. by rewrite pborc_fake pborc_pbor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.

  (** ** Rules that work under [Deriv ih δ] *)

  (** Create borrowers and lenders *)
  Lemma nborc_nlend_new_list α Pl Ql :
    ([∗ list] P ∈ Pl, ⟦ P ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] P ∈ Pl, ⟦ P ⟧(δ)) -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧(δ)))
      =[pborrow_wsati M δ]=∗
      ([∗ list] P ∈ Pl, nborc δ α P) ∗ [∗ list] Q ∈ Ql, nlend δ α Q.
  Proof.
    setoid_rewrite <-nborc_tok_nborc. setoid_rewrite <-nlend_tok_nlend.
    exact: nborc_nlend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma nborc_nlend_new α P :
    ⟦ P ⟧(δ) =[pborrow_wsati M δ]=∗ nborc δ α P ∗ nlend δ α P.
  Proof.
    rewrite -nborc_tok_nborc -nlend_tok_nlend. exact: nborc_nlend_tok_new.
  Qed.

  (** Create new prophetic borrowers and lenders *)
  Lemma pborc_plend_new_list α Xl (xΦl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦl := plist_zip ξl xΦl in
      ([∗ plist] '(x, Φ)' ∈ xΦl, ⟦ Φ x ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, plend_body_vari δ ξ Φ) -∗ M
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend_bodyi δ yπ Ψ)) =[pborrow_wsati M δ]=∗
        ([∗ plist] '(ξ, x, Φ)' ∈ ξxΦl, pborc δ α x ξ Φ) ∗
        ([∗ plist] '(yπ, Ψ)' ∈ yπΨl, plend δ α yπ Ψ).
  Proof.
    iMod (pborc_plend_tok_new_list (M:=M) (ip:=⟦⟧(_))) as (?) "big". iModIntro.
    iExists _. iIntros (??). setoid_rewrite <-pborc_tok_pborc.
    setoid_rewrite <-plend_tok_plend. iApply "big".
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pborc_plend_new α X (x : X) Φ :
    ⟦ Φ x ⟧(δ) =[pborrow_wsati M δ]=∗ ∃ ξ,
      pborc δ α x ξ Φ ∗ plend δ α (λ π, π ξ) Φ.
  Proof.
    setoid_rewrite <-pborc_tok_pborc. setoid_rewrite <-plend_tok_plend.
    exact: pborc_plend_tok_new.
  Qed.
End pborrow_deriv.

Section pborrow_deriv.
  Context `{!pborrowGS TY PROP Σ,
  !PborrowPreDeriv TY (PROP $oi Σ) (JUDGI : judgi (iProp Σ)),
  !Dintp JUDGI (PROP $oi Σ) (iProp Σ), !PborrowDeriv TY PROP Σ JUDGI,
  !GenUpd (PROP:=iProp Σ) M, !GenUpdBupd M}.
  Implicit Type (P Q : PROP $oi Σ).

  (** ** On non-prophetic borrowing *)

  (** Split a lender *)
  Lemma nlendd_split {α P} Ql :
    nlendd α P -∗ (⟦ P ⟧ -∗ M ([∗ list] Q ∈ Ql, ⟦ Q ⟧)) =[pborrow_wsatid M]=∗
      [∗ list] Q ∈ Ql, nlendd α Q.
  Proof.
    rewrite {1}nlend_unseal. setoid_rewrite <-nlend_tok_nlend.
    iIntros "[%R[RP l]] →Ql".
    iApply (nlend_tok_split (M:=M) (ip:=⟦⟧) with "l [RP →Ql]").
    iIntros "R". rewrite der_pborrow_jto. iMod ("RP" with "R"). by iApply "→Ql".
  Qed.

  (** Retrive from [nlendd] *)
  Lemma nlendd_retrieve {α P} :
    [†α] -∗ nlendd α P -∗ modw M (pborrow_wsatid M) ⟦ P ⟧.
  Proof.
    rewrite nlend_unseal. iIntros "† [%Q[QP l]]". rewrite der_pborrow_jto.
    iMod (nlend_tok_retrieve (M:=M) (ip:=⟦⟧) with "† l") as "Q".
    iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Open a closed borrower *)
  Lemma nborcd_open {α q P} :
    q.[α] -∗ nborcd α P =[pborrow_wsatid M]=∗ nobord α q P ∗ ⟦ P ⟧.
  Proof.
    rewrite nborc_unseal nobor_unseal. iIntros "α [%Q[$[QP c]]]".
    iMod (nborc_tok_open (ip:=⟦⟧) with "α c") as "[$ Q]".
    rewrite der_pborrow_jto. by iMod ("QP" with "Q").
  Qed.
  (** Open a borrower *)
  Lemma nbord_open {α q P} :
    q.[α] -∗ nbord α P -∗ modw M (pborrow_wsatid M) (nobord α q P ∗ ⟦ P ⟧).
  Proof.
    rewrite nbor_unseal nobor_unseal. iIntros "α [%Q[$[QP c]]]".
    iMod (nbor_tok_open (M:=M) (ip:=⟦⟧) with "α c") as "[$ Q]".
    rewrite der_pborrow_jto. iMod ("QP" with "Q") as "$". by iIntros.
  Qed.

  (** Lemma for [nobord_merge_subdiv] *)
  Local Lemma nobord_list {αqPl β} :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ nobord α q P) ⊢
    ∃ αqRl,
      ⌜(λ '(α, q, _)', (α, q)') <$> αqRl = (λ '(α, q, _)', (α, q)') <$> αqPl⌝ ∗
      ([∗ list] '(α, q, R)' ∈ αqRl, β ⊑□ α ∗ nobor_tok α q R) ∗
      (([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧) ==∗
        [∗ list] '(_, _, R)' ∈ αqRl, ⟦ R ⟧).
  Proof.
    rewrite nobor_unseal /=. elim: αqPl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q P]] αqPl ->) "[[⊑[%R[PR o]]][%αqRl[%[ol →']]]]".
    iExists ((α, q, R)' :: αqRl)=>/=. iFrame "⊑ o ol". iSplit.
    { iPureIntro. by f_equal. }
    iIntros "[P Pl]". rewrite der_pborrow_jto. iMod ("PR" with "P") as "$".
    iApply ("→'" with "Pl").
  Qed.
  (** Merge and subdivide open borrowers *)
  Lemma nobord_merge_subdiv αqPl Ql β :
    ([∗ list] '(α, q, P)' ∈ αqPl, β ⊑□ α ∗ nobord α q P) -∗
    ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M
      ([∗ list] '(_, _, P)' ∈ αqPl, ⟦ P ⟧)) =[pborrow_wsatid M]=∗
      ([∗ list] '(α, q, _)' ∈ αqPl, q.[α]) ∗ ([∗ list] Q ∈ Ql, nborcd β Q).
  Proof.
    rewrite nobord_list /=.
    rewrite -(big_sepL_fmap (λ '(α, q, _)', (α, q)') (λ _ '(α, q)', q.[α])%I).
    iIntros "[%[<-[ol →]]] Ql →Pl". rewrite big_sepL_fmap.
    setoid_rewrite <-nborc_tok_nborc.
    iApply (nobor_tok_merge_subdiv (M:=M) with "ol Ql [→ →Pl]"). iIntros "† Ql".
    iMod ("→Pl" with "† Ql") as "Pl". iMod ("→" with "Pl") as "$". by iIntros.
  Qed.
  (** Subdivide open borrowers *)
  Lemma nobord_subdiv {α q P} Ql β :
    β ⊑□ α -∗ nobord α q P -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗
    ([†β] -∗ ([∗ list] Q ∈ Ql, ⟦ Q ⟧) -∗ M ⟦ P ⟧) =[pborrow_wsatid M]=∗
      q.[α] ∗ ([∗ list] Q ∈ Ql, nborcd β Q).
  Proof.
    iIntros "⊑ o Ql →P".
    iMod (nobord_merge_subdiv [(_,_,_)'] with "[⊑ o] Ql [→P]") as "[[$ _]$]"
      =>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.
  (** Simply close a borrower *)
  Lemma nobord_close {α q P} :
    nobord α q P -∗ ⟦ P ⟧ =[pborrow_wsatid M]=∗ q.[α] ∗ nborcd α P.
  Proof.
    iIntros "o P".
    iMod (nobord_subdiv [P] with "[] o [P] []") as "[$[$_]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "_[$_]"|].
  Qed.

  (** Turn [nobord] to [nobor_tok] *)
  Lemma nobord_nobor_tok {α q P} :
    nobord α q P -∗ ⟦ P ⟧ =[pborrow_wsatid M]=∗ nobor_tok α q P ∗ ⟦ P ⟧.
  Proof.
    rewrite nobor_unseal. iIntros "[%[ΦΨ o]] P".
    iMod (nobor_tok_subdiv (M:=M) (ip:=⟦⟧) [_] with "[] o [$P //] [ΦΨ]")
      as "[α[c _]]".
    { iApply lft_sincl_refl. }
    { rewrite der_pborrow_jto /=. iIntros "_ [P _]". by iMod ("ΦΨ" with "P"). }
    iApply (nborc_tok_open (ip:=⟦⟧) with "α c").
  Qed.

  (** Reborrow a borrower *)
  Lemma nobord_reborrow {α q P} β :
    nobord α q P -∗ ⟦ P ⟧ =[pborrow_wsatid M]=∗
      q.[α] ∗ nborcd (α ⊓ β) P ∗ ([†β] -∗ nbord α P).
  Proof.
    iIntros "o P". iMod (nobord_nobor_tok with "o P") as "[o P]".
    rewrite -nborc_tok_nborc -nbor_tok_nbor.
    iApply (nobor_tok_reborrow (M:=M) (ip:=⟦⟧) with "o P").
  Qed.
  Lemma nborcd_reborrow {α q P} β :
    q.[α] -∗ nborcd α P =[pborrow_wsatid M]=∗
      q.[α] ∗ nborcd (α ⊓ β) P ∗ ([†β] -∗ nbord α P).
  Proof.
    iIntros "α c". iMod (nborcd_open with "α c") as "[o P]".
    by iMod (nobord_reborrow with "o P").
  Qed.
  Lemma nbord_reborrow {α q P} β :
    q.[α] -∗ nbord α P -∗ modw M (pborrow_wsatid M)
      (q.[α] ∗ nborcd (α ⊓ β) P ∗ ([†β] -∗ nbord α P)).
  Proof.
    iIntros "α b". iMod (nbord_open with "α b") as "[o P]".
    by iMod (nobord_reborrow with "o P").
  Qed.
End pborrow_deriv.
