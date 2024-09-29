(** * Prophetic borrowing machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export pborrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation FunNPNotation iPropAppNotation UpdwNotation
  LftNotation ProphNotation DsemNotation.

Implicit Type (TY : synty) (FM : ofe).

(** ** [pborrow_judgty]: Judgment type for [pborrow] *)
Variant pborrow_judg_id TY FM := .
Definition pborrow_judgty TY (FM : ofe) : ofe := tagged (pborrow_judg_id TY FM)
  ((** Basic conversion *) FM * FM +
  (** Conversion judgment for [lend_body] *)
    @sigT (TY *' TY) (λ '(X, Y)',
      leibnizO (clair TY X *' clair TY Y) *
      (X -d> FM) * (Y -d> FM)))%type.

(** ** [PborrowJudg]: Judgment structure for [pborrow] *)
Notation PborrowJudg TY FM JUDG := (Ejudg (pborrow_judgty TY FM) JUDG).

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ,
    pborrow_judg : !PborrowJudg TY (FML $oi Σ) JUDG}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : FML $oi Σ) (X Y : TY).

  (** Judgments *)
  Local Definition pborrow_jto Px Qx : JUDG :=
    pborrow_judg (Tagged (inl (Px, Qx))).
  Local Definition pborrow_jlto {X Y} (xπ : clair TY X) (yπ : clair TY Y)
    (Φx : X -d> FML $oi Σ) (Ψx : Y -d> FML $oi Σ) : JUDG :=
    pborrow_judg (Tagged (inr (existT (X, Y)' ((xπ, yπ)', Φx, Ψx)))).
  #[export] Instance pborrow_jto_ne : NonExpansive2 pborrow_jto.
  Proof. solve_proper. Qed.
  #[export] Instance pborrow_jlto_ne {X Y xπ yπ} :
    NonExpansive2 (@pborrow_jlto X Y xπ yπ).
  Proof.
    unfold pborrow_jlto=> ???????. f_equiv. apply inr_ne. apply: existT_ne=>/=.
    split; [split|]; solve_proper.
  Qed.

  (** [nbor]: Relaxed non-prophetic borrower *)
  Local Definition nbor_def δ α Px : iProp Σ :=
    ∃ Qx, □ δ (pborrow_jto Px Qx) ∗ □ δ (pborrow_jto Qx Px) ∗ nbor_tok α Qx.
  Local Lemma nbor_aux : seal nbor_def. Proof. by eexists. Qed.
  Definition nbor := nbor_aux.(unseal).
  Local Lemma nbor_unseal : nbor = nbor_def. Proof. exact: seal_eq. Qed.
  (** [nobor]: Relaxed non-prophetic open borrower *)
  Local Definition nobor_def δ α q Px : iProp Σ :=
    ∃ Qx, □ δ (pborrow_jto Px Qx) ∗ □ δ (pborrow_jto Qx Px) ∗ nobor_tok α q Qx.
  Local Lemma nobor_aux : seal nobor_def. Proof. by eexists. Qed.
  Definition nobor := nobor_aux.(unseal).
  Local Lemma nobor_unseal : nobor = nobor_def. Proof. exact: seal_eq. Qed.
  (** [nlend]: Relaxed non-prophetic lender *)
  Local Definition nlend_def δ α Px : iProp Σ :=
    ∃ Qx, □ δ (pborrow_jto Qx Px) ∗ nlend_tok α Qx.
  Local Lemma nlend_aux : seal nlend_def. Proof. by eexists. Qed.
  Definition nlend := nlend_aux.(unseal).
  Local Lemma nlend_unseal : nlend = nlend_def. Proof. exact: seal_eq. Qed.

  (** [pbor]: Relaxed prophetic borrower *)
  Local Definition pbor_def {X} δ α x ξ (Φx : X -d> _) : iProp Σ :=
    ∃ Ψx, □ (∀ x, δ (pborrow_jto (Φx x) (Ψx x))) ∗
      □ (∀ x, δ (pborrow_jto (Ψx x) (Φx x))) ∗ pbor_tok α x ξ Ψx.
  Local Lemma pbor_aux : seal (@pbor_def). Proof. by eexists. Qed.
  Definition pbor {X} := pbor_aux.(unseal) X.
  Local Lemma pbor_unseal : @pbor = @pbor_def. Proof. exact: seal_eq. Qed.
  (** [pobor]: Relaxed prophetic open borrower *)
  Local Definition pobor_def {X} δ α q ξ (Φx : X -d> _) : iProp Σ :=
    ∃ Ψx, □ (∀ x, δ (pborrow_jto (Φx x) (Ψx x))) ∗
      □ (∀ x, δ (pborrow_jto (Ψx x) (Φx x))) ∗ pobor_tok α q ξ Ψx.
  Local Lemma pobor_aux : seal (@pobor_def). Proof. by eexists. Qed.
  Definition pobor {X} := pobor_aux.(unseal) X.
  Local Lemma pobor_unseal : @pobor = @pobor_def. Proof. exact: seal_eq. Qed.
  (** [plend]: Relaxed prophetic lender *)
  Local Definition plend_def {X} δ α xπ (Φx : X -d> _) : iProp Σ :=
    ∃ Y yπ Ψx, □ δ (pborrow_jlto yπ xπ Ψx Φx) ∗ plend_tok (X:=Y) α yπ Ψx.
  Local Lemma plend_aux : seal (@plend_def). Proof. by eexists. Qed.
  Definition plend {X} := plend_aux.(unseal) X.
  Local Lemma plend_unseal : @plend = @plend_def. Proof. exact: seal_eq. Qed.

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance nbor_ne {δ α} : NonExpansive (nbor δ α).
  Proof. rewrite nbor_unseal. solve_proper. Qed.
  #[export] Instance nbor_proper {δ α} : Proper ((≡) ==> (⊣⊢)) (nbor δ α).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance nobor_ne {δ α q} : NonExpansive (nobor δ α q).
  Proof. rewrite nobor_unseal. solve_proper. Qed.
  #[export] Instance nobor_proper {δ α q} : Proper ((≡) ==> (⊣⊢)) (nobor δ α q).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance nlend_ne {δ α} : NonExpansive (nlend δ α).
  Proof. rewrite nlend_unseal. solve_proper. Qed.
  #[export] Instance nlend_proper {δ α} : Proper ((≡) ==> (⊣⊢)) (nlend δ α).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pbor_ne {δ X α x ξ} : NonExpansive (pbor (X:=X) δ α x ξ).
  Proof. rewrite pbor_unseal. solve_proper. Qed.
  #[export] Instance pbor_proper {δ X α x ξ} :
    Proper ((≡) ==> (⊣⊢)) (pbor (X:=X) δ α x ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pobor_ne {δ X α q ξ} : NonExpansive (pobor (X:=X) δ α q ξ).
  Proof. rewrite pobor_unseal. solve_proper. Qed.
  #[export] Instance pobor_proper {δ X α q ξ} :
    Proper ((≡) ==> (⊣⊢)) (pobor (X:=X) δ α q ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance plend_ne {δ X α xπ} : NonExpansive (plend (X:=X) δ α xπ).
  Proof. rewrite plend_unseal. solve_proper. Qed.
  #[export] Instance plend_proper {δ X α xπ} :
    Proper ((≡) ==> (⊣⊢)) (plend (X:=X) δ α xπ).
  Proof. apply ne_proper, _. Qed.
End pborrow_deriv.

(** Notation *)
Notation nbord := (nbor der). Notation nobord := (nobor der).
Notation nlendd := (nlend der).
Notation pbord := (pbor der). Notation pobord := (pobor der).
Notation plendd := (plend der).
Notation plend_bodyi δ := (plend_body ⟦⟧(δ)).
Notation plend_bodyid := (plend_bodyi der).
Notation plend_body_vari δ := (plend_body_var ⟦⟧(δ)).
Notation plend_body_varid := (plend_body_vari der).

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ, !PborrowJudg TY (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : FML $oi Σ).

  (** ** [pborrow_judg_sem]: Semantics of [pborrow_judgty] *)
  Definition pborrow_judg_sem δ (J : pborrow_judgty TY (FML $oi Σ)) : iProp Σ :=
    match J.(untag) with
    | inl PQx => ⟦ PQx.1 ⟧(δ) ==∗ ⟦ PQx.2 ⟧(δ)
    | inr (existT _ ((xπ, yπ)', Φx, Ψx)) =>
        plend_body ⟦ ⟧(δ) xπ Φx ==∗ plend_body ⟦ ⟧(δ) yπ Ψx
    end.
  (** [pborrow_judg_sem] is non-expansive *)
  #[export] Instance pborrow_judg_sem_ne {δ} :
    NonExpansive (pborrow_judg_sem δ).
  Proof.
    move=> ?[?][?]/=[?|]; [solve_proper|]. move=> [?[[??]?]][?[[??]?]][/=?].
    subst=>/=. move=> [/=[/=/leibniz_equiv_iff]]. solve_proper.
  Qed.
  (** [Dsem] over [pborrow_judgty] *)
  #[export] Instance pborrow_jto_dsem
    : Dsem JUDG (pborrow_judgty TY (FML $oi Σ)) (iProp Σ) :=
    DSEM pborrow_judg_sem _.
End pborrow_deriv.

(** ** [PborrowJsem]: Judgment semantics for [pborrow] *)
Notation PborrowJsem TY FML Σ JUDG :=
  (Ejsem (pborrow_judgty TY (FML $oi Σ)) JUDG (iProp Σ)).

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ, !PborrowJudg TY (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !PborrowJsem TY FML Σ JUDG, !Deriv (JUDG:=JUDG) ih δ}.
  Implicit Type (X Y Z : TY) (Px Qx Rx : FML $oi Σ) (δ : JUDG -n> iProp Σ).

  (** ** Conversion *)

  (** Lemmas for [pborrow_jto] *)
  Local Lemma pborrow_jto_refl {Px} : ⊢ δ (pborrow_jto Px Px).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite sem_ejudg.
    by iIntros "$".
  Qed.
  Local Lemma pborrow_jto_trans {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    δ (pborrow_jto Qx Rx) -∗ δ (pborrow_jto Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !sem_ejudg.
    iIntros "QR Px". iMod ("big" with "[//] [//] [//] Px"). by iApply "QR".
  Qed.
  Local Lemma pborrow_jto_trans' {Px Qx Rx} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ Qx ⟧(δ') ==∗ ⟦ Rx ⟧(δ'))
      -∗ δ (pborrow_jto Px Qx) -∗ δ (pborrow_jto Px Rx).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????). rewrite !sem_ejudg.
    iIntros "PQ Px". iMod ("PQ" with "Px"). by iApply "big".
  Qed.
  Local Lemma der_pborrow_jto {Px Qx} :
    der (pborrow_jto Px Qx) ⊢ (⟦ Px ⟧ ==∗ ⟦ Qx ⟧).
  Proof. by rewrite der_sound sem_ejudg. Qed.

  (** Lemmas for [pborrow_jlto] *)
  Local Lemma pborrow_jlto_refl {X xπ Φx} :
    ⊢ δ (pborrow_jlto (X:=X) xπ xπ Φx Φx).
  Proof.
    iApply Deriv_factor. iIntros (????). rewrite sem_ejudg.
    by iIntros "$".
  Qed.
  Local Lemma pborrow_jlto_trans {X Y Z xπ yπ zπ Φx Ψx Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φx ==∗ plend_body ⟦ ⟧(δ') yπ Ψx) -∗
    δ (pborrow_jlto (X:=Y) (Y:=Z) yπ zπ Ψx Ω) -∗
    δ (pborrow_jlto (X:=X) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !sem_ejudg. iIntros "ΨΩ Φx".
    iMod ("big" with "[//] [//] [//] Φx"). by iApply "ΨΩ".
  Qed.
  Local Lemma pborrow_jlto_trans' {X Y Z xπ yπ zπ Φx Ψx Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') yπ Ψx ==∗ plend_body ⟦ ⟧(δ') zπ Ω) -∗
    δ (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) -∗
    δ (pborrow_jlto (Y:=Z) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !sem_ejudg. iIntros "ΦΨ Φx". iMod ("ΦΨ" with "Φx").
    by iApply "big".
  Qed.
  Local Lemma der_pborrow_jlto {X Y xπ yπ Φx Ψx} :
    der (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) ⊢
      (plend_bodyid xπ Φx ==∗ plend_bodyid yπ Ψx).
  Proof. by rewrite der_sound sem_ejudg. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma nbor_to {α Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    nbor δ α Px -∗ nbor δ α Qx.
  Proof.
    rewrite nbor_unseal. iIntros "#PQ #QP (%Rx & #PR & #RP & $)".
    iSplit; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma nobor_to {α q Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Qx ⟧(δ') ==∗ ⟦ Px ⟧(δ')) -∗
    nobor δ α q Px -∗ nobor δ α q Qx.
  Proof.
    rewrite nobor_unseal. iIntros "#PQ #QP (%Rx & #PR & #RP & $)".
    iSplit; [iApply (pborrow_jto_trans with "QP PR")|
      iApply (pborrow_jto_trans' with "PQ RP")].
  Qed.
  Lemma nlend_to {α Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ==∗ ⟦ Qx ⟧(δ')) -∗
    nlend δ α Px -∗ nlend δ α Qx.
  Proof.
    rewrite nlend_unseal. iIntros "#PQ (%Rx & #RP & $)".
    iApply (pborrow_jto_trans' with "PQ RP").
  Qed.
  Lemma pbor_to {X α x ξ Φx Ψx} :
    □ (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx x' ⟧(δ') ==∗ ⟦ Ψx x' ⟧(δ')) -∗
    □ (∀ x' δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx x' ⟧(δ') ==∗ ⟦ Φx x' ⟧(δ')) -∗
    pbor (X:=X) δ α x ξ Φx -∗ pbor δ α x ξ Ψx.
  Proof.
    rewrite pbor_unseal. iIntros "#ΦΨ #ΨΦ (%Ω & #ΦΩ & #ΩΦ & $)".
    iSplit; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma pobor_to {X α q ξ Φx Ψx} :
    □ (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx x ⟧(δ') ==∗ ⟦ Ψx x ⟧(δ')) -∗
    □ (∀ x δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx x ⟧(δ') ==∗ ⟦ Φx x ⟧(δ')) -∗
    pobor (X:=X) δ α q ξ Φx -∗ pobor δ α q ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "#ΦΨ #ΨΦ (%Ω & #ΦΩ & #ΩΦ & $)".
    iSplit; iIntros (?); [iApply (pborrow_jto_trans with "ΨΦ ΦΩ")|
      iApply (pborrow_jto_trans' with "ΦΨ ΩΦ")].
  Qed.
  Lemma plend_to {X Y α xπ yπ Φx Ψx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      plend_body ⟦ ⟧(δ') xπ Φx ==∗ plend_body ⟦ ⟧(δ') yπ Ψx) -∗
    plend (X:=X) δ α xπ Φx -∗ plend (X:=Y) δ α yπ Ψx.
  Proof.
    rewrite plend_unseal. iIntros "#ΦΨ (%Z & %zπ & %Ω & #ΩΦ & $)".
    iApply (pborrow_jlto_trans' with "ΦΨ ΩΦ").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma nbor_lft {α β Px} : β ⊑□ α -∗ nbor δ α Px -∗ nbor δ β Px.
  Proof.
    rewrite nbor_unseal. iIntros "⊑ (% & #? & #? & b)".
    iDestruct (nbor_tok_lft with "⊑ b") as "$". by iSplit.
  Qed.
  Lemma nobor_lft {α β q r Px} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ nobor δ α q Px -∗ nobor δ β r Px.
  Proof.
    rewrite nobor_unseal. iIntros "⊑ → (% & #? & #? & o)".
    iDestruct (nobor_tok_lft with "⊑ → o") as "$". by iSplit.
  Qed.
  Lemma nlend_lft {α β Px} : α ⊑□ β -∗ nlend δ α Px -∗ nlend δ β Px.
  Proof.
    rewrite nlend_unseal. iIntros "⊑ (% & #? & l)".
    by iDestruct (nlend_tok_lft with "⊑ l") as "$".
  Qed.
  Lemma pbor_lft {X α β x ξ Φx} :
    β ⊑□ α -∗ pbor (X:=X) δ α x ξ Φx -∗ pbor δ β x ξ Φx.
  Proof.
    rewrite pbor_unseal. iIntros "⊑ (% & #? & #? & b)".
    iDestruct (pbor_tok_lft with "⊑ b") as "$". by iSplit.
  Qed.
  Lemma pobor_lft {X α β q r ξ Φx} :
    β ⊑□ α -∗ (q.[α] -∗ r.[β]) -∗ pobor (X:=X) δ α q ξ Φx -∗ pobor δ β r ξ Φx.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ → (% & ? & ? & o)".
    iDestruct (pobor_tok_lft with "⊑ → o") as "$". by iSplit.
  Qed.
  Lemma plend_lft {X α β xπ Φx} :
    α ⊑□ β -∗ plend (X:=X) δ α xπ Φx -∗ plend δ β xπ Φx.
  Proof.
    rewrite plend_unseal. iIntros "⊑ (% & % & % & #? & l)".
    by iDestruct (plend_tok_lft with "⊑ l") as "$".
  Qed.

  (** Turn from tokens *)
  Lemma nbor_tok_nbor {α Px} : nbor_tok α Px ⊢ nbor δ α Px.
  Proof.
    rewrite nbor_unseal. iIntros "$". iSplit; iApply pborrow_jto_refl.
  Qed.
  Lemma nobor_tok_nobor {α q Px} : nobor_tok α q Px ⊢ nobor δ α q Px.
  Proof.
    rewrite nobor_unseal. iIntros "$". iSplit; iApply pborrow_jto_refl.
  Qed.
  Lemma nlend_tok_nlend {α Px} : nlend_tok α Px ⊢ nlend δ α Px.
  Proof. rewrite nlend_unseal. iIntros "$". iApply pborrow_jto_refl. Qed.
  Lemma pbor_tok_pbor {X α x ξ Φx} :
    pbor_tok (X:=X) α x ξ Φx ⊢ pbor δ α x ξ Φx.
  Proof.
    rewrite pbor_unseal. iIntros "$".
    iSplit; iIntros "!> %"; iApply pborrow_jto_refl.
  Qed.
  Lemma pobor_tok_pobor {X α q ξ Φx} :
    pobor_tok (X:=X) α q ξ Φx ⊢ pobor δ α q ξ Φx.
  Proof.
    rewrite pobor_unseal. iIntros "$".
    iSplit; iIntros "!> %"; iApply pborrow_jto_refl.
  Qed.
  Lemma plend_tok_plend {X α xπ Φx} :
    plend_tok (X:=X) α xπ Φx ⊢ plend δ α xπ Φx.
  Proof. rewrite plend_unseal. iIntros "$". iApply pborrow_jlto_refl. Qed.

  (** Fake a borrower *)
  Lemma nbor_fake {α} Px : [†α] ⊢ nbor δ α Px.
  Proof. by rewrite nbor_tok_fake nbor_tok_nbor. Qed.

  Context `{!GenUpd (PROP:=iProp Σ) M, !AbsorbBUpd M}.

  (** ** Rules that work under [Deriv ih δ] *)

  (** Create borrowers and lenders *)
  Lemma nbor_nlend_new_list α Pxl Qxl :
    ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗
    ([†α] -∗ ([∗ list] Px ∈ Pxl, ⟦ Px ⟧(δ)) -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧(δ)))
      =[pborrow_wsat M ⟦⟧(δ)]=∗
      ([∗ list] Px ∈ Pxl, nbor δ α Px) ∗ [∗ list] Qx ∈ Qxl, nlend δ α Qx.
  Proof.
    setoid_rewrite <-nbor_tok_nbor. setoid_rewrite <-nlend_tok_nlend.
    exact: nbor_nlend_tok_new_list.
  Qed.
  (** Simply create a borrower and a lender *)
  Lemma nbor_nlend_new α Px :
    ⟦ Px ⟧(δ) =[pborrow_wsat M ⟦⟧(δ)]=∗ nbor δ α Px ∗ nlend δ α Px.
  Proof.
    rewrite -nbor_tok_nbor -nlend_tok_nlend. exact: nbor_nlend_tok_new.
  Qed.

  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_new_list α Xl (xΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦxl := plist_zip ξl xΦxl in
      ([∗ plist] '(x, Φx)' ∈ xΦxl, ⟦ Φx x ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, plend_body_vari δ ξ Φx) -∗ M
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_bodyi δ yπ Ψx))
        =[pborrow_wsat M ⟦⟧(δ)]=∗
        ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, pbor δ α x ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend δ α yπ Ψx).
  Proof.
    iMod (pbor_plend_tok_new_list (M:=M) (sm:=⟦⟧(_))) as (?) "big". iModIntro.
    iExists _. iIntros (??). setoid_rewrite <-pbor_tok_pbor.
    setoid_rewrite <-plend_tok_plend. iApply "big".
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_new α X (x : X) Φx :
    ⟦ Φx x ⟧(δ) =[pborrow_wsat M ⟦⟧(δ)]=∗ ∃ ξ,
      pbor δ α x ξ Φx ∗ plend δ α (λ π, π ξ) Φx.
  Proof.
    setoid_rewrite <-pbor_tok_pbor. setoid_rewrite <-plend_tok_plend.
    exact: pbor_plend_tok_new.
  Qed.
End pborrow_deriv.

Section pborrow_deriv.
  Context `{!pborrowGS TY FML Σ, !PborrowJudg TY (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !PborrowJsem TY FML Σ JUDG, !GenUpd (PROP:=iProp Σ) M, !AbsorbBUpd M}.
  Implicit Type (X Y : TY) (Px Qx : FML $oi Σ).

  (** ** On non-prophetic borrowing *)

  (** Split a lender *)
  Lemma nlendd_split {α Px} Qxl :
    nlendd α Px -∗ (⟦ Px ⟧ -∗ M ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧))
      =[pborrow_wsat M ⟦⟧]=∗ [∗ list] Qx ∈ Qxl, nlendd α Qx.
  Proof.
    rewrite {1}nlend_unseal. setoid_rewrite <-nlend_tok_nlend.
    iIntros "(%Rx & #RP & l) →Ql".
    iApply (nlend_tok_split (M:=M) with "l [RP →Ql]"). iIntros "Rx".
    iMod (der_pborrow_jto with "RP Rx"). by iApply "→Ql".
  Qed.

  (** Retrive from [nlendd] *)
  Lemma nlendd_retrieve {α Px} :
    [†α] -∗ nlendd α Px -∗ modw M (pborrow_wsat M ⟦⟧) ⟦ Px ⟧.
  Proof.
    rewrite nlend_unseal. iIntros "† (%Qx & #QP & l)".
    iMod (nlend_tok_retrieve (M:=M) with "† l") as "Qx".
    iMod (der_pborrow_jto with "QP Qx") as "$". by iIntros.
  Qed.

  (** Open a borrower *)
  Lemma nbord_open {α q Px} :
    q.[α] -∗ nbord α Px -∗ modw M (pborrow_wsat M ⟦⟧) (nobord α q Px ∗ ⟦ Px ⟧).
  Proof.
    rewrite nbor_unseal nobor_unseal. iIntros "α (%Qx & $ & #QP & b)".
    iMod (nbor_tok_open (M:=M) with "α b") as "[$ Qx]".
    iMod (der_pborrow_jto with "QP Qx") as "$". by iIntros "$".
  Qed.

  (** Lemma for [nobord_merge_subdiv] *)
  Local Lemma from_sincl_nobords {αqPxl β} :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ nobord α q Px) ⊢
    ∃ αqRxl,
      □ (([∗ list] '(_, _, Px)' ∈ αqPxl, ⟦ Px ⟧) ==∗
        [∗ list] '(_, _, Rx)' ∈ αqRxl, ⟦ Rx ⟧) ∗
      □ (([∗ list] '(α, q, Rx)' ∈ αqRxl, q.[α] ∗ ([†β] -∗ nbor_tok α Rx)) -∗
        [∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ nbord α Px)) ∗
      ([∗ list] '(α, q, Rx)' ∈ αqRxl, β ⊑□ α ∗ nobor_tok α q Rx).
  Proof.
    rewrite nobor_unseal /=. elim: αqPxl=>/=.
    { iIntros. iExists []=>/=. do 2 (iSplit; [done|]). by iIntros. }
    iIntros ([α[q Px]] αqPxl ->).
    iIntros "[[⊑(%Rx & #PR & #RP & o)] (%αqRxl & #→Rxl & #→αbdl & ol)]".
    iExists ((α, q, Rx)' :: αqRxl)=>/=. iFrame "⊑ o ol". iSplit.
    - iIntros "!> [Px Pxl]". iMod ("→Rxl" with "Pxl") as "$".
      iApply (der_pborrow_jto with "PR Px").
    - iIntros "!> [[$ →b]αbl]". iDestruct ("→αbdl" with "αbl") as "$".
      iIntros "†". rewrite nbor_unseal. iDestruct ("→b" with "†") as "$".
      by iSplit.
  Qed.
  (** Merge and subdivide/reborrow borrowers *)
  Lemma nobord_merge_subdiv αqPxl Qxl β :
    ([∗ list] '(α, q, Px)' ∈ αqPxl, β ⊑□ α ∗ nobord α q Px) -∗
    ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M
      ([∗ list] '(_, _, Px)' ∈ αqPxl, ⟦ Px ⟧)) =[pborrow_wsat M ⟦⟧]=∗
      ([∗ list] '(α, q, Px)' ∈ αqPxl, q.[α] ∗ ([†β] -∗ nbord α Px)) ∗
      ([∗ list] Qx ∈ Qxl, nbord β Qx).
  Proof.
    iIntros "big Qxl →Pxl". rewrite from_sincl_nobords /=.
    iDestruct "big" as (αqRxl) "(#→Rxl & #→αbdl & ol)".
    setoid_rewrite <-(nbor_tok_nbor (α:=β)).
    iMod (nobor_tok_merge_subdiv (M:=M) with "ol Qxl [→Pxl]") as "[αbl $]".
    - iIntros "† Qxl". iMod ("→Pxl" with "† Qxl") as "Pxl".
      by iMod ("→Rxl" with "Pxl").
    - iModIntro. by iApply "→αbdl".
  Qed.
  (** Subdivide/reborrow a borrower *)
  Lemma nobord_subdiv {α q Px} Qxl β :
    β ⊑□ α -∗ nobord α q Px -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗
    ([†β] -∗ ([∗ list] Qx ∈ Qxl, ⟦ Qx ⟧) -∗ M ⟦ Px ⟧) =[pborrow_wsat M ⟦⟧]=∗
      q.[α] ∗ ([†β] -∗ nbord α Px) ∗ ([∗ list] Qx ∈ Qxl, nbord β Qx).
  Proof.
    iIntros "⊑ o Qxl →Px".
    iMod (nobord_merge_subdiv [(_,_,_)'] with "[⊑ o] Qxl [→Px]")
      as "[[[$$]_]$]"=>/=; by [iFrame|rewrite bi.sep_emp|].
  Qed.

  (** Reborrow a borrower *)
  Lemma nobord_reborrow {α q Px} β :
    β ⊑□ α -∗ nobord α q Px -∗ ⟦ Px ⟧ =[pborrow_wsat M ⟦⟧]=∗
      q.[α] ∗ ([†β] -∗ nbord α Px) ∗ nbord β Px.
  Proof.
    iIntros "⊑ o Px".
    iMod (nobord_subdiv [Px] with "⊑ o [Px] []") as "($ & $ & $ & _)"=>/=;
      by [iFrame|iIntros "_ [$ _]"|].
  Qed.
  Lemma nbord_reborrow {α q Px} β :
    β ⊑□ α -∗ q.[α] -∗ nbord α Px -∗ modw M (pborrow_wsat M ⟦⟧)
      (q.[α] ∗ ([†β] -∗ nbord α Px) ∗ nbord β Px).
  Proof.
    iIntros "⊑ α b". iMod (nbord_open with "α b") as "[o Px]".
    by iMod (nobord_reborrow with "⊑ o Px").
  Qed.
  (** Simply close a borrower *)
  Lemma nobord_close {α q Px} :
    nobord α q Px -∗ ⟦ Px ⟧ =[pborrow_wsat M ⟦⟧]=∗ q.[α] ∗ nbord α Px.
  Proof.
    iIntros "o Px".
    iMod (nobord_reborrow with "[] o Px") as "($ & _ & $)";
      by [iApply lft_sincl_refl|].
  Qed.

  (** ** On prophetic borrowing *)

  (** Split a prophetic lender *)
  Lemma plendd_split {X α xπ} {Φx : X → _} Yl
    (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl) :
    plendd α xπ Φx -∗
    (plend_bodyid xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend_bodyid yπ Ψx))
      =[pborrow_wsat M ⟦⟧]=∗ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plendd α yπ Ψx.
  Proof.
    rewrite {1}plend_unseal. iIntros "(%Z & %zπ & %Ω & ΩΦ & l) →Ψxl".
    setoid_rewrite <-plend_tok_plend.
    iApply (plend_tok_split (M:=M) with "l [ΩΦ →Ψxl]"). iIntros "lb".
    iMod (der_pborrow_jlto with "ΩΦ lb") as "?". by iApply "→Ψxl".
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plendd_retrieve {X α xπ} {Φx : X → _} :
    [†α] -∗ plendd α xπ Φx -∗ modw M (pborrow_wsat M ⟦⟧) (plend_bodyid xπ Φx).
  Proof.
    rewrite {1}plend_unseal. iIntros "† (%Y & %yπ & %Ψx & ΨΦ & l)".
    iMod (plend_tok_retrieve (M:=M) with "† l") as "lb".
    iMod (der_pborrow_jlto with "ΨΦ lb") as "$". by iIntros.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pbord_open {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (pborrow_wsat M ⟦⟧)
      (pobord α q ξ Φx ∗ ⟦ Φx x ⟧).
  Proof.
    rewrite pbor_unseal pobor_unseal. iIntros "α (% & $ & #ΨΦ & b)".
    iMod (pbor_tok_open (M:=M) with "α b") as "[$ Ψx]".
    iMod (der_pborrow_jto with "ΨΦ Ψx") as "$". by iIntros "$".
  Qed.

  (** Lemma for [pobord_merge_subdiv] *)
  Local Lemma from_sincl_pobords {Xl A β}
    {αqξΦxfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl} :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦxfl, β ⊑□ α ∗ pobord α q ξ Φx) ⊢
      ∃ αqξΩfl : plist (λ X, _ *' _ *' _ *' _ *' (A → X)) Xl,
      ⌜([∗ plist] '(α, q, _)' ∈ αqξΦxfl, q.[α]) ⊣⊢
        [∗ plist] '(α, q, _)' ∈ αqξΩfl, q.[α]⌝ ∗
      ⌜∀ aπ,
        ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
          ⟨π, π (Aprvar _ ξ) = f (aπ π)⟩) ⊣⊢
        [∗ plist] '(_, _, ξ, _, f)' ∈ αqξΩfl, ⟨π, π (Aprvar _ ξ) = f (aπ π)⟩⌝ ∗
      ([∗ plist] '(α, q, ξ, Ω, _)' ∈ αqξΩfl, β ⊑□ α ∗ pobor_tok α q ξ Ω) ∗
      (∀ a, ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦxfl, ⟦ Φx (f a) ⟧) ==∗
        [∗ plist] '(_, _, _, Ω, f)' ∈ αqξΩfl, ⟦ Ω (f a) ⟧).
  Proof.
    rewrite pobor_unseal. elim: Xl αqξΦxfl=>/=.
    { iIntros. iExists (). do 2 (iSplit; [done|]). by iIntros. }
    move=> X Xl IH [[α[q[ξ[Φx f]]]] αqξΦxfl]. rewrite IH.
    iIntros "[[⊑ (%Ω & #ΦΩ & _ & o)] [%αqξΩfl[%[%[ol →']]]]]".
    iExists ((α, q, ξ, Ω, f)', αqξΩfl)'. iFrame "⊑ o ol".
    do 2 (iSplit; [iPureIntro=> >; by f_equiv|]). iIntros (a) "[Φx Φxl]".
    iMod (der_pborrow_jto with "ΦΩ Φx") as "$". by iApply "→'".
  Qed.
  (** Merge and subdivide prophetic borrowers *)
  Lemma pobord_merge_subdiv Xl Yl
    (αqξΦxfl : plist (λ X, _ *' _ *' _ *' _ *' (_ → X)) Xl) (yΨxl : plist _ Yl)
    Rxl β :
    ([∗ plist] '(α, q, ξ, Φx, _)' ∈ αqξΦxfl, β ⊑□ α ∗ pobord α q ξ Φx) -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨxl, ⟦ Ψx y ⟧) -∗ ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧) -∗
      ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗ M
        ([∗ plist] '(_, _, _, Φx, f)' ∈ αqξΦxfl, ⟦ Φx (f yl') ⟧))
      =[pborrow_wsat M ⟦⟧]=∗ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦxfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbord β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, nbord β Rx.
  Proof.
    rewrite from_sincl_pobords /=.
    iIntros "(% & %eq & %eq' & ol & →) Ψxl Rxl →Φxl". setoid_rewrite eq.
    setoid_rewrite eq'. setoid_rewrite <-pbor_tok_pbor.
    setoid_rewrite <-nbor_tok_nbor.
    iApply (pobor_tok_merge_subdiv (M:=M) with "ol Ψxl Rxl").
    iIntros "% † Ψxl Rxl". iMod ("→Φxl" with "† Ψxl Rxl") as "Φxl".
    by iMod ("→" with "Φxl").
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobord_subdiv {X α q ξ Φx} Yl (f : _ → X) (yΨxl : plist _ Yl) Rxl β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨxl, ⟦ Ψx y ⟧) -∗ ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧) -∗
      ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗ M ⟦ Φx (f yl') ⟧) =[pborrow_wsat M ⟦⟧]=∗
      ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbord β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, nbord β Rx.
  Proof.
    iIntros "⊑ o Ψxl Rxl →Φx".
    iMod (pobord_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψxl Rxl [→Φx]") as (?) "/=[[$ _][[$ _]$]]"; [|done].
    iIntros (?). by rewrite /= bi.sep_emp.
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobord_resolve {X α q ξ Φx} (x : X) :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[pborrow_wsat M ⟦⟧]=∗
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbord α (Φx x).
  Proof.
    iIntros "o Φx".
    iMod (pobord_subdiv [] (λ _, x) () [Φx x] with "[] o [//] [Φx] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pbord_resolve {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (pborrow_wsat M ⟦⟧)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ nbord α (Φx x)).
  Proof.
    iIntros "α b". iMod (pbord_open with "α b") as "[o Φx]".
    iMod (pobord_resolve with "o Φx") as "$". by iIntros.
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobord_nsubdiv {X α q ξ Φx} Ψx (x : X) β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗ ⟦ Ψx x ⟧ -∗
    (∀ x', [†β] -∗ ⟦ Ψx x' ⟧ -∗ M ⟦ Φx x' ⟧) =[pborrow_wsat M ⟦⟧]=∗
      q.[α] ∗ pbord β x ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ (%Ω & #ΦΩ & _ & o) Ψx →Φx".
    rewrite -pbor_tok_pbor.
    iApply (pobor_tok_nsubdiv (M:=M) with "⊑ o Ψx [ΦΩ →Φx]").
    iIntros "% † Ψx". iMod ("→Φx" with "† Ψx") as "Φx".
    by iMod (der_pborrow_jto with "ΦΩ Φx").
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobord_close {X α q ξ Φx} (x : X) :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[pborrow_wsat M ⟦⟧]=∗ q.[α] ∗ pbord α x ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobord_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobord_pobord_reborrow {X Y α q ξ Φx β r η Ψx} y (f : X → Y) :
    β ⊑□ α -∗ pobord β q ξ Φx -∗ pobord α r η Ψx -∗ ⟦ Ψx y ⟧ -∗
    (∀ y', [†β] -∗ pbord α y' η Ψx -∗ M ⟦ Φx (f y') ⟧) -∗
      modw M (pborrow_wsat M ⟦⟧) (∃ η',
      q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pbord β y η' Ψx).
  Proof.
    rewrite pobor_unseal pbor_unseal.
    iIntros "⊑ (%Φx' & #ΦΦ' & #Φ'Φ & o) (%Ψx' & #ΨΨ' & #Ψ'Ψ & o') Ψx →Φx".
    iMod (der_pborrow_jto with "ΨΨ' Ψx") as "Ψx'".
    iMod (pobor_pobor_tok_reborrow (M:=M)
      with "⊑ o o' Ψx' [→Φx]") as (?) "($ & $ & obs & b)"; last first.
    { iIntros "$ !>". iFrame "obs b". by iSplit. }
    iIntros "% † b". iMod ("→Φx" with "† [$b]") as "Φx"; [by iSplit|].
    by iMod (der_pborrow_jto with "ΦΦ' Φx").
  Qed.
  Lemma pobord_pbord_reborrow {X Y α q ξ Φx β r y η Ψx} (f : X → Y) :
    β ⊑□ α -∗ pobord β q ξ Φx -∗ r.[α] -∗ pbord α y η Ψx -∗
    (∀ y', [†β] -∗ pbord α y' η Ψx -∗ M ⟦ Φx (f y') ⟧) -∗
      modw M (pborrow_wsat M ⟦⟧) (∃ η',
        q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pbord β y η' Ψx).
  Proof.
    iIntros "⊑ o r b →Φx". iMod (pbord_open with "r b") as "[o' Ψx]".
    iApply (pobord_pobord_reborrow with "⊑ o o' Ψx →Φx").
  Qed.
End pborrow_deriv.
