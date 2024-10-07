(** * Prophetic borrowing machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export pborrow.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation FunNPNotation iPropAppNotation ModwNotation
  LftNotation ProphNotation DsemNotation.

Implicit Type (TY : synty) (CON : cifcon) (Σ : gFunctors) (FM : ofe).

(** ** [pborrow_judgty]: Judgment type for [pborrow] *)
Variant pborrow_judg_id TY CON Σ := .
Definition pborrow_judgty TY CON Σ : ofe := tagged (pborrow_judg_id TY CON Σ)
  ((** Basic conversion *) cif CON Σ * cif CON Σ +
  (** Conversion judgment for [lend_body] *)
    @sigT (TY *' TY) (λ '(X, Y)',
      leibnizO (clair TY X *' clair TY Y) *
      (X -d> cif CON Σ) * (Y -d> cif CON Σ)))%type.

(** ** [PborrowJudg]: Judgment structure for [pborrow] *)
Notation PborrowJudg TY CON Σ JUDG := (Ejudg (pborrow_judgty TY CON Σ) JUDG).

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG TY Σ,
    pborrow_judg : !PborrowJudg TY CON Σ JUDG}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : cif CON Σ) (X Y : TY).

  (** Judgments *)
  Local Definition pborrow_jto Px Qx : JUDG :=
    pborrow_judg (Tagged (inl (Px, Qx))).
  Local Definition pborrow_jlto {X Y} (xπ : clair TY X) (yπ : clair TY Y)
    (Φx : X -d> cif CON Σ) (Ψx : Y -d> cif CON Σ) : JUDG :=
    pborrow_judg (Tagged (inr (existT (X, Y)' ((xπ, yπ)', Φx, Ψx)))).
  #[export] Instance pborrow_jto_ne : NonExpansive2 pborrow_jto.
  Proof. solve_proper. Qed.
  #[export] Instance pborrow_jlto_ne {X Y xπ yπ} :
    NonExpansive2 (@pborrow_jlto X Y xπ yπ).
  Proof.
    unfold pborrow_jlto=> ???????. f_equiv. apply inr_ne. apply: existT_ne=>/=.
    split; [split|]; solve_proper.
  Qed.

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
Notation pbord := (pbor der). Notation pobord := (pobor der).
Notation plendd := (plend der).

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG TY Σ,
    !PborrowJudg TY CON Σ JUDG, !Jsem JUDG (iProp Σ), !SemCifcon JUDG CON Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : cif CON Σ).

  (** ** [pborrow_judg_sem]: Semantics of [pborrow_judgty] *)
  Definition pborrow_judg_sem δ (J : pborrow_judgty TY CON Σ) : iProp Σ :=
    match J.(untag) with
    | inl PQx => ⟦ PQx.1 ⟧(δ) ==∗ ⟦ PQx.2 ⟧(δ)
    | inr (existT _ ((xπ, yπ)', Φx, Ψx)) => xplend δ xπ Φx ==∗ xplend δ yπ Ψx
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
    : Dsem JUDG (pborrow_judgty TY CON Σ) (iProp Σ) :=
    DSEM pborrow_judg_sem _.
End pborrow_deriv.

(** ** [PborrowJsem]: Judgment semantics for [pborrow] *)
Notation PborrowJsem TY CON Σ JUDG :=
  (Ejsem (pborrow_judgty TY CON Σ) JUDG (iProp Σ)).

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG TY Σ,
    !PborrowJudg TY CON Σ JUDG, !Jsem JUDG (iProp Σ), !SemCifcon JUDG CON Σ,
    !PborrowJsem TY CON Σ JUDG, !Deriv (JUDG:=JUDG) ih δ}.
  Implicit Type (X Y Z : TY) (Px Qx Rx : cif CON Σ) (δ : JUDG -n> iProp Σ).

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
      xplend δ' xπ Φx ==∗ xplend δ' yπ Ψx) -∗
    δ (pborrow_jlto (X:=Y) (Y:=Z) yπ zπ Ψx Ω) -∗
    δ (pborrow_jlto (X:=X) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !sem_ejudg. iIntros "ΨΩ Φx".
    iMod ("big" with "[//] [//] [//] Φx"). by iApply "ΨΩ".
  Qed.
  Local Lemma pborrow_jlto_trans' {X Y Z xπ yπ zπ Φx Ψx Ω} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      xplend δ' yπ Ψx ==∗ xplend δ' zπ Ω) -∗
    δ (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) -∗
    δ (pborrow_jlto (Y:=Z) xπ zπ Φx Ω).
  Proof.
    iIntros "big". iApply Deriv_map. iIntros (????).
    rewrite !sem_ejudg. iIntros "ΦΨ Φx". iMod ("ΦΨ" with "Φx").
    by iApply "big".
  Qed.
  Local Lemma der_pborrow_jlto {X Y xπ yπ Φx Ψx} :
    der (pborrow_jlto (X:=X) (Y:=Y) xπ yπ Φx Ψx) ⊢
      (xplendd xπ Φx ==∗ xplendd yπ Ψx).
  Proof. by rewrite der_sound sem_ejudg. Qed.

  (** Convert the body of borrower and lender propositions *)
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
      xplend δ' xπ Φx ==∗ xplend δ' yπ Ψx) -∗
    plend (X:=X) δ α xπ Φx -∗ plend (X:=Y) δ α yπ Ψx.
  Proof.
    rewrite plend_unseal. iIntros "#ΦΨ (%Z & %zπ & %Ω & #ΩΦ & $)".
    iApply (pborrow_jlto_trans' with "ΦΨ ΩΦ").
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
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

  Context `{!@ModUpd (iProp Σ) M, !ModBUpd M, !ModExcept0 M}.

  (** ** Rules that work under [Deriv ih δ] *)

  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_new_list α Xl (xΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl),
      let ξxΦxl := plist_zip ξl xΦxl in
      ([∗ plist] '(x, Φx)' ∈ xΦxl, ⟦ Φx x ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, xplend_var δ ξ Φx) -∗ M
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
        =[borrow_wsat M ⟦⟧(δ)]=∗◇
        ([∗ plist] '(ξ, x, Φx)' ∈ ξxΦxl, pbor δ α x ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend δ α yπ Ψx).
  Proof.
    simpl. setoid_rewrite <-pbor_tok_pbor. setoid_rewrite <-plend_tok_plend.
    exact: pbor_plend_tok_new_list.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_new α X (x : X) Φx :
    ⟦ Φx x ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗◇ ∃ ξ,
      pbor δ α x ξ Φx ∗ plend δ α (λ π, π ξ) Φx.
  Proof.
    setoid_rewrite <-pbor_tok_pbor. setoid_rewrite <-plend_tok_plend.
    exact: pbor_plend_tok_new.
  Qed.
End pborrow_deriv.

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG TY Σ,
    !PborrowJudg TY CON Σ JUDG, !Jsem JUDG (iProp Σ), !SemCifcon JUDG CON Σ,
    !PborrowJsem TY CON Σ JUDG,
    !@ModUpd (iProp Σ) M, !ModBUpd M, !ModExcept0 M}.
  Implicit Type (X Y : TY) (Px Qx : cif CON Σ).

  (** Split a prophetic lender *)
  Lemma plendd_split {X α xπ} {Φx : X → _} Yl
    (yπΨxl : plist (λ Y, _ *' (Y → _)) Yl) :
    plendd α xπ Φx -∗
    (xplendd xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplendd yπ Ψx))
      =[borrow_wsat M ⟦⟧]=∗◇ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plendd α yπ Ψx.
  Proof.
    rewrite {1}plend_unseal. iIntros "(%Z & %zπ & %Ω & ΩΦ & l) →Ψxl".
    setoid_rewrite <-plend_tok_plend.
    iApply (plend_tok_split (M:=M) with "l [ΩΦ →Ψxl]"). iIntros "lb".
    iMod (der_pborrow_jlto with "ΩΦ lb") as "?". by iApply "→Ψxl".
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plendd_retrieve {X α xπ} {Φx : X → _} :
    [†α] -∗ plendd α xπ Φx -∗ modw M (borrow_wsat M ⟦⟧) (xplendd xπ Φx).
  Proof.
    rewrite {1}plend_unseal. iIntros "† (%Y & %yπ & %Ψx & ΨΦ & l)".
    iMod (plend_tok_retrieve (M:=M) with "† l") as "lb".
    iMod (der_pborrow_jlto with "ΨΦ lb") as "$". by iIntros.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pbord_open {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (borrow_wsat M ⟦⟧)
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
      =[borrow_wsat M ⟦⟧]=∗◇ ∃ ηl,
      ([∗ plist] '(α, q, _)' ∈ αqξΦxfl, q.[α]) ∗
      ([∗ plist] '(_, _, ξ, _, f)' ∈ αqξΦxfl,
        ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩) ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbord β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, bor_tok β Rx.
  Proof.
    rewrite from_sincl_pobords /=.
    iIntros "(% & %eq & %eq' & ol & →) Ψxl Rxl →Φxl". setoid_rewrite eq.
    setoid_rewrite eq'. setoid_rewrite <-pbor_tok_pbor.
    iApply (pobor_tok_merge_subdiv (M:=M) with "ol Ψxl Rxl").
    iIntros "% † Ψxl Rxl". iMod ("→Φxl" with "† Ψxl Rxl") as "Φxl".
    by iMod ("→" with "Φxl").
  Qed.
  (** Subdivide a prophetic borrower *)
  Lemma pobord_subdiv {X α q ξ Φx} Yl (f : _ → X) (yΨxl : plist _ Yl) Rxl β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗
    ([∗ plist] '(y, Ψx)' ∈ yΨxl, ⟦ Ψx y ⟧) -∗ ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗
    (∀ yl', [†β] -∗ ([∗ plist] '(y', _, Ψx)' ∈ plist_zip yl' yΨxl, ⟦ Ψx y' ⟧) -∗
      ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗ M ⟦ Φx (f yl') ⟧) =[borrow_wsat M ⟦⟧]=∗◇
      ∃ ηl,
      q.[α] ∗ ⟨π, π (Aprvar _ ξ) = f (app_plist_prvar π ηl)⟩ ∗
      ([∗ plist] '(η, y, Ψx)' ∈ plist_zip ηl yΨxl, pbord β y η Ψx) ∗
      [∗ list] Rx ∈ Rxl, bor_tok β Rx.
  Proof.
    iIntros "⊑ o Ψxl Rxl →Φx".
    iMod (pobord_merge_subdiv [_] _ ((_,_,_,_,_)',())'
      with "[$⊑ $o //] Ψxl Rxl [→Φx]") as (?) "/=[[$ _][[$ _]$]]"; [|done].
    iIntros (?). by rewrite /= bi.sep_emp.
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobord_resolve {X α q ξ Φx} (x : X) :
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[borrow_wsat M ⟦⟧]=∗◇
      q.[α] ∗ ⟨π, π ξ = x⟩ ∗ bor_tok α (Φx x).
  Proof.
    iIntros "o Φx".
    iMod (pobord_subdiv [] (λ _, x) () [Φx x] with "[] o [//] [Φx] []")
      as (?) "[$[$[_[$ _]]]]"=>/=;
      by [iApply lft_sincl_refl|iFrame|iIntros "% _ _ [$ _]"|].
  Qed.
  Lemma pbord_resolve {X α q x ξ} {Φx : X → _} :
    q.[α] -∗ pbord α x ξ Φx -∗ modw M (borrow_wsat M ⟦⟧)
      (q.[α] ∗ ⟨π, π ξ = x⟩ ∗ bor_tok α (Φx x)).
  Proof.
    iIntros "α b". iMod (pbord_open with "α b") as "[o Φx]".
    iMod (pobord_resolve with "o Φx") as "$". by iIntros.
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobord_nsubdiv {X α q ξ Φx} Ψx (x : X) β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗ ⟦ Ψx x ⟧ -∗
    (∀ x', [†β] -∗ ⟦ Ψx x' ⟧ -∗ M ⟦ Φx x' ⟧) =[borrow_wsat M ⟦⟧]=∗
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
    pobord α q ξ Φx -∗ ⟦ Φx x ⟧ =[borrow_wsat M ⟦⟧]=∗ q.[α] ∗ pbord α x ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobord_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobord_pobord_reborrow {X Y α q ξ Φx β r η Ψx} y (f : X → Y) :
    β ⊑□ α -∗ pobord β q ξ Φx -∗ pobord α r η Ψx -∗ ⟦ Ψx y ⟧ -∗
    (∀ y', [†β] -∗ pbord α y' η Ψx -∗ M ⟦ Φx (f y') ⟧) -∗
      modw M (borrow_wsat M ⟦⟧) (∃ η',
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
      modw M (borrow_wsat M ⟦⟧) (∃ η',
        q.[β] ∗ r.[α] ∗ ⟨π, π ξ = f (π (Aprvar _ η'))⟩ ∗ pbord β y η' Ψx).
  Proof.
    iIntros "⊑ o r b →Φx". iMod (pbord_open with "r b") as "[o' Ψx]".
    iApply (pobord_pobord_reborrow with "⊑ o o' Ψx →Φx").
  Qed.
End pborrow_deriv.
