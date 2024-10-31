(** * Prophetic borrowing machinery relaxed with derivability *)

From nola.util Require Import tagged.
From nola.bi Require Export deriv.
From nola.iris Require Export pborrow borrow_deriv.
From iris.proofmode Require Import proofmode.
Import ProdNotation PlistNotation iPropAppNotation ModwNotation LftNotation
  ProphNotation DsemNotation.

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !proph_agC A TY CON, !borrowJ (cifOF CON $oi Σ) JUDG}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Px Qx : cif CON Σ) (X Y : TY).

  (** [pbor]: Relaxed prophetic borrower *)
  Local Definition pbor_def {X} δ α a xπ ξ (Φx : _ -d> _ -d> cif CON Σ)
    : iProp Σ :=
    ∃ Ψx, □ (∀ a xπ, δ (borrow_jto (Φx a xπ) (Ψx a xπ))) ∗
      □ (∀ a xπ, δ (borrow_jto (Ψx a xπ) (Φx a xπ))) ∗
      pbor_tok (X:=X) α a xπ ξ Ψx.
  Local Lemma pbor_aux : seal (@pbor_def). Proof. by eexists. Qed.
  Definition pbor {X} := pbor_aux.(unseal) X.
  Local Lemma pbor_unseal : @pbor = @pbor_def. Proof. exact: seal_eq. Qed.
  (** [pobor]: Relaxed prophetic open borrower *)
  Local Definition pobor_def {X} δ α q ξ (Φx : _ -d> _ -d> cif CON Σ)
    : iProp Σ :=
    ∃ Ψx, □ (∀ a xπ, δ (borrow_jto (Φx a xπ) (Ψx a xπ))) ∗
      □ (∀ a xπ, δ (borrow_jto (Ψx a xπ) (Φx a xπ))) ∗
      pobor_tok (X:=X) α q ξ Ψx.
  Local Lemma pobor_aux : seal (@pobor_def). Proof. by eexists. Qed.
  Definition pobor {X} := pobor_aux.(unseal) X.
  Local Lemma pobor_unseal : @pobor = @pobor_def. Proof. exact: seal_eq. Qed.
  (** [plend]: Relaxed prophetic lender *)
  Definition plend {X} δ α xπ (Φx : _ -d> cif CON Σ) : iProp Σ :=
    lend δ α (cif_xplend (X:=X) xπ Φx).

  (** Borrower and lender propositions are non-expansive *)
  #[export] Instance pbor_ne {δ X α a xπ ξ} :
    NonExpansive (pbor (X:=X) δ α a xπ ξ).
  Proof. rewrite pbor_unseal. solve_proper. Qed.
  #[export] Instance pbor_proper {δ X α a xπ ξ} :
    Proper ((≡) ==> (⊣⊢)) (pbor (X:=X) δ α a xπ ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance pobor_ne {δ X α q ξ} : NonExpansive (pobor (X:=X) δ α q ξ).
  Proof. rewrite pobor_unseal. solve_proper. Qed.
  #[export] Instance pobor_proper {δ X α q ξ} :
    Proper ((≡) ==> (⊣⊢)) (pobor (X:=X) δ α q ξ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance plend_ne {δ X α xπ} : NonExpansive (plend (X:=X) δ α xπ).
  Proof. solve_proper. Qed.
  #[export] Instance plend_proper {δ X α xπ} :
    Proper ((≡) ==> (⊣⊢)) (plend (X:=X) δ α xπ).
  Proof. apply ne_proper, _. Qed.
End pborrow_deriv.

(** Notation *)
Notation pbord := (pbor der). Notation pobord := (pobor der).
Notation plendd := (plend der).

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !proph_agC A TY CON, !borrowJ (cifOF CON $oi Σ) JUDG, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ), !proph_agCS A TY CON JUDG Σ,
    !borrowJS (cifOF CON) JUDG Σ, !Deriv (JUDG:=JUDG) ih δ}.
  Implicit Type (X Y Z : TY) (Px Qx Rx : cif CON Σ) (δ : JUDG -n> iProp Σ).

  (** ** Conversion *)

  (** Utility *)
  Lemma der_borrow_jto' {Px Qx} :
    der (borrow_jto Px Qx) ⊢ (cif_sem der Px ==∗ cif_sem der Qx).
  Proof. exact der_borrow_jto. Qed.

  (** Convert the body of borrower and lender propositions *)
  Lemma pbor_to {X α a xπ ξ Φx Ψx} :
    □ (∀ a xπ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx a xπ ⟧(δ') ==∗ ⟦ Ψx a xπ ⟧(δ')) -∗
    □ (∀ a xπ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx a xπ ⟧(δ') ==∗ ⟦ Φx a xπ ⟧(δ')) -∗
    pbor (X:=X) δ α a xπ ξ Φx -∗ pbor δ α a xπ ξ Ψx.
  Proof.
    rewrite pbor_unseal. iIntros "#ΦΨ #ΨΦ (%Ω & #ΦΩ & #ΩΦ & $)".
    iSplit; iIntros "!>" (??); [by iApply borrow_jto_trans|].
    iApply borrow_jto_trans'; by [iApply "ΦΨ"|].
  Qed.
  Lemma pobor_to {X α q ξ Φx Ψx} :
    □ (∀ a xπ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Φx a xπ ⟧(δ') ==∗ ⟦ Ψx a xπ ⟧(δ')) -∗
    □ (∀ a xπ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Ψx a xπ ⟧(δ') ==∗ ⟦ Φx a xπ ⟧(δ')) -∗
    pobor (X:=X) δ α q ξ Φx -∗ pobor δ α q ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "#ΦΨ #ΨΦ (%Ω & #ΦΩ & #ΩΦ & $)".
    iSplit; iIntros "!>" (??); [by iApply borrow_jto_trans|].
    iApply borrow_jto_trans'; by [iApply "ΦΨ"|].
  Qed.
  Lemma plend_to {X Y α xπ yπ Φx Ψx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      xplend δ' xπ Φx ==∗ xplend δ' yπ Ψx) -∗
    plend (X:=X) δ α xπ Φx -∗ plend (X:=Y) δ α yπ Ψx.
  Proof.
    iIntros "?". iApply lend_to=>/=. by setoid_rewrite sem_ecustom=>/=.
  Qed.

  (** Modify the lifetime of borrower and lender propositions *)
  Lemma pbor_lft {X α β a xπ ξ Φx} :
    β ⊑□ α -∗ pbor (X:=X) δ α a xπ ξ Φx -∗ pbor δ β a xπ ξ Φx.
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
  Proof. exact lend_lft. Qed.

  (** Turn from tokens *)
  Lemma pbor_tok_pbor {X α a xπ ξ Φx} :
    pbor_tok (X:=X) α a xπ ξ Φx ⊢ pbor δ α a xπ ξ Φx.
  Proof.
    rewrite pbor_unseal. iIntros "$".
    iSplit; iIntros "!> %%"; iApply borrow_jto_refl.
  Qed.
  Lemma pobor_tok_pobor {X α q ξ Φx} :
    pobor_tok (X:=X) α q ξ Φx ⊢ pobor δ α q ξ Φx.
  Proof.
    rewrite pobor_unseal. iIntros "$".
    iSplit; iIntros "!> %%"; iApply borrow_jto_refl.
  Qed.
  Lemma plend_tok_plend {X α xπ Φx} :
    plend_tok (X:=X) α xπ Φx ⊢ plend δ α xπ Φx.
  Proof. exact lend_tok_lend. Qed.

  Context `{!@ModUpd (iProp Σ) M, !ModBUpd M, !ModExcept0 M}.

  (** ** Rules that work under [Deriv ih δ] *)

  (** Create new prophetic borrowers and lenders *)
  Lemma pbor_plend_new_list Xl α (axπΦxl : plist _ Xl) :
    ⊢ |==> ∃ ξl, ∀ Yl (yπΨxl : plist (λ Y, _ *' (clair TY Y → _)) Yl),
      let ξaxπΦxl := plist_zip ξl axπΦxl in
      ([∗ plist] '(a, xπ, Φx)' ∈ axπΦxl, ⟦ Φx a xπ ⟧(δ)) -∗
      ([†α] -∗ ([∗ plist] '(ξ, _, _, Φx)' ∈ ξaxπΦxl,
        xplend_var δ ξ (λ xπ, ∃ a, Φx a xπ)%cif) -∗
        M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplend δ yπ Ψx))
        =[borrow_wsat M ⟦⟧(δ)]=∗
        ([∗ plist] '(ξ, a, xπ, Φx)' ∈ ξaxπΦxl, pbor δ α a xπ ξ Φx) ∗
        ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plend δ α yπ Ψx).
  Proof.
    simpl. setoid_rewrite <-pbor_tok_pbor. setoid_rewrite <-plend_tok_plend.
    exact: pbor_plend_tok_new_list.
  Qed.
  (** Simply create a prophetic borrower and a prophetic lender *)
  Lemma pbor_plend_new X α a xπ Φx :
    ⟦ Φx a xπ ⟧(δ) =[borrow_wsat M ⟦⟧(δ)]=∗ ∃ ξ,
      pbor (X:=X) δ α a xπ ξ Φx ∗ plend δ α (λ π, π ξ) (λ xπ, ∃ a, Φx a xπ)%cif.
  Proof.
    setoid_rewrite <-pbor_tok_pbor. setoid_rewrite <-plend_tok_plend.
    exact: pbor_plend_tok_new.
  Qed.
End pborrow_deriv.

Section pborrow_deriv.
  Context `{!borrowGS (cifOF CON) Σ, !prophGS TY Σ, !proph_agG A TY Σ,
    !proph_agC A TY CON, !borrowJ (cifOF CON $oi Σ) JUDG, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ), !proph_agCS A TY CON JUDG Σ,
    !borrowJS (cifOF CON) JUDG Σ, !@ModUpd (iProp Σ) M, !ModBUpd M,
    !ModExcept0 M}.
  Implicit Type (X Y : TY) (Px Qx : cif CON Σ).

  (** Split a prophetic lender *)
  Lemma plendd_split {X α} {xπ : clair TY X} {Φx} Yl
    (yπΨxl : plist (λ Y, _ *' (clair TY Y → _)) Yl) :
    plendd α xπ Φx -∗
    (xplendd xπ Φx -∗ M ([∗ plist] '(yπ, Ψx)' ∈ yπΨxl, xplendd yπ Ψx))
      =[borrow_wsat M ⟦⟧]=∗ [∗ plist] '(yπ, Ψx)' ∈ yπΨxl, plendd α yπ Ψx.
  Proof.
    iIntros "/=l →Ψxl".
    iMod (lendd_split (FML:=cifOF _) (M:=M)
      (nola.iris.pborrow.cif_xplendl yπΨxl) with "l [→Ψxl]");
      rewrite big_sepL_of_plist //=.
    by setoid_rewrite sem_ecustom=>/=.
  Qed.

  (** Retrieve from a prophetic lender *)
  Lemma plend_tok_retrieve {X α} {xπ : clair TY X} {Φx} :
    [†α] -∗ plendd α xπ Φx -∗ modw M (borrow_wsat M ⟦⟧) (xplendd xπ Φx).
  Proof.
    iIntros "† l". iMod (lendd_retrieve with "† l")=>/=.
    by setoid_rewrite sem_ecustom.
  Qed.

  (** Open a prophetic borrower *)
  Lemma pbord_open {X α q a xπ} {ξ : prvar X} {Φx} :
    q.[α] -∗ pbord α a xπ ξ Φx -∗ modw M (borrow_wsat M ⟦⟧)
      (pobord α q ξ Φx ∗ ⟦ Φx a xπ ⟧).
  Proof.
    rewrite pbor_unseal pobor_unseal. iIntros "α (% & $ & #ΨΦ & b)".
    iMod (pbor_tok_open (M:=M) with "α b") as "[$ Ψx]".
    iMod (der_borrow_jto with "ΨΦ Ψx") as "$". by iIntros "$".
  Qed.

  (** Subdivide a prophetic borrower without changing the prophecy *)
  Lemma pobord_nsubdiv {X α q ξ Φx} Ψx a (xπ : clair TY X) β :
    β ⊑□ α -∗ pobord α q ξ Φx -∗ ⟦ Ψx a xπ ⟧ -∗
    (∀ a' xπ', [†β] -∗ ⟦ Ψx a' xπ' ⟧ -∗ M ⟦ Φx a' xπ' ⟧)
      =[borrow_wsat M ⟦⟧]=∗ q.[α] ∗ pbord β a xπ ξ Ψx.
  Proof.
    rewrite pobor_unseal. iIntros "⊑ (%Ω & #ΦΩ & _ & o) Ψx →Φx".
    rewrite -pbor_tok_pbor.
    iApply (pobor_tok_nsubdiv (M:=M) with "⊑ o Ψx [ΦΩ →Φx]").
    iIntros "%% † Ψx". iMod ("→Φx" with "† Ψx") as "Φx".
    by iMod (der_borrow_jto with "ΦΩ Φx").
  Qed.
  (** Simply close a prophetic borrower *)
  Lemma pobord_close {X α q ξ Φx} a (xπ : clair TY X) :
    pobord α q ξ Φx -∗ ⟦ Φx a xπ ⟧ =[borrow_wsat M ⟦⟧]=∗
      q.[α] ∗ pbord α a xπ ξ Φx.
  Proof.
    iIntros "o Φx". iApply (pobord_nsubdiv Φx with "[] o Φx"); [|by iIntros].
    iApply lft_sincl_refl.
  Qed.

  (** Subdivide a prophetic borrower *)
  Lemma pobord_subdiv {X α q r ξ Φx}
    Yl (fπ : clair TY (_ → X)) ζl (ayπΨxl : plist _ Yl) Rxl β :
    (∀ π π' p p', fπ π p = fπ π' p' → p = p') →
    (∀ p, proph_dep (λ π, fπ π p) ζl) →
    pobord α q ξ Φx =[r:∗[ζl]]=∗ ∃ ηl,
      ⟨π, π (Aprvar _ ξ) = fπ π (app_plist_prvar π ηl)⟩ ∗
      (β ⊑□ α -∗
        ([∗ plist] '(a, yπ, Ψx)' ∈ ayπΨxl, ⟦ Ψx a yπ ⟧) -∗
        ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗
        (∀ yπl', [†β] -∗
          ([∗ plist] '(yπ', _, _, Ψx)' ∈ plist_zip yπl' ayπΨxl,
            ⟦ ∃ a, Ψx a yπ' ⟧%cif) -∗
          ([∗ list] Rx ∈ Rxl, ⟦ Rx ⟧) -∗
            M ⟦ ∃ a, Φx a (λ π, fπ π (app_plist_clair π yπl')) ⟧%cif)
          =[borrow_wsat M ⟦⟧]=∗
          q.[α] ∗
          ([∗ plist] '(η, a, yπ, Ψx)' ∈ plist_zip ηl ayπΨxl,
            pbord β a yπ η Ψx) ∗
          [∗ list] Rx ∈ Rxl, bord β Rx).
  Proof.
    rewrite pobor_unseal=> ??. iIntros "(%Φx' & #ΦΦ' & #? & o)".
    iMod (pobor_tok_subdiv with "o") as (?) "[$ big]"; [done..|].
    iIntros "!> ⊑ Ψxl Rxl →Φx". setoid_rewrite <-pbor_tok_pbor.
    setoid_rewrite <-bor_tok_bor. iApply ("big" with "⊑ Ψxl Rxl").
    iIntros "% † Ψxl Rxl". iMod ("→Φx" with "† Ψxl Rxl") as "/=[% Φx]".
    by iMod (der_borrow_jto' with "ΦΦ' Φx") as "$".
  Qed.

  (** Resolve the prophecy of a prophetic borrower *)
  Lemma pobord_resolve {X α q r ξ Φx} a (xπ : clair TY X) ηl :
    proph_dep xπ ηl →
    pobord α q ξ Φx =[r:∗[ηl]]=∗
      ⟨π, π ξ = xπ π⟩ ∗
      (⟦ Φx a xπ ⟧ =[borrow_wsat M ⟦⟧]=∗ q.[α] ∗ bord α (Φx a xπ)).
  Proof.
    iIntros (?) "o".
    iMod (pobord_subdiv [] (λ π _, xπ π) ηl () [Φx a xπ] with "o")
      as "[%[$ big]]"=>//=. { by move=> ??[][]. }
    iIntros "!> Φx".
    iMod ("big" with "[] [//] [$Φx //] []") as "($ & _ & $ & _)"=>//.
    { iApply lft_sincl_refl. } { by iIntros "_ _ _ [$ _]". }
  Qed.

  (** Reborrow a nested prophetic borrower *)
  Lemma pobord_pbord_reborrow {X Y α q ξ Φx β r η Ψx a yπ}
    (fπ : clair TY (Y → X)) :
    (∀ π π' y y', fπ π y = fπ π' y' → y = y') →
    β ⊑□ α -∗ r.[α] -∗
    pobord β q ξ Φx -∗ pbord α a yπ η Ψx -∗
    (∀ a' yπ', [†β] -∗ pbord α a' yπ' η Ψx -∗ M
      ⟦ Φx a' (λ π, fπ π (yπ' π)) ⟧) -∗
      modw M (borrow_wsat M ⟦⟧) (1:[η] ∗ ⟦ Ψx a yπ ⟧ ∗
        ∀ ζl s, ⌜∀ y, proph_dep (λ π, fπ π y) ζl⌝ -∗ s:∗[ζl]
          ==∗ ∃ η' : prvar _, ⟨π, π ξ = fπ π (π η')⟩ ∗ s:∗[ζl] ∗
            (1:[η] -∗ ⟦ Ψx a yπ ⟧ =[borrow_wsat M ⟦⟧]=∗
              q.[β] ∗ r.[α] ∗ pbord β a yπ η' Ψx)).
  Proof.
    rewrite pobor_unseal pbor_unseal. iIntros (?) "⊑ α".
    iIntros "(%Φx' & #ΦΦ' & #? & o) (%Ψx' & #ΨΨ' & #Ψ'Ψ & b) →Φx".
    iMod (pobor_pbor_tok_reborrow with "⊑ α o b [→Φx]") as "($ & Ψ'x & big)".
    { done. }
    { iIntros "%% † b". iMod ("→Φx" with "† [$b]") as "Φx"; [by iSplit|].
      by iMod (der_borrow_jto with "ΦΦ' Φx"). }
    iMod (der_borrow_jto with "Ψ'Ψ Ψ'x") as "$". iModIntro.
    iIntros (???) "ζl". iMod ("big" with "[//] ζl") as (?) "($ & $ & big)".
    iIntros "!> η Ψx". iMod (der_borrow_jto with "ΨΨ' Ψx") as "Ψx'".
    iMod ("big" with "η Ψx'") as "($ & $ & $)". iModIntro. by iSplit.
  Qed.
End pborrow_deriv.
