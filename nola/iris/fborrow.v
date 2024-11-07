(** * Fractured borrows *)

From nola.iris Require Export dinv_deriv borrow_deriv.
From nola.util Require Import tagged.
From iris.bi Require Export lib.fractional.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation ModwNotation LftNotation DsemNotation.

Implicit Type (α : lft) (q : Qp) (Σ : gFunctors) (FML : oFunctor) (FM : ofe).

(** Formula for fractured borrows *)
Variant fborrow_fml_id := .
Definition fborrow_fmlOF FML : oFunctor :=
  leibnizO (tagged fborrow_fml_id lft) * (Qp -d> FML).

(** Ghost state for fractured borrows *)
Class fborrowGpreS FML Σ : Type :=
  fborrowGpreS_dinv :: dinvGpreS (fborrow_fmlOF FML) Σ.
Class fborrowGS FML Σ : Type := fborrowGS_dinv :: dinvGS (fborrow_fmlOF FML) Σ.
Definition fborrowΣ FML `{!oFunctorContractive FML} :=
  dinvΣ (fborrow_fmlOF FML).
#[export] Instance subG_fborrowΣ
  `{!oFunctorContractive FML, !subG (fborrowΣ FML) Σ} : fborrowGpreS FML Σ.
Proof. solve_inG. Qed.

Section fborrow_wsat.
  Context `{!fborrowGS FML Σ, !borrowGS FML Σ, !bupdJ (FML $oi Σ) JUDG}.
  Implicit Type (Φx : Qp -d> FML $oi Σ) (δ : JUDG -n> iProp Σ).

  (** [fborrow_sem]: Semantics for [fborrow_fmlOF] *)
  Definition fborrow_sem δ : fborrow_fmlOF FML $oi Σ → iProp Σ :=
    λ '(Tagged α, Φx), (∃ q, bor δ α (Φx q))%I.
  (** [fborrow_sem] is non-expansive *)
  #[export] Instance fborrow_sem_ne {δ} : NonExpansive (fborrow_sem δ).
  Proof. move=> ?[??][??][/=/leibniz_equiv_iff<- ?]. solve_proper. Qed.
  (** [Dsem] for [fborrow_fmlOF] *)
  #[export] Instance fborrow_dsem :
    Dsem JUDG (fborrow_fmlOF FML $oi Σ) (iProp Σ) := DSEM fborrow_sem _.

  (** [fborrow_wsat]: World satisfaction for fractured borrows *)
  Local Definition fborrow_wsat_def δ : iProp Σ := dinv_wsat (fborrow_dsem δ).
  Local Lemma fborrow_wsat_aux : seal fborrow_wsat_def. Proof. by eexists. Qed.
  Definition fborrow_wsat := fborrow_wsat_aux.(unseal).
  Local Lemma fborrow_wsat_unseal : fborrow_wsat = fborrow_wsat_def.
  Proof. exact: seal_eq. Qed.
End fborrow_wsat.
Notation fborrow_wsatd := (fborrow_wsat der).

(** Allocate [fborrow_wsat] *)
Lemma fborrow_wsat_alloc `{!borrowGS FML Σ, !fborrowGpreS FML Σ,
  !bupdJ (FML $oi Σ) JUDG} :
  ⊢ |==> ∃ _ : fborrowGS FML Σ, ∀ δ, fborrow_wsat δ.
Proof.
  iMod dinv_wsat_alloc as (?) "→W". iModIntro. iExists _. iIntros (?).
  rewrite fborrow_wsat_unseal. iApply "→W". iApply ne_internal_ne.
Qed.

(** [fborrowJ]: Judgment for [fborrow] registered *)
Notation fborrowJ FML JUDG Σ := (dinvJ (fborrow_fmlOF FML $oi Σ) JUDG).
(** [fborrowJS]: Judgment semantics for [fborrow] registered *)
Notation fborrowJS FML JUDG Σ := (dinvJS (fborrow_fmlOF FML) JUDG Σ).

Section fbor.
  Context `{!borrowGS FML Σ, !fborrowJ FML JUDG Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Φx : Qp -d> FML $oi Σ).

  (** [fbor]: Relaxed fractured borrower *)
  Local Definition fbor_def δ α Φx : iProp Σ :=
    ∃ α', α ⊑□ α' ∗ dinv δ (Tagged α' : leibnizO _, Φx).
  Local Lemma fbor_aux : seal fbor_def. Proof. by eexists. Qed.
  Definition fbor := fbor_aux.(unseal).
  Local Lemma fbor_unseal : fbor = fbor_def. Proof. exact: seal_eq. Qed.

  (** [fbor] is persistent *)
  #[export] Instance fbor_persistent {δ α Φx} : Persistent (fbor δ α Φx).
  Proof. rewrite fbor_unseal. exact _. Qed.
  (** [fbor] is non-expansive *)
  #[export] Instance fbor_ne {δ α} : NonExpansive (fbor δ α).
  Proof. rewrite fbor_unseal /fbor_def=> ????. do 4 f_equiv. solve_proper. Qed.
  #[export] Instance fbor_proper {δ α} : Proper ((≡) ==> (≡)) (fbor δ α).
  Proof. apply ne_proper, _. Qed.
End fbor.
Notation fbord := (fbor der).

Section fbor.
  Context `{!borrowGS FML Σ, !bupdJ (FML $oi Σ) JUDG, !fborrowGS FML Σ,
    !fborrowJ FML JUDG Σ, !Dsem JUDG (FML $oi Σ) (iProp Σ),
    !Jsem JUDG (iProp Σ), !bupdJS (FML $oi Σ) JUDG (iProp Σ),
    !fborrowJS FML JUDG Σ, !ModUpd (PROP:=iProp Σ) M, !ModBUpd M}.

  (** Access the content of [fbord] under the fractionality of [Φx] *)
  Lemma fbord_acc_bord {α Φx r} :
    Fractional (λ q, ⟦ Φx q ⟧) →
    r.[α] -∗ fbord α Φx -∗ modw M (fborrow_wsatd ∗ borrow_wsat M ⟦⟧)
      (∃ q, r.[α] ∗ bor_tok α (Φx q)).
  Proof.
    rewrite fbor_unseal. iIntros (frac) "α (%α' & #⊑ & f) [Wf Wb]".
    rewrite fborrow_wsat_unseal.
    iDestruct (dinvd_acc (FML:=fborrow_fmlOF _) with "f Wf") as "/=[[%q b] cl]".
    iMod (lft_sincl_live_acc with "⊑ α") as (?) "[α' →α]".
    iMod (bord_open with "α' b Wb") as "(Wb & o & Φx)".
    iMod (obord_subdiv [Φx (q/2)%Qp; Φx (q/2)%Qp] α' with "[] o [Φx] [] Wb")
      as "($ & α' & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. }
    { rewrite -{1}(Qp.div_2 q) frac. iDestruct "Φx" as "[$$]". }
    { rewrite -{3}(Qp.div_2 q) frac. by iIntros "_ [$[$ _]]". }
    iModIntro. iDestruct ("→α" with "α'") as "$".
    iDestruct (bor_tok_lft with "⊑ b") as "$". iApply "cl". iExists _.
    by rewrite -bor_tok_bor.
  Qed.
  Lemma fbord_acc {α Φx r} :
    Fractional (λ q, ⟦ Φx q ⟧) →
    r.[α] -∗ fbord α Φx -∗ modw M (fborrow_wsatd ∗ borrow_wsat M ⟦⟧)
      (∃ q, ⟦ Φx q ⟧ ∗ (⟦ Φx q ⟧ =[borrow_wsat M ⟦⟧]=∗ r.[α])).
  Proof.
    iIntros (frac) "α f". iMod (fbord_acc_bord with "α f") as (?) "[α b]"=>//.
    iIntros "[$ Wb]". iMod (bor_tok_open with "α b Wb") as "/=($ & o & $)".
    iIntros "!> Φx". by iMod (obor_tok_close (M:=M) with "o Φx") as "[$ _]".
  Qed.

  (** Modify the lifetime of [fbor] *)
  Lemma fbor_lft {δ α β Φx} : β ⊑□ α -∗ fbor δ α Φx -∗ fbor δ β Φx.
  Proof.
    rewrite fbor_unseal. iIntros "#⊑ (% & #⊑' & $)". by iApply lft_sincl_trans.
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Allocate [fbor] from [bor] *)
  Lemma fbor_alloc {α} Φx q : bor δ α (Φx q) =[fborrow_wsat δ]=∗ fbor δ α Φx.
  Proof.
    iIntros "b". rewrite fbor_unseal fborrow_wsat_unseal.
    iMod (dinv_alloc (FML:=fborrow_fmlOF _) (Tagged α, Φx) with "[b]")
      as "$"=>/=; [by iExists _|].
    iModIntro. iApply lft_sincl_refl.
  Qed.

  (** Convert the body of [fbor] *)
  Lemma fbor_to {α Φx Ψx} :
    □ (∀ q δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ Φx q ⟧(δ') ==∗ ⟦ Ψx q ⟧(δ')) -∗
    □ (∀ q δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ Ψx q ⟧(δ') ==∗ ⟦ Φx q ⟧(δ')) -∗
    fbor δ α Φx -∗ fbor δ α Ψx.
  Proof.
    iIntros "#ΦΨ #ΨΦ". rewrite fbor_unseal. iIntros "(% & $ & i)".
    iApply (dinv_iff (FML:=fborrow_fmlOF _) with "[] i"). iIntros (????) "!>/=".
    iSplit; iIntros "[%q b]"; iExists q;
      (iApply (bor_to (ih:=ih) with "[] [] b");
        iIntros "!>" (????); by [iApply "ΦΨ"|iApply "ΨΦ"]).
  Qed.
End fbor.

(** ** Constructor *)

From nola.iris Require Import cif.

(** [fborCT]: Constructor *)
Variant fborCT_id := .
Definition fborCT :=
  Cifcon fborCT_id lft (λ _, Empty_set) (λ _, Qp) (λ _, unitO) _.
(** [fborC]: [fborCT] registered *)
Notation fborC := (inC fborCT).

Section fborC.
  Context `{!fborC CON} {Σ}.
  Implicit Type Φx : Qp -d> cif CON Σ.
  (** [cif_fbor]: Formula for [fbor] *)
  Definition cif_fbor α Φx : cif CON Σ :=
    cif_in fborCT α nullary Φx ().
  (** [cif_fbor] is non-expansive *)
  #[export] Instance cif_fbor_ne {α} : NonExpansive (cif_fbor α).
  Proof. solve_proper. Qed.
  #[export] Instance cif_fbor_proper {α} : Proper ((≡) ==> (≡)) (cif_fbor α).
  Proof. apply ne_proper, _. Qed.
  (** [cif_fbor] is productive *)
  #[export] Instance cif_bor_productive {α} : Productive (cif_fbor α).
  Proof. move=> ????. by apply cif_in_preserv_productive. Qed.

  Context `{!dinvJ (cifO CON Σ) JUDG, !borrowGS (cifOF CON) Σ,
    !fborrowJ (cifOF CON) JUDG Σ}.
  #[export] Program Instance fborCT_ecsem : Ecsem fborCT CON JUDG Σ :=
    ECSEM (λ _ δ α _ Φx _, fbor δ α Φx) _.
  Next Obligation. solve_proper. Qed.
End fborC.
(** [fborCS]: Semantics of [fborCT] registered *)
Notation fborCS := (inCS fborCT).

(** Reify [fbor] *)
Section fborC.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !dinvJ (cifO CON Σ) JUDG,
    !borrowGS (cifOF CON) Σ, !fborrowJ (cifOF CON) JUDG Σ, !fborC CON,
    !fborCS CON JUDG Σ}.

  #[export] Program Instance fbor_as_cif {α Φx} :
    AsCif CON (λ δ, fbor δ α Φx) := AS_CIF (cif_fbor α Φx) _.
  Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.
End fborC.
