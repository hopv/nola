(** * Fractured borrows *)

From nola.iris Require Export dinv_deriv borrow_deriv cif.
From iris.bi Require Export lib.fractional.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation ModwNotation LftNotation CsemNotation.

Implicit Type (α : lft) (q : Qp) (Σ : gFunctors).

(** ** Fractured borrows *)

Section fbor.
  Context `{!dinvJ (cifO CON Σ) JUDG, !borrowC CON, !lftG Σ}.
  Implicit Type (δ : JUDG -n> iProp Σ) (Φx : Qp -d> cif CON Σ).

  (** [fbor]: Relaxed fractured borrower *)
  Local Definition fbor_def δ α Φx : iProp Σ :=
    ∃ α', α ⊑□ α' ∗ dinv δ (∃ q, cif_bor α' (Φx q))%cif.
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

Arguments dsem {_ _ _ _} _ _ /.
Section fbor.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), dinvGS (cifOF CON) Σ,
    !dinvJ (cifO CON Σ) JUDG, !dinvJS (cifOF CON) JUDG Σ,
    !borrowGS (cifOF CON) Σ, !borrowC CON, !borrowJ (cifO CON Σ) JUDG,
    !borrowCS CON JUDG Σ, !borrowJS (cifOF CON) JUDG Σ,
    !ModUpd (PROP:=iProp Σ) M, !ModBUpd M}.

  (** Access the content of [fbord] under the fractionality of [Φx] *)
  Lemma fbord_acc_bord {α Φx r} :
    Fractional (λ q, ⟦ Φx q ⟧ᶜ) →
    fbord α Φx -∗ r.[α] -∗ modw M (dinv_wsat ⟦⟧ᶜ ∗ borrow_wsat M ⟦⟧ᶜ)
      (∃ q, r.[α] ∗ bord α (Φx q)).
  Proof.
    rewrite fbor_unseal. iIntros (frac) "(%α' & #⊑ & f) α [Wd Wb]".
    iDestruct (dinvd_acc (Dsem0:=cif_dsem) with "f Wd") as "/=[[%q b] cl]".
    rewrite sem_cif_in /=.
    iMod (lft_sincl_live_acc with "⊑ α") as (?) "[α' →α]".
    iMod (bord_open (Dsem0:=cif_dsem) with "α' b Wb") as "(Wb & o & Φx)".
    iMod (obord_subdiv (Dsem0:=cif_dsem) [Φx (q/2)%Qp; Φx (q/2)%Qp] α'
      with "[] o [Φx] [] Wb") as "($ & α' & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. }
    { rewrite -{1}(Qp.div_2 q) frac. iDestruct "Φx" as "[$$]". }
    { rewrite -{3}(Qp.div_2 q) frac. by iIntros "_ [$[$ _]]". }
    iModIntro. iDestruct ("→α" with "α'") as "$".
    iDestruct (bor_lft with "⊑ b") as "$". iApply "cl". iExists _.
    by rewrite sem_cif_in /=.
  Qed.
  Lemma fbord_acc {α Φx r} :
    Fractional (λ q, ⟦ Φx q ⟧ᶜ) →
    fbord α Φx -∗ r.[α] -∗ modw M (dinv_wsat ⟦⟧ᶜ ∗ borrow_wsat M ⟦⟧ᶜ)
      (∃ q, ⟦ Φx q ⟧ᶜ ∗ (⟦ Φx q ⟧ᶜ =[borrow_wsat M ⟦⟧ᶜ]=∗ r.[α])).
  Proof.
    iIntros (frac) "f α". iMod (fbord_acc_bord with "f α") as (?) "[α b]"=>//.
    iIntros "[$ Wb]".
    iMod (bord_open (Dsem0:=cif_dsem) with "α b Wb") as "/=($ & o & $)".
    iModIntro. iIntros "Φx".
    by iMod (obord_close (Dsem0:=cif_dsem) with "o Φx") as "[$ _]".
  Qed.

  (** Modify the lifetime of [fbor] *)
  Lemma fbor_lft {δ α β Φx} : β ⊑□ α -∗ fbor δ α Φx -∗ fbor δ β Φx.
  Proof.
    rewrite fbor_unseal. iIntros "#⊑ (% & #⊑' & $)". by iApply lft_sincl_trans.
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Allocate [fbor] from [bor] *)
  Lemma fbor_alloc {α} Φx q : bor δ α (Φx q) =[dinv_wsat ⟦⟧ᶜ(δ)]=∗ fbor δ α Φx.
  Proof.
    iIntros "b". rewrite fbor_unseal.
    iMod (dinv_alloc (Dsem0:=cif_dsem) (∃ q, cif_bor α (Φx q))%cif with "[b]")
      as "$"=>/=.
    { iExists _. rewrite sem_cif_in //=. } { iModIntro. iApply lft_sincl_refl. }
  Qed.

  (** Convert the body of [fbor] *)
  Lemma fbor_to {α Φx Ψx} :
    □ (∀ q δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ Φx q ⟧ᶜ(δ') ==∗ ⟦ Ψx q ⟧ᶜ(δ')) -∗
    □ (∀ q δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ Ψx q ⟧ᶜ(δ') ==∗ ⟦ Φx q ⟧ᶜ(δ')) -∗
    fbor δ α Φx -∗ fbor δ α Ψx.
  Proof.
    iIntros "#ΦΨ #ΨΦ". rewrite fbor_unseal. iIntros "(% & $ & i)".
    iApply (dinv_iff (FML:=cifOF _) with "[] i"). iIntros (????) "!> /=".
    iSplit; iIntros "[%q b]"; iExists q; rewrite !sem_cif_in /=;
      (iApply (bor_to (Dsem0:=cif_dsem) (ih:=ih) with "[] [] b");
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

  Context `{!dinvJ (cifO CON Σ) JUDG, !borrowC CON, !lftG Σ}.
  #[export] Program Instance fborCT_ecsem : Ecsem fborCT CON JUDG Σ :=
    ECSEM (λ _ δ α _ Φx _, fbor δ α Φx) _.
  Next Obligation. solve_proper. Qed.
End fborC.
(** [fborCS]: Semantics of [fborCT] registered *)
Notation fborCS := (inCS fborCT).

(** Reify [fbor] *)
Section fborC.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !dinvJ (cifO CON Σ) JUDG,
    !borrowC CON, !lftG Σ, !fborC CON, !fborCS CON JUDG Σ}.

  #[export] Program Instance fbor_as_cif {α Φx} :
    AsCif CON (λ δ, fbor δ α Φx) := AS_CIF (cif_fbor α Φx) _.
  Next Obligation. move=>/= *. by rewrite sem_cif_in. Qed.
End fborC.
