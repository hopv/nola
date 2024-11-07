(** * Fractured borrows *)

From nola.iris Require Export dinv borrow.
From iris.bi Require Export lib.fractional.
From iris.proofmode Require Import proofmode.
Import ProdNotation iPropAppNotation ModwNotation LftNotation.

Implicit Type (α : lft) (q : Qp) (Σ : gFunctors) (FML : oFunctor) (JUDG : ofe).

(** Formula for fractured borrows *)
Definition fborrow_fmlOF FML : oFunctor := leibnizO lft * (Qp -d> FML).

(** Ghost state for fractured borrows *)
Class fborrowGpreS FML Σ : Type :=
  fborrowGpreS_dinv : dinvGpreS (fborrow_fmlOF FML) Σ.
Local Existing Instance fborrowGpreS_dinv.
Class fborrowGS FML Σ : Type := fborrowGS_dinv : dinvGS (fborrow_fmlOF FML) Σ.
Local Existing Instance fborrowGS_dinv.
Definition fborrowΣ FML `{!oFunctorContractive FML} :=
  dinvΣ (fborrow_fmlOF FML).
#[export] Instance subG_fborrowΣ
  `{!oFunctorContractive FML, !subG (fborrowΣ FML) Σ} : fborrowGpreS FML Σ.
Proof. solve_inG. Qed.

Section fborrow.
  Context `{!fborrowGS FML Σ, !borrowGS FML Σ}.
  Implicit Type (Φx : Qp -d> FML $oi Σ).

  (** [fbor_tok]: Fractured borrower token *)
  Local Definition fbor_tok_def α Φx : iProp Σ :=
    ∃ α', α ⊑□ α' ∗ dinv_tok (α', Φx).
  Local Lemma fbor_tok_aux : seal fbor_tok_def. Proof. by eexists. Qed.
  Definition fbor_tok := fbor_tok_aux.(unseal).
  Local Lemma fbor_tok_unseal : fbor_tok = fbor_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [fbor_tok] is persistent *)
  #[export] Instance fbor_tok_persistent {α Φx} : Persistent (fbor_tok α Φx).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.
  (** [fbor_tok] is timeless for discrete formulas *)
  #[export] Instance fbor_tok_timeless {α} `{!Discrete Φx} :
    Timeless (fbor_tok α Φx).
  Proof. rewrite fbor_tok_unseal. exact _. Qed.
  (** [fbor_tok] is non-expansive *)
  #[export] Instance fbor_tok_ne {α} : NonExpansive (fbor_tok α).
  Proof.
    rewrite fbor_tok_unseal /fbor_tok_def=> ????. do 4 f_equiv. solve_proper.
  Qed.
  #[export] Instance fbor_tok_proper {α} : Proper ((≡) ==> (≡)) (fbor_tok α).
  Proof. apply ne_proper, _. Qed.

  (** [fborrow_sem]: Semantics for [fborrow_fmlOF] *)
  Definition fborrow_sem : fborrow_fmlOF FML $oi Σ → iProp Σ :=
    λ '(α, Φx), (∃ q, bor_tok α (Φx q))%I.
  (** [fborrow_sem] is non-expansive *)
  #[export] Instance fborrow_sem_ne : NonExpansive fborrow_sem.
  Proof. move=> ?[??][??][/=/leibniz_equiv_iff<- ?]. solve_proper. Qed.

  (** [fborrow_wsat]: World satisfaction for fractured borrows *)
  Local Definition fborrow_wsat_def : iProp Σ := dinv_wsat fborrow_sem.
  Local Lemma fborrow_wsat_aux : seal fborrow_wsat_def. Proof. by eexists. Qed.
  Definition fborrow_wsat := fborrow_wsat_aux.(unseal).
  Local Lemma fborrow_wsat_unseal : fborrow_wsat = fborrow_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [fborrow_wsat] is timeless when all formulas are discrete *)
  #[export] Instance fborrow_wsat_timeless `{!OfeDiscrete (FML $oi Σ)} :
    Timeless fborrow_wsat.
  Proof.
    rewrite fborrow_wsat_unseal. apply: dinv_wsat_timeless. case. exact _.
  Qed.
End fborrow.

(** Allocate [fborrow_wsat] *)
Lemma fborrow_wsat_alloc `{!borrowGS FML Σ, !fborrowGpreS FML Σ} :
  ⊢ |==> ∃ _ : fborrowGS FML Σ, fborrow_wsat.
Proof.
  iMod dinv_wsat_alloc as (?) "→W". iModIntro. iExists _.
  rewrite fborrow_wsat_unseal. iApply "→W". iApply ne_internal_ne.
Qed.

Section fborrow.
  Context `{!borrowGS FML Σ, !fborrowGS FML Σ, !ModUpd (PROP:=iProp Σ) M,
    !ModBUpd M}.

  (** Modify the lifetime of [fbor_tok] *)
  Lemma fbor_tok_lft {α β Φx} : β ⊑□ α -∗ fbor_tok α Φx -∗ fbor_tok β Φx.
  Proof.
    rewrite fbor_tok_unseal. iIntros "#⊑ (% & #⊑' & $)".
    by iApply lft_sincl_trans.
  Qed.

  (** Allocate [fbor_tok] from [bor_tok] *)
  Lemma fbor_tok_alloc {α} Φx q :
    bor_tok α (Φx q) =[fborrow_wsat]=∗ fbor_tok α Φx.
  Proof.
    iIntros "b". rewrite fbor_tok_unseal fborrow_wsat_unseal.
    iMod (dinv_tok_alloc (FML:=fborrow_fmlOF _) (α, Φx) with "[b]")
      as "$"=>/=; [by iExists _|].
    iModIntro. iApply lft_sincl_refl.
  Qed.

  (** Access the content of [fbor_tok] under the fractionality of [Φx] *)
  Lemma fbor_tok_acc_bor_tok {α Φx r sm} :
    Fractional (λ q, sm (Φx q)) →
    r.[α] -∗ fbor_tok α Φx -∗ modw M (fborrow_wsat ∗ borrow_wsat M sm)
      (∃ q, r.[α] ∗ bor_tok α (Φx q)).
  Proof.
    rewrite fbor_tok_unseal. iIntros (frac) "α (%α' & #⊑ & f) [Wf Wb]".
    rewrite fborrow_wsat_unseal.
    iDestruct (dinv_tok_acc (FML:=fborrow_fmlOF _) with "f Wf")
      as "/=[[%q b] cl]".
    iMod (lft_sincl_live_acc with "⊑ α") as (?) "[α' →α]".
    iMod (bor_tok_open with "α' b Wb") as "(Wb & o & Φx)".
    iMod (obor_tok_subdiv [Φx (q/2)%Qp; Φx (q/2)%Qp] α' with "[] o [Φx] [] Wb")
      as "($ & α' & _ & b & b' & _)"=>/=.
    { iApply lft_sincl_refl. }
    { rewrite -{1}(Qp.div_2 q) frac. iDestruct "Φx" as "[$$]". }
    { rewrite -{3}(Qp.div_2 q) frac. by iIntros "_ [$[$ _]]". }
    iModIntro. iDestruct ("→α" with "α'") as "$".
    iDestruct (bor_tok_lft with "⊑ b") as "$". iApply "cl". by iExists _.
  Qed.
  Lemma fbor_tok_acc {α Φx r sm} :
    Fractional (λ q, sm (Φx q)) →
    r.[α] -∗ fbor_tok α Φx -∗ modw M (fborrow_wsat ∗ borrow_wsat M sm)
      (∃ q, sm (Φx q) ∗ (sm (Φx q) =[borrow_wsat M sm]=∗ r.[α])).
  Proof.
    iIntros (frac) "α f".
    iMod (fbor_tok_acc_bor_tok with "α f") as (?) "[α b]"=>//. iIntros "[$ Wb]".
    iMod (bor_tok_open with "α b Wb") as "/=($ & o & $)". iIntros "!> Φx".
    by iMod (obor_tok_close (M:=M) with "o Φx") as "[$ _]".
  Qed.
End fborrow.

(** ** Constructor *)

From nola.iris Require Import cif.

(** [fbor_tokCT]: Constructor *)
Variant fbor_tokCT_id := .
Definition fbor_tokCT :=
  Cifcon fbor_tokCT_id lft (λ _, Empty_set) (λ _, Qp) (λ _, unitO) _.
(** [fbor_tokC]: [fbor_tokCT] registered *)
Notation fbor_tokC := (inC fbor_tokCT).

Section fbor_tokC.
  Context `{!fbor_tokC CON} {Σ}.
  Implicit Type Φx : Qp -d> cif CON Σ.
  (** [cif_fbor_tok]: Formula for [fbor_tok] *)
  Definition cif_fbor_tok α Φx : cif CON Σ :=
    cif_in fbor_tokCT α nullary Φx ().
  (** [cif_fbor_tok] is non-expansive *)
  #[export] Instance cif_fbor_tok_ne {α} : NonExpansive (cif_fbor_tok α).
  Proof. solve_proper. Qed.
  #[export] Instance cif_fbor_tok_proper {α} :
    Proper ((≡) ==> (≡)) (cif_fbor_tok α).
  Proof. apply ne_proper, _. Qed.
  (** [cif_fbor_tok] is productive *)
  #[export] Instance cif_fbor_tok_productive {α} : Productive (cif_fbor_tok α).
  Proof. move=> ????. by apply cif_in_preserv_productive. Qed.

  Context `{!borrowGS (cifOF CON) Σ, !fborrowGS (cifOF CON) Σ} {JUDG}.
  #[export] Program Instance fbor_tokCT_ecsem : Ecsem fbor_tokCT CON JUDG Σ :=
    ECSEM (λ _ _ α _ Φx _, fbor_tok α Φx) _.
  Next Obligation. solve_proper. Qed.
End fbor_tokC.
(** [fbor_tokCS]: Semantics of [fbor_tokCT] registered *)
Notation fbor_tokCS := (inCS fbor_tokCT).

(** Reify [fbor_tok] *)
Section fbor_tokC.
  Context `{!fbor_tokC CON, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
    !borrowGS (cifOF CON) Σ, !fborrowGS (cifOF CON) Σ, !fbor_tokCS CON JUDG Σ}.

  #[export] Program Instance fbor_tok_as_cif {α Φx} :
    AsCif CON (λ _, fbor_tok α Φx) := AS_CIF (cif_fbor_tok α Φx) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End fbor_tokC.
