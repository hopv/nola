(** * Adequacy *)

From nola.examples.rust_halt Require Export type.
Import PlistNotation WpwNotation.

Implicit Type JUDG : ofe.

(** Allocate the world satisfaction *)
Lemma rust_wsat_alloc `{!rust_haltGpreS CON Σ,
  lrustGS_gen0 : !lrustGS_gen HasNoLc Σ, !rust_haltJ CON JUDG Σ} :
  ⊢ |==> ∃ _ : rust_haltGS CON Σ, ⌜rust_haltGS_lrust = lrustGS_gen0⌝ ∧
    ∀ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)), rust_halt_wsat.
Proof.
  iMod inv_wsat_alloc as (?) "Winv". iMod dinv_wsat_alloc as (?) "Wdinv".
  iMod borrow_wsat_alloc as (?) "Wborrow". iMod proph_init as (?) "_".
  iMod fborrow_wsat_alloc as (?) "Wfborrow". iModIntro.
  iExists (RustHaltGS _ _ _ _ _ _ _ _ _ _ _). iSplit; [done|]. iIntros (??).
  iDestruct ("Winv" with "[]") as "$"; [iApply ne_internal_ne|].
  iDestruct ("Wdinv" with "[]") as "$"; [iApply ne_internal_ne|].
  iDestruct ("Wborrow" with "[]") as "$"; [iApply ne_internal_ne|].
  iApply "Wfborrow".
Qed.

(** Usual adequacy for a partial weakest precondition *)
Theorem wp_adequacy `{!rust_haltGpreS CON Σ, !rust_haltJ CON JUDG Σ}
  {e σ φ} :
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ |={⊤}=> WP[rust_halt_wsat] e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  move=> totwp. eapply lrust_adequacy; [exact _|]=> ?.
  iMod rust_wsat_alloc as (?<-) "→W". case (totwp _)=> ?[? twp].
  iMod twp as "$". iModIntro. iApply "→W".
Qed.

(** Termination adequacy over a total weakest precondition *)
Theorem twp_total `{!rust_haltGpreS CON Σ, !rust_haltJ CON JUDG Σ}
  {e σ} :
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)) Φ,
    ⊢ |={⊤}=> WP[rust_halt_wsat] e [{ Φ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. eapply lrust_total; [exact _|]=> ?.
  iMod rust_wsat_alloc as (?<-) "→W". case (totwp _)=> ?[?[? twp]].
  iMod twp as "$". iModIntro. iApply "→W".
Qed.

(** Usual adequacy over a typing judgment *)
Theorem type_adeqaucy `{!rust_haltGpreS CON Σ, !rust_haltJ CON JUDG Σ}
  {Xl e Γo pre σ} :
  (∀ post, pre post ()) →
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ type (Yl:=Xl) ⊤ ᵖ[] e (λ _, Γo) pre) →
  adequate NotStuck e σ (λ _ _, True).
Proof.
  move=> topre totyp. eapply wp_adequacy=> ?. case (totyp _)=> ?[? typ].
  exists _, _. rewrite type_unseal in typ.
  iMod (na_alloc (na_invG0:=rust_haltGS_na_inv)) as (t) "t". iModIntro.
  iDestruct (typ $! 1%Qp t (λ _ _, True) () with "[//] t [] [//]") as "twp".
  { by iApply proph_obs_true. }
  iApply twp_wp. iApply (twp_mono with "twp"). by iIntros.
Qed.

(** Termination adequacy over a typing judgment *)
Theorem type_total `{!rust_haltGpreS CON Σ, !rust_haltJ CON JUDG Σ}
  {Xl e Γo pre σ} :
  (∀ post, pre post ()) →
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ type (Yl:=Xl) ⊤ ᵖ[] e (λ _, Γo) pre) →
  sn erased_step ([e], σ).
Proof.
  move=> topre totyp. eapply twp_total=> ?. case (totyp _)=> ?[? typ].
  exists _, _, (λ _, True)%I. rewrite type_unseal in typ.
  iMod (na_alloc (na_invG0:=rust_haltGS_na_inv)) as (t) "t". iModIntro.
  iDestruct (typ $! 1%Qp t (λ _ _, True) () with "[//] t [] [//]") as "twp".
  { by iApply proph_obs_true. }
  iApply (twp_mono with "twp"). by iIntros.
Qed.
