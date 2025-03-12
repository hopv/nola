(** * Adequacy *)

From nola.rust_lang Require Export adequacy.
From nola.examples.rust_halt Require Export type num.

Implicit Type JUDG : ofe.

(** Ghost state *)
Class rust_haltGpreS CON Σ : Type := RustHaltGpreS {
  rust_haltGpreS_lrust :: lrustGpreS Σ;
  rust_haltGoreS_inv :: inv'GpreS (cifOF CON) Σ;
  rust_haltGpreS_na_inv :: na_invG Σ;
  rust_haltGpreS_dinv :: dinvGpreS (cifOF CON) Σ;
  rust_haltGpreS_token :: tokenG Σ;
  rust_haltGpreS_borrow :: borrowGpreS (cifOF CON) Σ;
  rust_haltGpreS_proph :: prophGpreS xty Σ;
  rust_haltGpreS_proph_ag :: proph_agG nat xty Σ;
  rust_haltGpreS_fborrow :: fborrowGpreS (cifOF CON) Σ;
}.
Definition rust_haltΣ CON : gFunctors :=
  #[lrustΣ; inv'Σ (cifOF CON); na_invΣ; dinvΣ (cifOF CON); tokenΣ;
    borrowΣ (cifOF CON); prophΣ xty; proph_agΣ nat xty; fborrowΣ (cifOF CON)].
Global Instance subG_rust_haltGpreS `{!subG (rust_haltΣ CON) Σ} :
  rust_haltGpreS CON Σ.
Proof. solve_inG. Qed.

(** Allocate the world satisfaction *)
Lemma rust_wsat_alloc `{!rust_haltGpreS CON Σ,
  lrustGS_gen0 : !lrustGS_gen HasNoLc Σ} {JUDG} :
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

(** Safety adequacy for a partial weakest precondition *)
Theorem wp_adequacy `{!rust_haltGpreS CON Σ} {JUDG s e σ φ} :
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    own heap_name (◯ to_heap σ) ={⊤}=∗ WP[rust_halt_wsat] e @ s; ⊤ {{ v, ∀ σ',
      own heap_name (● to_heap σ') -∗ rust_halt_wsat ={⊤,∅}=∗ ⌜φ v σ'⌝ }}) →
  adequate s e σ φ.
Proof.
  move=> towp. eapply lrust_adequacy=> ?. iIntros "◯σ".
  iMod rust_wsat_alloc as (?<-) "→W". case: (towp _)=> ?[? wp].
  iMod (wp with "◯σ") as "$". iModIntro. iApply "→W".
Qed.

(** Termination adequacy for a total weakest precondition *)
Theorem twp_total `{!rust_haltGpreS CON Σ} {JUDG s e σ} :
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)) Φ,
    own heap_name (◯ to_heap σ) ={⊤}=∗ WP[rust_halt_wsat] e @ s; ⊤ [{ Φ }]) →
  sn erased_step ([e], σ).
Proof.
  move=> totwp. eapply lrust_total=> ?. iIntros "◯σ".
  iMod rust_wsat_alloc as (?<-) "→W". case: (totwp _)=> ?[?[? twp]].
  iMod (twp with "◯σ") as "$". iModIntro. iApply "→W".
Qed.

(** Safety adequacy for a typing judgment *)
Theorem type_adeqaucy `{!rust_haltGpreS CON Σ} {Xl post pre Γo e σ JUDG} :
  pre post () →
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ type (Yl:=Xl) ⊤ ᵖ[] e (λ _, Γo) pre) →
  adequate NotStuck e σ (λ _ _, ∃ xl, post xl).
Proof.
  move=> topre totyp. eapply wp_adequacy=> ?. case: (totyp _)=> ?[? typ].
  exists _, _. iIntros "_". rewrite type_unseal in typ.
  iMod (na_alloc (na_invG0:=rust_haltGS_na_inv)) as (t) "t". iModIntro.
  iDestruct (typ $! 1%Qp t (λ _, post) (λ _, ()) with "[//] t [] [//]")
    as "twp".
  { by iApply proph_obs_true. }
  iApply twp_wp. iApply (twp_mono with "twp")=> ?. iIntros "to" (?) "_ W".
  iMod ("to" with "W") as "[_(% & _ & _ & obs & _)]".
  iApply fupd_mask_intro_discard; [done|]. rewrite proph_obs_sat.
  iDestruct "obs" as "[% %]". by iExists _.
Qed.
Theorem type_adeqaucy_int `{!rust_haltGpreS CON Σ, !rust_haltC CON}
  {Xl post pre Γo e σ JUDG} :
  pre post () →
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ type (Yl:=_::Xl) ⊤ ᵖ[] e (λ r, r ◁ ty_int ᵖ:: Γo) pre) →
  adequate NotStuck e σ (λ v _, ∃ (n : Z) xl, v = #n ∧ post (n ᵖ:: xl)).
Proof.
  move=> topre totyp. eapply wp_adequacy=> ?. case: (totyp _)=> ?[? typ].
  exists _, _. iIntros "_". rewrite type_unseal in typ.
  iMod (na_alloc (na_invG0:=rust_haltGS_na_inv)) as (t) "t". iModIntro.
  iDestruct (typ $! 1%Qp t (λ _, post) (λ _, ()) with "[//] t [] [//]")
    as "twp".
  { by iApply proph_obs_true. }
  iApply twp_wp. iApply (twp_mono with "twp")=> ?. iIntros "to" (?) "_ W".
  rewrite /ty_int ty_pty_unseal /=.
  iMod ("to" with "W") as "[_(% & _ & _ & obs & %i & _)]".
  iApply fupd_mask_intro_discard; [done|]. case i=> [?[? +]].
  rewrite of_path_val. move=> [[->][?[eq[->]]]]. rewrite proph_obs_sat.
  iDestruct "obs" as "[%π %]". rewrite -(eq π). by iExists _, _.
Qed.

(** Termination adequacy for a typing judgment *)
Theorem type_total `{!rust_haltGpreS CON Σ} {Xl post pre Γo e σ JUDG} :
  pre post () →
  (∀ `{!rust_haltGS CON Σ}, ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ)),
    ⊢ type (Yl:=Xl) ⊤ ᵖ[] e (λ _, Γo) pre) →
  sn erased_step ([e], σ).
Proof.
  move=> topre totyp. eapply twp_total=> ?. case: (totyp _)=> ?[? typ].
  exists _, _, (λ _, True)%I. iIntros "_". rewrite type_unseal in typ.
  iMod (na_alloc (na_invG0:=rust_haltGS_na_inv)) as (t) "t". iModIntro.
  iDestruct (typ $! 1%Qp t (λ _, post) (λ _, ()) with "[//] t [] [//]")
    as "twp"; [by iApply proph_obs_true|].
  iApply (twp_mono with "twp"). by iIntros.
Qed.
