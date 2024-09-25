(** * Mutex machinery *)

From nola.heap_lang Require Import notation proofmode.
From nola.util Require Import prod.
From nola.bi Require Export deriv.
From nola.iris Require Export iprop inv.
Import ProdNotation iPropAppNotation UpdwNotation WpwNotation DsemNotation.

Implicit Type (b : bool) (l : loc) (n : nat).

(** ** Camera for the mutex machinery *)

Local Definition mutex_fml FML : oFunctor := leibnizO loc * FML.
Class mutexGS FML Σ := mutexGS_inv : inv'GS (mutex_fml FML) Σ.
Local Existing Instances mutexGS_inv.

Class mutexGpreS FML Σ := mutexGpreS_inv : inv'GpreS (mutex_fml FML) Σ.
Local Existing Instances mutexGpreS_inv.
Definition mutexΣ FML `{!oFunctorContractive FML} := #[inv'Σ (mutex_fml FML)].
#[export] Instance subG_mutexΣ
  `{!oFunctorContractive FML, !subG (mutexΣ FML) Σ} : mutexGpreS FML Σ.
Proof. solve_inG. Qed.

(** ** Mutex *)
Section mutex.
  Context `{!mutexGS FML Σ, !heapGS_gen hlc Σ}.
  Implicit Types (sm : FML $oi Σ → iProp Σ) (Px : FML $oi Σ).

  (** [mutex_tok]: Mutex token *)
  Definition mutex_tok l Px : iProp Σ := inv_tok nroot (l, Px).

  (** [mutex_tok] is non-expansive *)
  #[export] Instance mutex_tok_ne {l} : NonExpansive (mutex_tok l).
  Proof. move=> ????. by apply inv_tok_ne. Qed.
  (** [mutex_tok] is persistent *)
  Fact mutex_tok_persistent {l Px} : Persistent (mutex_tok l Px).
  Proof. exact _. Qed.
  (** [mutex_tok] is timeless for discrete formulas *)
  Fact mutex_tok_timeless `{!Discrete Px} {l} : Timeless (mutex_tok l Px).
  Proof. exact _. Qed.

  (** Semantics for a mutex *)
  Local Definition mutex_sem (sm : FML $oi Σ -d> iProp Σ)
    : mutex_fml FML $oi Σ -d> iProp Σ :=
    λ '(l, Px), (∃ b, l ↦ #b ∗ if b then True else sm Px)%I.
  Local Lemma mutex_sem_ne {sm} :
    □ (∀ Px Qx, Px ≡ Qx -∗ sm Px -∗ sm Qx) -∗
      □ (∀ M M', M ≡ M' -∗ mutex_sem sm M -∗ mutex_sem sm M').
  Proof.
    iIntros "#Ne !>" ([??][??]). rewrite prod_equivI /=. iIntros "[<- eqv]".
    iIntros "[%b[$ Px]]". case: b=>//=. iApply ("Ne" with "eqv Px").
  Qed.

  (** World satisfaction for the mutex machinery *)
  Local Definition mutex_wsat_def (sm : FML $oi Σ -d> iProp Σ) : iProp Σ :=
    inv_wsat (mutex_sem sm).
  Local Lemma mutex_wsat_aux : seal mutex_wsat_def. Proof. by eexists. Qed.
  Definition mutex_wsat := mutex_wsat_aux.(unseal).
  Local Lemma mutex_wsat_unseal : mutex_wsat = mutex_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [mutex_wsat] is non-expansive *)
  #[export] Instance mutex_wsat_ne : NonExpansive mutex_wsat.
  Proof.
    rewrite mutex_wsat_unseal /mutex_wsat_def=> ????. f_equiv. case=> ??.
    unfold mutex_sem. solve_proper.
  Qed.
  #[export] Instance mutex_wsat_proper : Proper ((≡) ==> (≡)) mutex_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate a new mutex *)
  Lemma alloc_mutex_tok {sm l Px} :
    l ↦ #false -∗ sm Px =[mutex_wsat sm]=∗ mutex_tok l Px.
  Proof.
    rewrite mutex_wsat_unseal. iIntros "↦ Px".
    iApply (inv_tok_alloc (FML:=mutex_fml _) (l, Px) with "[↦ Px]").
    by iFrame.
  Qed.

  (** Allocate a new mutex with the lock acquired *)
  Lemma alloc_acquire_mutex_tok {sm l Px} :
    l ↦ #true =[mutex_wsat sm]=∗ mutex_tok l Px.
  Proof.
    rewrite mutex_wsat_unseal. iIntros "↦".
    iApply (inv_tok_alloc (FML:=mutex_fml _) (l, Px) with "[↦]").
    iFrame.
  Qed.

  (** Try to acquire the lock on the mutex *)
  Definition try_acquire_mutex : val := λ: "l", CAS "l" #false #true.
  Lemma twp_try_acquire_mutex_tok {sm l Px} :
    [[{ mutex_tok l Px }]][mutex_wsat sm]
      try_acquire_mutex #l
    [[{ b, RET #b; if b then sm Px else True }]].
  Proof.
    rewrite mutex_wsat_unseal. iIntros (Φ) "l →Φ". wp_lam.
    wp_bind (CmpXchg _ _ _).
    iMod (inv_tok_acc (sm:=mutex_sem _) with "l") as "[[%b[↦ big]]cl]";
      [done|]; case b.
    - wp_cmpxchg_fail. iModIntro. iMod ("cl" with "[$↦//]") as "_". iModIntro.
      wp_pures. by iApply "→Φ".
    - wp_cmpxchg_suc. iModIntro. iMod ("cl" with "[$↦//]") as "_". iModIntro.
      wp_pures. by iApply "→Φ".
  Qed.

  (** Try to acquire the lock on the mutex repeatedly with a timeout *)
  Definition try_acquire_loop_mutex : val :=
    rec: "self" "n" "l" :=
      if: "n" = #0 then #false else
      if: try_acquire_mutex "l" then #true else "self" ("n" - #1) "l".
  Lemma twp_try_acquire_loop_mutex_tok {sm l Px n} :
    [[{ mutex_tok l Px }]][mutex_wsat sm]
      try_acquire_loop_mutex #n #l
    [[{ b, RET #b; if b then sm Px else True }]].
  Proof.
    iIntros (Φ) "#l →Φ". iInduction n as [|n] "IH".
    { wp_lam. wp_pures. by iApply "→Φ". }
    wp_lam. wp_pures. wp_apply (twp_try_acquire_mutex_tok with "l").
    iIntros ([|]).
    - iIntros "?". wp_pures. iModIntro. by iApply "→Φ".
    - iIntros "_". wp_pures. have ->: (S n - 1)%Z = n by lia. by iApply "IH".
  Qed.

  (** Release the lock on the mutex *)
  Definition release_mutex : val := λ: "l", "l" <- #false.
  Lemma twp_release_mutex_tok {sm l Px} :
    [[{ mutex_tok l Px ∗ sm Px }]][mutex_wsat sm]
      release_mutex #l
    [[{ RET #(); True }]].
  Proof.
    rewrite mutex_wsat_unseal. iIntros (Φ) "[#l Px] →Φ". wp_lam.
    iMod (inv_tok_acc (sm:=mutex_sem _) with "l") as "[[%[↦ _]]cl]"; [done|].
    wp_store. iModIntro. iMod ("cl" with "[$]") as "_". iModIntro.
    by iApply "→Φ".
  Qed.
End mutex.

(** Allocate [mutex_wsat] *)
Lemma mutex_wsat_alloc' `{!mutexGpreS FML Σ, !heapGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : mutexGS FML Σ,
    ∀ sm, □ (∀ Px Qx, Px ≡ Qx -∗ sm Px -∗ sm Qx) -∗ mutex_wsat sm.
Proof.
  iMod inv_wsat_alloc' as (?) "W". iModIntro. iExists _. iIntros (sm) "Ne".
  rewrite mutex_wsat_unseal. iApply "W". by iApply mutex_sem_ne.
Qed.
Lemma mutex_wsat_alloc `{!mutexGpreS FML Σ, !heapGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : mutexGS FML Σ, ∀ sm, ⌜NonExpansive sm⌝ -∗ mutex_wsat sm.
Proof.
  iMod mutex_wsat_alloc' as (?) "W". iModIntro. iExists _. iIntros (??).
  iApply "W". iIntros "!> %% eqv ?". by iRewrite -"eqv".
Qed.

(** ** Relax a mutex with derivability *)

(** ** [mutex_judgty]: Judgment type for [mutex] *)
Definition mutex_judgty (FM : ofe) : ofe :=
  (FM * FM)%type (** Accessor judgment *).

(** ** [MutexJudg]: Judgment structure for [mutex] *)
Class MutexJudg (FM JUDG : ofe) := MUTEX_JUDG {
  (** Inclusion of [mutex_judgty] *)
  mutex_judg : mutex_judgty FM → JUDG;
  (** [mutex_judg] is non-expansive *)
  mutex_judg_ne :: NonExpansive mutex_judg;
}.
Hint Mode MutexJudg ! - : typeclass_instances.
Arguments MUTEX_JUDG {_ _} _ _.

Section mutex_deriv.
  Context `{!mutexGS FML Σ, !MutexJudg (FML $oi Σ) JUDG}.
  Implicit Type δ : JUDG → iProp Σ.

  (** [mutex]: Relaxed simple invariant *)
  Local Definition mutex_def δ l Px : iProp Σ :=
    ∃ Qx, □ δ (mutex_judg (Px, Qx)) ∗ mutex_tok l Qx.
  Local Lemma mutex_aux : seal mutex_def. Proof. by eexists. Qed.
  Definition mutex := mutex_aux.(unseal).
  Local Lemma mutex_unseal : mutex = mutex_def. Proof. exact: seal_eq. Qed.

  (** [mutex] is persistent *)
  #[export] Instance mutex_persistent {δ l Px} : Persistent (mutex δ l Px).
  Proof. rewrite mutex_unseal. exact _. Qed.

  (** [mutex] is non-expansive *)
  #[export] Instance mutex_ne `{!NonExpansive δ} {l} : NonExpansive (mutex δ l).
  Proof. rewrite mutex_unseal. solve_proper. Qed.
End mutex_deriv.

(** Notation *)
Notation mutexd := (mutex der).
Notation mutex_wsati δ := (mutex_wsat ⟦⟧(δ)).
Notation mutex_wsatid := (mutex_wsati der).

Section mutex_deriv.
  Context `{!mutexGS FML Σ, !heapGS_gen hlc Σ, !MutexJudg (FML $oi Σ) JUDG,
    !Jsem JUDG (iProp Σ), !Dsem JUDG (FML $oi Σ) (iProp Σ)}.
  Implicit Type (δ : JUDG → iProp Σ) (Px Qx : FML $oi Σ).

  (** ** [mutex_judg_sem]: Semantics of [mutex_judgty] *)
  Definition mutex_judg_sem δ (PQx : mutex_judgty (FML $oi Σ)) : iProp Σ :=
    mod_iff (fupd ⊤ ⊤) ⟦ PQx.1 ⟧(δ) ⟦ PQx.2 ⟧(δ).
  (** [mutex_judg_sem] is non-expansive *)
  #[export] Instance mutex_judg_sem_ne `{!NonExpansive δ} :
    NonExpansive (mutex_judg_sem δ).
  Proof. solve_proper. Qed.

  (** [MutexJsem]: Judgment semantics for [mutex] *)
  Class MutexJsem :=
    (** Interpreting [mutex_judg] *)
    sem_mutex_judg : ∀ {δ PQx}, ⟦ mutex_judg PQx ⟧(δ) ⊣⊢ mutex_judg_sem δ PQx.

  Context `{!MutexJsem}.

  (** Unfold [mutexd] *)
  Lemma mutexd_unfold {l Px} :
    mutexd l Px ⊢ ∃ Qx, □ mod_iff (fupd ⊤ ⊤) ⟦ Px ⟧ ⟦ Qx ⟧ ∗ mutex_tok l Qx.
  Proof.
    rewrite mutex_unseal /mutex_def. do 2 f_equiv.
    by rewrite der_sound sem_mutex_judg.
  Qed.

  (** Wrapper lemmas *)
  Lemma twp_try_acquire_mutexd {l Px} :
    [[{ mutexd l Px }]][mutex_wsatid]
      try_acquire_mutex #l
    [[{ b, RET #b; if b then ⟦ Px ⟧ else True }]].
  Proof.
    setoid_rewrite mutexd_unfold. iIntros (?) "[%Qx[#[_ QP]l]] →Φ".
    iApply twp_fupd. wp_apply (twp_try_acquire_mutex_tok (sm:=⟦⟧) with "l").
    iIntros ([|]) "Qx"; iApply "→Φ"; by [iApply "QP"|].
  Qed.
  Lemma twp_try_acquire_loop_mutexd {l Px n} :
    [[{ mutexd l Px }]][mutex_wsatid]
      try_acquire_loop_mutex #n #l
    [[{ b, RET #b; if b then ⟦ Px ⟧ else True }]].
  Proof.
    setoid_rewrite mutexd_unfold. iIntros (?) "[%Qx[#[_ QP]l]] →Φ".
    iApply twp_fupd.
    wp_apply (twp_try_acquire_loop_mutex_tok (sm:=⟦⟧) with "l").
    iIntros ([|]) "Qx"; iApply "→Φ"; by [iApply "QP"|].
  Qed.
  Lemma twp_release_mutexd {l Px} :
    [[{ mutexd l Px ∗ ⟦ Px ⟧ }]][mutex_wsatid]
      release_mutex #l
    [[{ RET #(); True }]].
  Proof.
    setoid_rewrite mutexd_unfold. iIntros (?) "[[%Qx[#[PQ _]l]] Px] →Φ".
    iApply fupd_twp. iMod ("PQ" with "Px") as "Qx". iModIntro.
    by wp_apply (twp_release_mutex_tok (sm:=⟦⟧) with "[$]").
  Qed.

  Context `{!Deriv (JUDG:=JUDG) ih δ}.

  (** Turn [mutex_tok] into [mutex] *)
  Lemma mutex_tok_mutex {l Px} : mutex_tok l Px ⊢ mutex δ l Px.
  Proof.
    rewrite mutex_unseal. iIntros "$ !>". iApply Deriv_factor. iIntros (????).
    rewrite sem_mutex_judg. iSplit; by iIntros.
  Qed.

  (** Wrapper lemmas *)
  Lemma alloc_mutex {l Px} :
    l ↦ #false -∗ ⟦ Px ⟧(δ) =[mutex_wsati δ]=∗ mutex δ l Px.
  Proof. rewrite -mutex_tok_mutex. exact alloc_mutex_tok. Qed.
  Lemma alloc_acquire_mutex {l Px} :
    l ↦ #true =[mutex_wsati δ]=∗ mutex δ l Px.
  Proof. rewrite -mutex_tok_mutex. exact alloc_acquire_mutex_tok. Qed.

  (** Convert [mutex] with [mod_iff] *)
  Lemma mutex_iff' {l Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_iff (fupd ⊤ ⊤) ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      mutex δ l Px -∗ mutex δ l Qx.
  Proof.
    rewrite mutex_unseal. iIntros "#big [%Rx[#iff $]] !>". iApply Deriv_factor.
    iIntros (??? to). rewrite to !sem_mutex_judg.
    iApply (mod_iff_trans with "[] iff"). iApply mod_iff_sym. by iApply "big".
  Qed.
  Lemma mutex_iff {l Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      mod_iff (fupd ⊤ ⊤) ⟦ Px ⟧(δ') ⟦ Qx ⟧(δ')) -∗
      mutex δ l Px ∗-∗ mutex δ l Qx.
  Proof.
    iIntros "big"; iSplit; iApply mutex_iff'; [done|]. iStopProof. do 6 f_equiv.
    apply mod_iff_sym.
  Qed.
End mutex_deriv.
Arguments MutexJsem FML Σ {_ _} JUDG {_ _ _}.
Hint Mode MutexJsem ! - - - - - - - : typeclass_instances.
