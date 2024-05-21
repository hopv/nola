(** * Lock machinery *)

From nola.heap_lang Require Import notation proofmode.
From nola.util Require Import prod.
From nola.iris Require Export ofe inv.
Import ProdNotation iPropAppNotation UpdwNotation WpwNotation.

(** ** Camera for the lock machinery *)

Local Definition lock_prop PROP : oFunctor := leibnizO loc * PROP.
Class lockGS PROP Σ := lockGS_inv : inv'GS (lock_prop PROP) Σ.
Local Existing Instances lockGS_inv.

Class lockGpreS PROP Σ := lockGpreS_inv : inv'GpreS PROP Σ.
Local Existing Instances lockGpreS_inv.
Definition lockΣ PROP `{!oFunctorContractive PROP} := #[inv'Σ PROP].
#[export] Instance subG_lockΣ
  `{!oFunctorContractive PROP, !subG (lockΣ PROP) Σ} : lockGpreS PROP Σ.
Proof. solve_inG. Qed.

(** **  lock *)
Section lock.
  Context `{!heapGS_gen hlc Σ, !lockGS PROP Σ}.
  Implicit Types (P : PROP $oi Σ) (b : bool) (l : loc) (n : nat).

  (** [lock_tok]: Lock token *)
  Definition lock_tok l P : iProp Σ := inv_tok nroot (l, P).

  (** [lock_tok] is persistent *)
  Fact lock_tok_persistent {l P} : Persistent (lock_tok l P).
  Proof. exact _. Qed.
  (** [lock_tok] is timeless if the underlying OFE is discrete *)
  Fact lock_tok_timeless `{!OfeDiscrete (PROP $oi Σ)} {l P} :
    Timeless (lock_tok l P).
  Proof. exact _. Qed.

  (** Interpretation for a lock *)
  Local Definition lock_intp (intp : PROP $oi Σ -d> iProp Σ)
    : lock_prop PROP $oi Σ -d> iProp Σ := λ '(l, P),
    (∃ b, l ↦ #b ∗ if b then True else intp P)%I.
  #[export] Instance lock_intp_ne `{!NonExpansive intp} :
    NonExpansive (lock_intp intp).
  Proof. move=> ?[??][??][/=??]. solve_proper. Qed.

  (** World satisfaction for the lock machinery *)
  Local Definition lock_wsat_def (intp : PROP $oi Σ -d> iProp Σ) : iProp Σ :=
    inv_wsat (lock_intp intp).
  Local Lemma lock_wsat_aux : seal lock_wsat_def. Proof. by eexists. Qed.
  Definition lock_wsat := lock_wsat_aux.(unseal).
  Local Lemma lock_wsat_unseal : lock_wsat = lock_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [lock_wsat] is non-expansive *)
  #[export] Instance lock_wsat_ne : NonExpansive lock_wsat.
  Proof.
    rewrite lock_wsat_unseal /lock_wsat_def=> ????. f_equiv. case=> ??.
    unfold lock_intp. solve_proper.
  Qed.
  #[export] Instance lock_wsat_proper : Proper ((≡) ==> (≡)) lock_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate a lock *)
  Definition newlock : val := λ: <>, ref #false.
  Lemma twp_newlock {intp P} :
    [[{ intp P }]][lock_wsat intp]
      newlock #()
    [[{ l, RET #l; lock_tok l P }]].
  Proof.
    rewrite lock_wsat_unseal. iIntros (Φ) "P →Φ". wp_lam.
    iApply twpw_fupdw_nonval; [done|]. wp_alloc l as "↦". iModIntro.
    iMod (inv_tok_alloc (PROP:=lock_prop _) (l, P) with "[↦ P]") as "l".
    { by iFrame. }
    iModIntro. by iApply ("→Φ" with "l").
  Qed.

  (** Try to acquire a lock *)
  Definition try_acquire : val := λ: "l", CAS "l" #false #true.
  Lemma twp_try_acquire `{!NonExpansive intp} {l P} :
    [[{ lock_tok l P }]][lock_wsat intp]
      try_acquire #l
    [[{ b, RET #b; if b then intp P else True }]].
  Proof.
    rewrite lock_wsat_unseal. iIntros (Φ) "l →Φ". wp_lam.
    wp_bind (CmpXchg _ _ _).
    iMod (inv_tok_acc (intp:=lock_intp _) with "l") as "[[%b[↦ big]]cl]";
      [done|]; case b.
    - wp_cmpxchg_fail. iModIntro. iMod ("cl" with "[$↦//]") as "_". iModIntro.
      wp_pures. by iApply "→Φ".
    - wp_cmpxchg_suc. iModIntro. iMod ("cl" with "[$↦//]") as "_". iModIntro.
      wp_pures. by iApply "→Φ".
  Qed.

  (** Acquire a lock with a timeout *)
  Definition acquire_loop : val :=
    rec: "acquire" "n" "l" :=
      if: "n" = #0 then #false else
      if: try_acquire "l" then #true else "acquire" ("n" - #1) "l".
  Lemma twp_acquire_loop `{!NonExpansive intp} {l P n} :
    [[{ lock_tok l P }]][lock_wsat intp]
      acquire_loop #n #l
    [[{ b, RET #b; if b then intp P else True }]].
  Proof.
    iIntros (Φ) "#l →Φ". iInduction n as [|n] "IH".
    { wp_lam. wp_pures. by iApply "→Φ". }
    wp_lam. wp_pures. wp_apply (twp_try_acquire with "l"). iIntros ([|]).
    - iIntros "?". wp_pures. iModIntro. by iApply "→Φ".
    - iIntros "_". wp_pures. have ->: (S n - 1)%Z = n by lia. by iApply "IH".
  Qed.

  (** Release a lock *)
  Definition release : val := λ: "l", "l" <- #false.
  Lemma twp_release `{!NonExpansive intp} {l P} :
    [[{ lock_tok l P ∗ intp P }]][lock_wsat intp]
      release #l
    [[{ RET #(); True }]].
  Proof.
    rewrite lock_wsat_unseal. iIntros (Φ) "[#l P] →Φ". wp_lam.
    iMod (inv_tok_acc (intp:=lock_intp _) with "l") as "[[%b[↦ _]]cl]"; [done|].
    wp_store. iModIntro. iMod ("cl" with "[$]") as "_". iModIntro.
    by iApply "→Φ".
  Qed.
End lock.
