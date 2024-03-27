(** * Iris preliminaries *)

From nola.examples.type Require Export type.
From nola.util Require Export prod.
From nola.iris Require Export deriv inv wp.
From nola.examples.heap_lang Require Export definitions.
From iris.proofmode Require Export proofmode.
Import EqNotations.

(** ** Iris resources for invariant *)

(** Data for invariant *)
Variant tinvd i : Type :=
(** Guard **)
| tinvd_guard (T : type i (;ᵞ)) (v : val)
(** Reference **)
| tinvd_ref (l : loc) (T : type i (;ᵞ)).
Arguments tinvd_guard {_} _ _.
Arguments tinvd_ref {_} _ _.

Local Set Warnings "-redundant-canonical-projection".
Canonical tinvdO i := leibnizO (tinvd i).
Local Set Warnings "redundant-canonical-projection".

(** [tinvGS']: Product of [ninvGS (tinvdO ?) Σ] over [[o..L+o]] *)
Fixpoint tinvGS' (L o : nat) Σ : Type :=
  match L with 0 => unit | S L =>
    ninvGS (tinvdO o) Σ *' tinvGS' L (S o) Σ
  end.
Existing Class tinvGS'.
Notation tinvGS L Σ := (tinvGS' L 0 Σ).

(** Get [ninvGS] out of [tinvGS] *)
Fixpoint tinvGS'_ninvGS {o Σ L i}
  : tinvGS' L o Σ → i <ⁿ L → ninvGS (tinvdO (i +' o)) Σ :=
  match L with 0 => λ _ _, nlt_no0 | S L =>
    match i with 0 => λ '(_,_)' _, _ | S i =>
      λ '(_,tΣ)' iL, tinvGS'_ninvGS tΣ (nlt_unS iL)
    end
  end.
#[export] Existing Instance tinvGS'_ninvGS.
Definition ninvGS_rew `{nΣ : ninvGS (tinvdO i) Σ} {j} (eq : i = j)
  : ninvGS (tinvdO j) Σ := rew[λ _, _] eq in nΣ.
#[export] Instance tinvGS_ninvGS `{!tinvGS L Σ, ! i <ⁿ L}
  : ninvGS (tinvdO i) Σ := ninvGS_rew add'_0_r.

(** ** World satisfaction for invariant *)
Section tinv_wsat'.
  Context `{!heapGS_gen HasNoLc Σ}.

  (** Interpretation of [tinvd] *)
  Definition tinvd_intp {i} (intp : type i (;ᵞ) -d> val -d> iProp Σ)
    : tinvdO i -d> iProp Σ :=
    λ Tx, match Tx with
    | tinvd_guard T v => intp T v
    | tinvd_ref l T => ∃ v, l ↦ v ∗ intp T v
    end%I.

  (** [tinvd_intp] is non-expansive *)
  #[export] Instance tinvd_intp_ne {i} : NonExpansive2 (tinvd_intp (i:=i)).
  Proof. solve_proper. Qed.
  #[export] Instance tinvd_intp_proper {i} :
    Proper ((≡) ==> (≡) ==> (≡)) (tinvd_intp (i:=i)).
  Proof. solve_proper. Qed.

  (** [tinv_wsat']: World satisfaction for invariant *)
  Fixpoint tinv_wsat'' (L M o : nat) : tinvGS' L o Σ →
    discrete_fun (λ i, i <ⁿ M -d> type (i +' o) (;ᵞ) -d> val -d> iProp Σ) →
    iProp Σ :=
    match M with 0 => λ _ _, True | S M =>
      match L with 0 => λ _ _, False | S L => λ '(_,tΣ)' intp,
        inv_wsat (tinvd_intp (intp 0 _)) ∗
        tinv_wsat'' L M (S o) tΣ (λ i _ T, intp (S i) _ T)
      end
    end%I.
  Definition tinv_wsat' `{!tinvGS L Σ} (M : nat)
    (intp : discrete_fun (λ i, i <ⁿ M -d> type i (;ᵞ) -d> val -d> iProp Σ))
    : iProp Σ :=
    tinv_wsat'' L M 0 _ (λ i _ T, intp i _ (rew[λ i, _ i _] add'_0_r in T)).

  (** [tinv_wsat'] is non-expansive *)
  #[export] Instance tinv_wsat''_ne {L M o tΣ} :
    NonExpansive (tinv_wsat'' L M o tΣ).
  Proof.
    move: L M o tΣ. fix FIX 2=> L M.
    case: L M=> [|L][|M]//= ????? eq. do 2 f_equiv=> >; [|apply eq].
    f_equiv=> >. apply eq.
  Qed.
  #[export] Instance tinv_wsat'_ne `{!tinvGS L Σ} {M} :
    NonExpansive (tinv_wsat' M).
  Proof. move=> ??? eq. apply tinv_wsat''_ne=> >. apply eq. Qed.
  #[export] Instance tinv_wsat''_proper {L M o tΣ} :
    Proper ((≡) ==> (≡)) (tinv_wsat'' L M o tΣ).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance tinv_wsat'_proper `{!tinvGS L Σ} {M} :
    Proper ((≡) ==> (≡)) (tinv_wsat' M).
  Proof. apply ne_proper, _. Qed.

  (** Take out [inv_wsat] out of [tinv_wsat'] *)
  Lemma tinv_wsat''_inv_wsat
    `{tΣ : !tinvGS' L o Σ, iM : ! i <ⁿ M, iL : ! i <ⁿ L} {intp} :
    tinv_wsat'' L M o _ intp -∗ inv_wsat (tinvd_intp (intp i _)) ∗
      (inv_wsat (tinvd_intp (intp i _)) -∗ tinv_wsat'' L M o _ intp).
  Proof.
    move: L M i o tΣ iM iL intp. fix FIX 3=> L M i.
    case: L M i=> [|L][|M][|i]/=; try nlia; iIntros (?? iM ??) "[nw tw]".
    { rewrite (proof_irrel nlt_0 iM). iFrame. by iIntros. }
    iFrame "nw".
    iDestruct (FIX L M i _ _ (nlt_unS iM) with "tw") as "?".
    by rewrite (proof_irrel (nlt_S _) iM).
  Qed.
  (** Key equality hack for [tinv_wsat'_inv_wsat] *)
  Local Lemma inv_wsat_rew `{nΣ : !ninvGS (tinvdO i) Σ, ! j <ⁿ M} (eq : i = j)
    {intp : ∀ k, k <ⁿ M → type k (;ᵞ) → val → iProp Σ} :
    inv_wsat (tinvd_intp (λ T, intp j _ (rew[λ i, _ i _] eq in T))) ⊣⊢
      inv_wsat (ninvGS0:=ninvGS_rew eq) (tinvd_intp (intp j _)).
  Proof. by subst. Qed.
  Lemma tinv_wsat'_inv_wsat `{!tinvGS L Σ, ! i <ⁿ M, ! i <ⁿ L} {intp} :
    tinv_wsat' M intp -∗ inv_wsat (tinvd_intp (intp i _)) ∗
      (inv_wsat (tinvd_intp (intp i _)) -∗ tinv_wsat' M intp).
  Proof.
    iIntros "tw". iDestruct (tinv_wsat''_inv_wsat with "tw") as "[??]".
    rewrite inv_wsat_rew /=. iFrame.
  Qed.

  (** Inclusion between [tinv_wsat']s *)
  Lemma tinv_wsat''_incl {L M M' o tΣ intp intp'} :
    (∀ i iM iM', intp i iM ≡ intp' i iM') → M ≤ M' →
    tinv_wsat'' L M' o tΣ intp' -∗ tinv_wsat'' L M o tΣ intp ∗
      (tinv_wsat'' L M o tΣ intp -∗ tinv_wsat'' L M' o tΣ intp').
  Proof.
    move: L M M' o tΣ intp intp'. fix FIX 3=> L M M'.
    case: L M M'=> [|L][|M][|M']/=; try (lia || by move=> *; iIntros "$").
    iIntros (???? eq ?) "[nw tw]".
    iDestruct (FIX with "tw") as "[$ cl]"; [by move=> *?; apply eq|lia|].
    iSplitL "nw".
    { iStopProof. apply bi.equiv_entails. do 2 f_equiv=> >. apply eq. }
    iFrame. iIntros "[nw ?]". iSplitL "nw"; [|by iApply "cl"]. iStopProof.
    apply bi.equiv_entails. do 2 f_equiv=> >. symmetry. apply eq.
  Qed.
  Lemma tinv_wsat'_incl `{!tinvGS L Σ, ! M ≤ⁿ M'} {intp intp'} :
    (∀ i iM iM', intp i iM ≡ intp' i iM') →
    tinv_wsat' M' intp' -∗ tinv_wsat' M intp ∗
      (tinv_wsat' M intp -∗ tinv_wsat' M' intp').
  Proof. move=> eq. iApply tinv_wsat''_incl; [|done]=> >. apply eq. Qed.

  (** Eliminate [tinv_wsat'] under [L <ⁿ M] *)
  Lemma tinv_wsat''_over `{tΣ : !tinvGS' L o Σ, LM : ! L <ⁿ M} {intp} :
    tinv_wsat'' L M o _ intp ⊢ False.
  Proof.
    move: L M o tΣ LM intp. fix FIX 2=> L M. case: L M=> [|L][|M]//=; try nlia.
    move=>/= o ???. iIntros "[_ tw]". iDestruct (FIX with "tw") as "[]".
    by apply nlt_unS.
  Qed.
  Lemma tinv_wsat'_over `{!tinvGS L Σ, ! L <ⁿ M} {intp} :
    tinv_wsat' M intp ⊢ False.
  Proof. apply tinv_wsat''_over. Qed.

  (** Get inequality out of [tinv_wsat'] *)
  Lemma tinv_wsat'_le `{!tinvGS L Σ} {M intp} : tinv_wsat' M intp ⊢ ⌜M ≤ⁿ L⌝.
  Proof.
    case (nlt_or_nle (m:=L) (n:=M)); [|by iIntros]=> ?.
    rewrite tinv_wsat'_over. by iIntros.
  Qed.
  Lemma fupdw_tinv_wsat'_le `{!tinvGS L Σ} {M intp E E' P} :
    (⌜M ≤ⁿ L⌝ =[tinv_wsat' M intp]{E,E'}=∗ P)
      =[tinv_wsat' M intp]{E,E'}=∗ P.
  Proof.
    iIntros "→P". iApply fupdw_trans. iIntros "tw".
    iDestruct (tinv_wsat'_le with "tw") as %?. iFrame "tw". by iApply "→P".
  Qed.
End tinv_wsat'.
Arguments tinv_wsat'' : simpl never.

(** [tintpGS]: Iris resource *)
Class tintpGS (L : nat) Σ := TintpGS {
  tintpGS_tinvGS :: tinvGS L Σ;
  tintpGS_heapGS :: heapGS_gen HasNoLc Σ;
}.
Arguments TintpGS {_ _} _ _.

(** ** Derivability structure *)

(** [derivs] for [type] *)
Canonical tderivs Σ : derivs := Derivs (sigT tinvd) (iProp Σ).

(** Notation for [tderivs] *)
Notation tderiv_ty Σ := (deriv_ty (tderivs Σ)).
Notation "⸨ Tx ⸩ ( s )" := (dunwrap s (existT _ Tx))
  (format "'[' ⸨  Tx  ⸩ '/  ' ( s ) ']'") : nola_scope.

(** [tguard]: Proposition for [t_guard] *)
Definition tguard {Σ i} (s : tderiv_ty Σ) (T : type i (;ᵞ)) (v : val) : iProp Σ
  := □ ⸨ tinvd_guard T v ⸩(s).

(** [tref]: Proposition for [t_ref] *)
Definition tref {Σ i} (s : tderiv_ty Σ) (l : loc) (T : type i (;ᵞ)) : iProp Σ
  := □ ⸨ tinvd_ref l T ⸩(s).
