(** * Iris preliminaries *)

From nola.examples.type Require Export type.
From nola.util Require Export prod.
From nola.iris Require Export sintp inv wp.
From nola.examples.heap_lang Require Export primitive_laws.
From iris.proofmode Require Import proofmode.
Import EqNotations.

(** ** Iris resources for invariant *)

(** Data for invariant *)
Definition tinvd i : Type := loc *' type i (;ᵞ).

(** [tinvGS']: Product of [ninvGS (tinvd ?) Σ] over [[o..o+i]] *)
Fixpoint tinvGS' (L o : nat) Σ : Type :=
  match L with
  | 0 => unit
  | S L => ninvGS (tinvd o) Σ *' tinvGS' L (S o) Σ
  end.
Existing Class tinvGS'.
Notation tinvGS L Σ := (tinvGS' L 0 Σ).
#[export] Instance tinvGS'_S_ninvGS' {L o} `{tΣ : !tinvGS' (S L) o Σ}
  : ninvGS (tinvd o) Σ := tΣ.1'.
#[export] Instance tinvGS'_S_tinvGS' {L o} `{tΣ : !tinvGS' (S L) o Σ}
  : tinvGS' L (S o) Σ := tΣ.2'.

(** Get [ninvGS] out of [tinvGS] *)
Fixpoint tinvGS'_ninvGS {i L o Σ}
  : tinvGS' L o Σ → i <ⁿ L → ninvGS (tinvd (i +' o)) Σ :=
  match i, L with
  | _, 0 => λ _ _, nlt_no0
  | 0, S _ => λ _ _, _
  | S i, S L => λ _ iL, tinvGS'_ninvGS _ (nlt_unS iL)
  end.
#[export] Existing Instance tinvGS'_ninvGS.
Definition ninvGS_rew `{nΣ : ninvGS (tinvd i) Σ} {j} (eq : i = j)
  : ninvGS (tinvd j) Σ := rew[λ _, _] eq in nΣ.
#[export] Instance tinvGS_ninvGS `{!tinvGS L Σ, ! i <ⁿ L}
  : ninvGS (tinvd i) Σ := ninvGS_rew add'_0_r_d.

(** ** World satisfaction for invariant *)
Section tinv_wsat'.
  Context `{!heapGS_gen HasNoLc Σ}.

  Fixpoint tinv_wsat'' (L M o : nat) : tinvGS' L o Σ →
    discrete_fun (λ i, i <ⁿ M -d> type (i +' o) (;ᵞ) -d> val -d> iProp Σ) →
    iProp Σ :=
    match L, M with
    | _, 0 => λ _ _, True
    | 0, S _ => λ _ _, False
    | S L, S M => λ _ intp,
        ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp 0 _ T v) ∗
        tinv_wsat'' L M (S o) _ (λ i _ T, intp (S i) _ T)
    end%I.
  Definition tinv_wsat' `{!tinvGS L Σ} (M : nat)
    (intp : discrete_fun (λ i, i <ⁿ M -d> type i (;ᵞ) -d> val -d> iProp Σ))
    : iProp Σ :=
    tinv_wsat'' L M 0 _ (λ i _ T, intp i _ (rew[λ i, _ i _] add'_0_r_d in T)).

  (** [tinv_wsat'] is non-expansive *)
  #[export] Instance tinv_wsat''_ne {L M o tΣ} :
    NonExpansive (tinv_wsat'' L M o tΣ).
  Proof.
    move: L M o tΣ. fix FIX 2=> L M.
    case: L M=> [|L][|M]//= ????? eq. do 2 f_equiv=> >; [|apply eq].
    do 3 f_equiv. apply eq.
  Qed.
  #[export] Instance tinv_wsat'_ne `{!tinvGS L Σ} {M} :
    NonExpansive (tinv_wsat' M).
  Proof. move=> ??? eq. apply tinv_wsat''_ne=> >. apply eq. Qed.

  (** Take out [ninv_wsat] out of [tinv_wsat'] *)
  Lemma tinv_wsat''_ninv_wsat
    `{tΣ : !tinvGS' L o Σ, iM : ! i <ⁿ M, iL : ! i <ⁿ L} {intp} :
    tinv_wsat'' L M o _ intp -∗
      ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp i _ T v) ∗
      (ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp i _ T v) -∗
        tinv_wsat'' L M o _ intp).
  Proof.
    move: L M i o tΣ iM iL intp. fix FIX 3=> L M i.
    case: L M i=> [|L][|M][|i]/=; try (unfold nlt; lia);
      iIntros (?? iM ??) "[nw tw]".
    { rewrite (proof_irrel nlt_0 iM). iFrame. by iIntros. }
    iFrame "nw".
    iDestruct (FIX L M i _ _ (nlt_unS iM) with "tw") as "?".
    by rewrite (proof_irrel (nlt_S _) iM).
  Qed.
  (** Key equality hack for [tinv_wsat'_ninv_wsat] *)
  Local Lemma ninv_wsat_rew `{nΣ : !ninvGS (tinvd i) Σ, ! j <ⁿ M} (eq : i = j)
    {intp : ∀ k, k <ⁿ M → type k (;ᵞ) → val → iProp Σ} :
    ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp j _ (rew[λ i, _ i _] eq in T) v) ⊣⊢
      ninv_wsat (ninvGS0:=ninvGS_rew eq)
        (λ '(l, T)', ∃ v, l ↦ v ∗ intp j _ T v).
  Proof. by subst. Qed.
  Lemma tinv_wsat'_ninv_wsat `{!tinvGS L Σ, ! i <ⁿ M, ! i <ⁿ L} {intp} :
    tinv_wsat' M intp -∗
      ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp i _ T v) ∗
      (ninv_wsat (λ '(l, T)', ∃ v, l ↦ v ∗ intp i _ T v) -∗
        tinv_wsat' M intp).
  Proof.
    iIntros "tw". iDestruct (tinv_wsat''_ninv_wsat with "tw") as "[??]".
    rewrite ninv_wsat_rew /=. iFrame.
  Qed.

  (** Expansion between [tinv_wsat']s *)
  Lemma tinv_wsat''_expand {L M M' o tΣ intp intp'} :
    (∀ i iM iM', intp i iM ≡ intp' i iM') → M ≤ M' →
    tinv_wsat'' L M' o tΣ intp' -∗ tinv_wsat'' L M o tΣ intp ∗
      (tinv_wsat'' L M o tΣ intp -∗ tinv_wsat'' L M' o tΣ intp').
  Proof.
    move: L M M' o tΣ intp intp'. fix FIX 3=> L M M'.
    case: L M M'=> [|L][|M][|M']/=; try (lia || by move=> *; iIntros "$").
    iIntros (???? eq ?) "[nw tw]".
    iDestruct (FIX with "tw") as "[$ cl]"; [by move=> *?; apply eq|lia|].
    iSplitL "nw".
    { iStopProof. apply bi.equiv_entails. do 3 f_equiv=> >. apply eq. }
    iFrame. iIntros "[nw ?]". iSplitL "nw"; [|by iApply "cl"]. iStopProof.
    apply bi.equiv_entails. do 3 f_equiv=> >. symmetry. apply eq.
  Qed.
  Lemma tinv_wsat'_expand `{!tinvGS L Σ, ! M ≤ⁿ M'} {intp intp'} :
    (∀ i iM iM', intp i iM ≡ intp' i iM') →
    tinv_wsat' M' intp' -∗ tinv_wsat' M intp ∗
      (tinv_wsat' M intp -∗ tinv_wsat' M' intp').
  Proof. move=> eq. iApply tinv_wsat''_expand; [|done]=> >. apply eq. Qed.
End tinv_wsat'.

(** [tintpGS]: Iris resource *)
Class tintpGS (L : nat) (Σ : gFunctors) := TintpGS {
  tintpGS_tinvGS :: tinvGS L Σ;
  tintpGS_heapGS :: heapGS_gen HasNoLc Σ;
}.
Arguments TintpGS {_} _ _.

(** ** Strong interpretation structure *)

(** [intps] for [type]

  Later we interpret [sigT tinvd] as an accessor *)
Definition tintps Σ : intps := Intps unit (λ _, sigT tinvd) (iProp Σ).

(** Notation for [tintps] *)
Notation tsintp_ty Σ := (sintp_ty (tintps Σ)).
Notation "⸨ Tx ⸩ ( s )" := (sunwrap s (Sarg () Tx))
  (format "'[' ⸨  Tx  ⸩ '/  ' ( s ) ']'") : nola_scope.

(** [tinv]: [ninv] in the accessor style *)
Definition tinv {Σ} (s : tsintp_ty Σ) (i : nat) (l : loc) (T : type i (;ᵞ))
  : iProp Σ := □ ⸨ existT i (l, T)' ⸩(s).
