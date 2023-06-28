(** * Iris preliminaries *)

From nola.examples.type Require Export type.
From nola.util Require Export prod.
From nola.iris Require Export sintp inv wp.
From nola.examples.heap_lang Require Export primitive_laws.
From iris.proofmode Require Export proofmode.
Import EqNotations.

(** ** Iris resources for invariant *)

(** Data for invariant *)
Variant tinvd i : Type :=
| (** Reference **) tinvd_ref (l : loc) (T : type i (;ᵞ))
| (** Guard **) tinvd_guard (T : type i (;ᵞ)) (v : val).
Arguments tinvd_ref {_} _ _.
Arguments tinvd_guard {_} _ _.

(** [tinvGS']: Product of [ninvGS (tinvd ?) Σ] over [[o..o+i]] *)
Fixpoint tinvGS' (L o : nat) Σ : Type :=
  match L with 0 => unit | S L =>
    ninvGS (tinvd o) Σ *' tinvGS' L (S o) Σ
  end.
Arguments tinvGS' : simpl never.
Existing Class tinvGS'.
Notation tinvGS L Σ := (tinvGS' L 0 Σ).
#[export] Instance tinvGS'_S_ninvGS' `{tΣ : !tinvGS' (S L) o Σ}
  : ninvGS (tinvd o) Σ := tΣ.1'.
#[export] Instance tinvGS'_S_tinvGS' `{tΣ : !tinvGS' (S L) o Σ}
  : tinvGS' L (S o) Σ := tΣ.2'.

(** Get [ninvGS] out of [tinvGS] *)
Fixpoint tinvGS'_ninvGS {L i o Σ}
  : tinvGS' L o Σ → i <ⁿ L → ninvGS (tinvd (i +' o)) Σ :=
  match L with 0 => λ _ _, nlt_no0 | S _ =>
    match i with 0 => λ _ _, _ | S _ =>
      λ _ iL, tinvGS'_ninvGS _ (nlt_unS iL)
    end
  end.
Arguments tinvGS'_ninvGS : simpl never.
#[export] Existing Instance tinvGS'_ninvGS.
Definition ninvGS_rew `{nΣ : ninvGS (tinvd i) Σ} {j} (eq : i = j)
  : ninvGS (tinvd j) Σ := rew[λ _, _] eq in nΣ.
#[export] Instance tinvGS_ninvGS `{!tinvGS L Σ, ! i <ⁿ L}
  : ninvGS (tinvd i) Σ := ninvGS_rew add'_0_r.

(** ** World satisfaction for invariant *)
Section tinv_wsat'.
  Context `{!heapGS_gen HasNoLc Σ}.

  (** Interpretation of [tinvd] *)
  Definition tinvd_intp {i} (intp : type i (;ᵞ) -d> val -d> iProp Σ)
    : tinvd i -d> iProp Σ :=
    λ Tx, match Tx with
    | tinvd_ref l T => ∃ v, l ↦ v ∗ intp T v
    | tinvd_guard T v => intp T v
    end%I.

  (** [tinvd_intp] is non-expansive *)
  #[export] Instance tinvd_intp_ne {n i} :
    Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) (tinvd_intp (i:=i)).
  Proof. solve_proper. Qed.
  #[export] Instance tinvd_intp_proper {i} :
    Proper ((≡) ==> (=) ==> (≡)) (tinvd_intp (i:=i)).
  Proof. solve_proper. Qed.

  (** [tinv_wsat']: World satisfaction for invariant *)
  Fixpoint tinv_wsat'' (L M o : nat) : tinvGS' L o Σ →
    discrete_fun (λ i, i <ⁿ M -d> type (i +' o) (;ᵞ) -d> val -d> iProp Σ) →
    iProp Σ :=
    match M with 0 => λ _ _, True | S M =>
      match L with 0 => λ _ _, False | S L => λ _ intp,
        ninv_wsat (tinvd_intp (intp 0 _)) ∗
        tinv_wsat'' L M (S o) _ (λ i _ T, intp (S i) _ T)
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

  (** Take out [ninv_wsat] out of [tinv_wsat'] *)
  Lemma tinv_wsat''_ninv_wsat
    `{tΣ : !tinvGS' L o Σ, iM : ! i <ⁿ M, iL : ! i <ⁿ L} {intp} :
    tinv_wsat'' L M o _ intp -∗ ninv_wsat (tinvd_intp (intp i _)) ∗
      (ninv_wsat (tinvd_intp (intp i _)) -∗ tinv_wsat'' L M o _ intp).
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
    ninv_wsat (tinvd_intp (λ T, intp j _ (rew[λ i, _ i _] eq in T))) ⊣⊢
      ninv_wsat (ninvGS0:=ninvGS_rew eq) (tinvd_intp (intp j _)).
  Proof. by subst. Qed.
  Lemma tinv_wsat'_ninv_wsat `{!tinvGS L Σ, ! i <ⁿ M, ! i <ⁿ L} {intp} :
    tinv_wsat' M intp -∗ ninv_wsat (tinvd_intp (intp i _)) ∗
      (ninv_wsat (tinvd_intp (intp i _)) -∗ tinv_wsat' M intp).
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
    { iStopProof. apply bi.equiv_entails. do 2 f_equiv=> >. apply eq. }
    iFrame. iIntros "[nw ?]". iSplitL "nw"; [|by iApply "cl"]. iStopProof.
    apply bi.equiv_entails. do 2 f_equiv=> >. symmetry. apply eq.
  Qed.
  Lemma tinv_wsat'_expand `{!tinvGS L Σ, ! M ≤ⁿ M'} {intp intp'} :
    (∀ i iM iM', intp i iM ≡ intp' i iM') →
    tinv_wsat' M' intp' -∗ tinv_wsat' M intp ∗
      (tinv_wsat' M intp -∗ tinv_wsat' M' intp').
  Proof. move=> eq. iApply tinv_wsat''_expand; [|done]=> >. apply eq. Qed.
End tinv_wsat'.
Arguments tinv_wsat'' : simpl never.

(** [tintpGS]: Iris resource *)
Class tintpGS (L : nat) (Σ : gFunctors) := TintpGS {
  tintpGS_tinvGS :: tinvGS L Σ;
  tintpGS_heapGS :: heapGS_gen HasNoLc Σ;
}.
Arguments TintpGS {_} _ _.

(** ** Strong interpretation structure *)

(** [intps] for [type] *)
Definition tintps Σ : intps := Intps unit (λ _, sigT tinvd) (iProp Σ).

(** Notation for [tintps] *)
Notation tsintp_ty Σ := (sintp_ty (tintps Σ)).
Notation "⸨ Tx ⸩ ( s )" := (sunwrap s (Sarg () (existT _ Tx)))
  (format "'[' ⸨  Tx  ⸩ '/  ' ( s ) ']'") : nola_scope.

(** [tref]: Proposition for [t_ref] *)
Definition tref {Σ i} (s : tsintp_ty Σ) (l : loc) (T : type i (;ᵞ))
  : iProp Σ := □ ⸨ tinvd_ref l T ⸩(s).
(** [tguard]: Proposition for [t_guard] *)
Definition tguard {Σ i} (s : tsintp_ty Σ) (T : type i (;ᵞ)) (v : val)
  : iProp Σ := □ ⸨ tinvd_guard T v ⸩(s).
