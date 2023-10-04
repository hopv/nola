(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola.iris Require Export deriv inv na_inv wp.
From iris.base_logic.lib Require Export cancelable_invariants.
From nola.examples.heap_lang Require Export definitions.

(** ** Iris resources *)

(** Data for invariant *)
Variant nInvd : Type :=
| (* usual *) nInvd_u (P : nPropS (;ᵞ))
| (* non-atomic *) nInvd_na
    (p : na_inv_pool_name) (i : positive) (P : nPropS (;ᵞ)).

(** Agreement *)
Class agreeG A Σ := agree_inG :: inG Σ (agreeR (leibnizO A)).
Definition agreeΣ A : gFunctors := GFunctor (agreeR (leibnizO A)).
#[export] Instance subG_agreeΣ `{!subG (agreeΣ A) Σ} : agreeG A Σ.
Proof. solve_inG. Qed.

(** [nintpGS]: Iris resource *)
Class nintpGS Σ := NintpGS {
  nintpGS_agreeG :: agreeG (nPropL (;ᵞ)) Σ;
  nintpGS_ninvGS :: ninvGS nInvd Σ;
  nintpGS_na_invG :: na_invG Σ;
  nintpGS_cinvG :: cinvG Σ;
  nintpGS_heapGS :: heapGS_gen HasNoLc Σ;
}.
Arguments NintpGS {_} _ _ _ _ _.

Section nInvd_intp.
  Context `{!nintpGS Σ}.

  (** Interpret [nInvd] *)
  Definition nInvd_intp (intp : nPropS (;ᵞ) -d> iProp Σ) : nInvd -d> iProp Σ :=
    λ Px, match Px with
    | nInvd_u P => intp P
    | nInvd_na p i P => na_body p i (intp P)
    end.
  #[export] Instance nInvd_intp_ne : NonExpansive nInvd_intp.
  Proof. solve_proper. Qed.
End nInvd_intp.

(** [ninv_wsat] for [nInvd] *)
Notation ninv_wsat' intp := (ninv_wsat (nInvd_intp intp)).

(** ** Derivability structure *)

(** [derivs] for [nPropL] *)
Definition nderivs Σ : derivs := Derivs unit (λ _, nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nderivs] *)
Notation nderiv_ty Σ := (deriv_ty (nderivs Σ)).
Notation "⸨ P ⸩ ( δ )" := (dunwrap δ (Darg () P%n))
  (format "'[' ⸨  P  ⸩ '/  ' ( δ ) ']'") : nola_scope.

Section iris.
  Context (* Iris resources *) {Σ : gFunctors}.

  Definition nag `{!agreeG (nPropL (;ᵞ)) Σ}
    (γ : gname) (P : nPropL (;ᵞ)) : iProp Σ :=
    own γ (to_agree (P : leibnizO _)).

  (** [nninv]: [ninv] in the accessor style *)
  Definition nninv_def (δ : nderiv_ty Σ) (N : namespace) (P : nPropL (;ᵞ))
    : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(δ).
  Definition nninv_aux : seal nninv_def. Proof. by eexists. Qed.
  Definition nninv := nninv_aux.(unseal).
  Lemma nninv_unseal : nninv = nninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance nninv_persistent {δ N P} : Persistent (nninv δ N P).
  Proof. rewrite nninv_unseal. exact _. Qed.

  (** [na_nninv]: [na_ninv] in the accessor style *)
  Definition na_nninv_def (δ : nderiv_ty Σ)
    (p : na_inv_pool_name) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_inv_wsat]{E}=∗
          P ∗ n_na_own p (F∖↑N) ∗
          (P -∗ n_na_own p (F∖↑N) =[n_inv_wsat]{E}=∗ n_na_own p F) ⸩(δ).
  Definition na_nninv_aux : seal na_nninv_def. Proof. by eexists. Qed.
  Definition na_nninv := na_nninv_aux.(unseal).
  Lemma na_nninv_unseal : na_nninv = na_nninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance na_nninv_persistent {δ p N P} :
    Persistent (na_nninv δ p N P).
  Proof. rewrite na_nninv_unseal. exact _. Qed.
End iris.
