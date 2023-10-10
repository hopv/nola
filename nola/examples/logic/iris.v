(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola.iris Require Export deriv inv na_inv wp.
From iris.base_logic.lib Require Export cancelable_invariants.
From nola.examples.heap_lang Require Export definitions.

(** ** Iris resources *)

(** Agreement *)
Class agreeG A Σ := agree_inG :: inG Σ (agreeR (leibnizO A)).
Definition agreeΣ A : gFunctors := GFunctor (agreeR (leibnizO A)).
#[export] Instance subG_agreeΣ `{!subG (agreeΣ A) Σ} : agreeG A Σ.
Proof. solve_inG. Qed.

(** [nintpGS]: Iris resource *)
Class nintpGS Σ := NintpGS {
  nintpGS_agree :: agreeG (nPropL (;ᵞ)) Σ;
  nintpGS_ninv :: ninvGS (nPropS (;ᵞ)) Σ;
  nintpGS_na_ninv :: na_ninvGS (nPropS (;ᵞ)) Σ;
  nintpGS_na_inv :: na_invG Σ;
  nintpGS_cinv :: cinvG Σ;
  nintpGS_heap :: heapGS_gen HasNoLc Σ;
}.
Arguments NintpGS {_} _ _ _ _ _.

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

  (** [ninv]: [inv_tok] in the accessor style *)
  Definition ninv_def (δ : nderiv_ty Σ) (N : namespace) (P : nPropL (;ᵞ))
    : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(δ).
  Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Lemma ninv_unseal : ninv = ninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance ninv_persistent {δ N P} : Persistent (ninv δ N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  (** [na_ninv]: [na_ninv] in the accessor style *)
  Definition na_ninv_def (δ : nderiv_ty Σ)
    (p : na_inv_pool_name) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_na_inv_wsat]{E}=∗
          n_na_own p (F∖↑N) ∗ P ∗
          (n_na_own p (F∖↑N) -∗ P =[n_na_inv_wsat]{E}=∗ n_na_own p F) ⸩(δ).
  Definition na_ninv_aux : seal na_ninv_def. Proof. by eexists. Qed.
  Definition na_ninv := na_ninv_aux.(unseal).
  Lemma na_ninv_unseal : na_ninv = na_ninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance na_ninv_persistent {δ p N P} :
    Persistent (na_ninv δ p N P).
  Proof. rewrite na_ninv_unseal. exact _. Qed.
End iris.
