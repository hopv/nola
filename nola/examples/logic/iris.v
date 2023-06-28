(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola.iris Require Export sintp inv na_inv wp.
From iris.base_logic.lib Require Export cancelable_invariants.
From nola.examples.heap_lang Require Export primitive_laws.

(** ** Iris resources *)

(** Data for invariant *)
Variant nInvd : Type :=
| (* usual *) nInvd_u (P : nPropS (;ᵞ)) : nInvd
| (* non-atomic *) nInvd_na
    (p : na_inv_pool_name) (i : positive) (P : nPropS (;ᵞ)) : nInvd.

(** [nintpGS]: Iris resource *)
Class nintpGS (Σ : gFunctors) := NintpGS {
  nintpGS_ninvGS :: ninvGS nInvd Σ;
  nintpGS_na_invG :: na_invG Σ;
  nintpGS_cinvG :: cinvG Σ;
  nintpGS_heapGS :: heapGS_gen HasNoLc Σ;
}.
Arguments NintpGS {_} _ _ _ _.

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

(** ** Strong interpretation structure *)

(** [intps] for [nPropL] *)
Definition nintps Σ : intps := Intps nat (λ _, nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nintps] *)
Notation nsintp_ty Σ := (sintp_ty (nintps Σ)).
Notation "⸨ P ⸩ ( s , i )" := (sunwrap s (Sarg i P%n))
  (format "'[' ⸨  P  ⸩ '/  ' ( s ,  i ) ']'") : nola_scope.

Section iris.
  Context (* Iris resources *) {Σ : gFunctors}.

  (** [nninv]: [ninv] in the accessor style *)
  Definition nninv_def (s : nsintp_ty Σ)
    (i : nat) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(s, i).
  Definition nninv_aux : seal nninv_def. Proof. by eexists. Qed.
  Definition nninv := nninv_aux.(unseal).
  Lemma nninv_unseal : nninv = nninv_def. Proof. exact nninv_aux.(seal_eq). Qed.
  #[export] Instance nninv_persistent {s i N P} : Persistent (nninv s i N P).
  Proof. rewrite nninv_unseal. exact _. Qed.

  (** [na_nninv]: [na_ninv] in the accessor style *)
  Definition na_nninv_def (s : nsintp_ty Σ) (i : nat)
    (p : na_inv_pool_name) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_inv_wsat]{E}=∗
          P ∗ n_na_own p (F∖↑N) ∗
          (P -∗ n_na_own p (F∖↑N) =[n_inv_wsat]{E}=∗ n_na_own p F) ⸩(s, i).
  Definition na_nninv_aux : seal na_nninv_def. Proof. by eexists. Qed.
  Definition na_nninv := na_nninv_aux.(unseal).
  Lemma na_nninv_unseal : na_nninv = na_nninv_def.
  Proof. exact na_nninv_aux.(seal_eq). Qed.
  #[export] Instance na_nninv_persistent {s i p N P} :
    Persistent (na_nninv s i p N P).
  Proof. rewrite na_nninv_unseal. exact _. Qed.
End iris.
