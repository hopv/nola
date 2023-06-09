(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola Require Export sintp.
From nola.iris Require Export inv na_inv wp.
From nola.examples.heap_lang Require Export primitive_laws.

(** ** Iris resources *)

(** Data for invariant *)
Variant nid : Type :=
| (* usual *) nid_u : nPropS (;ᵞ) → nid
| (* non-atomic *) nid_na : na_inv_pool_name → positive → nPropS (;ᵞ) → nid.

(** [nintpGS]: Iris resource *)
Class nintpGS (Σ : gFunctors) := NintpG {
  nintpGS_heapGS :: heapGS_gen HasNoLc Σ;
  nintpGS_ninvGS :: ninvGS nid Σ;
  nintpGS_na_invG :: na_invG Σ;
}.

Section nid_intp.
  Context `{!nintpGS Σ}.

  (** Interpret [nid] *)
  Definition nid_intp (intp : nPropS (;ᵞ) -d> iProp Σ) : nid -d> iProp Σ :=
    λ Px, match Px with
    | nid_u P => intp P
    | nid_na p i P => na_body p i (intp P)
    end.
  #[export] Instance nid_intp_ne : NonExpansive nid_intp.
  Proof. solve_proper. Qed.

  (** [ninv_wsat] for [nid] *)
  Definition ninv_wsat' (intp : nPropS (;ᵞ) -d> iProp Σ) : iProp Σ :=
    ninv_wsat (nid_intp intp).
  #[export] Instance ninv_wsat'_ne : NonExpansive ninv_wsat'.
  Proof. solve_proper. Qed.
End nid_intp.

(** ** For strong interpretation *)

(** [intps] for [nPropL] *)
Definition nintps Σ : intps := Intps nat (λ _, nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nintps] *)
Notation nsintp_ty Σ := (sintp_ty (nintps Σ)).
Notation npsintp_ty Σ := (psintp_ty (nintps Σ)).
Notation "⸨ P ⸩ ( s , i )" := (sunwrap s (Sarg i P%n))
  (format "'[' ⸨  P  ⸩ '/  ' ( s ,  i ) ']'") : nola_scope.

Section iris.
  Context (* Iris resources *) `{!nintpGS Σ}.

  (** ** [nninv]: [ninv] in the accessor style *)
  Definition nninv_def (s : nsintp_ty Σ)
    (i : nat) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(s, i).
  Definition nninv_aux : seal nninv_def. Proof. by eexists. Qed.
  Definition nninv := nninv_aux.(unseal).
  Lemma nninv_unseal : nninv = nninv_def. Proof. exact nninv_aux.(seal_eq). Qed.
  #[export] Instance nninv_persistent {s i N P} : Persistent (nninv s i N P).
  Proof. rewrite nninv_unseal. apply _. Qed.

  (** ** [na_nninv]: Non-atomic [ninv] in the accessor style *)
  Definition na_nninv_def (s : nsintp_ty Σ) (i : nat)
    (p : na_inv_pool_name) (N : namespace) (P : nPropL (;ᵞ)) : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_inv_wsat]{E,E∖↑N}=∗
          P ∗ n_na_own p (F∖↑N) ∗
          (P -∗ n_na_own p (F∖↑N) =[n_inv_wsat]{E∖↑N,E}=∗ n_na_own p F) ⸩(s, i).
  Definition na_nninv_aux : seal na_nninv_def. Proof. by eexists. Qed.
  Definition na_nninv := na_nninv_aux.(unseal).
  Lemma na_nninv_unseal : na_nninv = na_nninv_def.
  Proof. exact na_nninv_aux.(seal_eq). Qed.
  #[export] Instance na_nninv_persistent {s i p N P} :
    Persistent (na_nninv s i p N P).
  Proof. rewrite na_nninv_unseal. apply _. Qed.
End iris.
