(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola.iris Require Export deriv wp inv na_inv borrow proph_ag.
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
  nintpGS_borrow :: borrowGS (nPropS (;ᵞ)) Σ;
  nintpGS_proph :: prophGS nsynty Σ;
  nintpGS_proph_ag :: proph_agG nsynty Σ;
  nintpGS_heap :: heapGS_gen HasNoLc Σ;
}.
Arguments NintpGS {_}.

(** ** Derivability structure *)

(** [derivs] for [nPropL] *)
Canonical nderivs Σ : derivs := Derivs (nPropL (;ᵞ)) (iProp Σ).

(** Notation for [nderivs] *)
Notation nderiv_ty Σ := (deriv_ty (nderivs Σ)).
Notation "⸨ P ⸩ ( δ )" := (dunwrap δ P%n)
  (format "'[' ⸨  P  ⸩ '/  ' ( δ ) ']'") : nola_scope.

Implicit Type (P : nPropL (;ᵞ)) (N : namespace) (p : na_inv_pool_name)
  (α : lft) (q : Qp).

Section iris.
  Context (* Iris resources *) `{!nintpGS Σ}.
  Implicit Type (δ : nderiv_ty Σ) .

  Definition nag γ P : iProp Σ :=
    own γ (to_agree (P : leibnizO _)).

  (** [ninv]: [inv_tok] in the accessor style *)
  Definition ninv_def δ N P : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(δ).
  Definition ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Lemma ninv_unseal : ninv = ninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance ninv_persistent {δ N P} : Persistent (ninv δ N P).
  Proof. rewrite ninv_unseal. exact _. Qed.

  (** [na_ninv]: [na_ninv] in the accessor style *)
  Definition na_ninv_def δ p N P : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_na_inv_wsat]{E}=∗
          n_na_own p (F∖↑N) ∗ P ∗
          (n_na_own p (F∖↑N) -∗ P =[n_na_inv_wsat]{E}=∗ n_na_own p F) ⸩(δ).
  Definition na_ninv_aux : seal na_ninv_def. Proof. by eexists. Qed.
  Definition na_ninv := na_ninv_aux.(unseal).
  Lemma na_ninv_unseal : na_ninv = na_ninv_def. Proof. exact: seal_eq. Qed.
  #[export] Instance na_ninv_persistent {δ p N P} :
    Persistent (na_ninv δ p N P).
  Proof. rewrite na_ninv_unseal. exact _. Qed.

  (** [conv]: Proposition converter *)
  Definition conv δ P Q : iProp Σ := ⸨ P -∗ Q ⸩(δ).

  (** [borc]: Modified [bor_ctok] *)
  Definition borc δ α P : iProp Σ :=
    ∃ Q, □ conv δ P (↑ˡ Q) ∗ □ conv δ (↑ˡ Q) P ∗ bor_ctok α Q.
  (** [bor]: Modified [bor_tok] *)
  Definition bor δ α P : iProp Σ :=
    ∃ Q, □ conv δ P (↑ˡ Q) ∗ □ conv δ (↑ˡ Q) P ∗ bor_tok α Q.
  (** [obor]: Modified [obor_tok] *)
  Definition obor δ α q P : iProp Σ :=
    ∃ Q, □ conv δ P (↑ˡ Q) ∗ □ conv δ (↑ˡ Q) P ∗ obor_tok α q Q.
  (** [lend]: Modified [lend_tok] *)
  Definition lend δ α P : iProp Σ :=
    ∃ Q, □ conv δ (↑ˡ Q) P ∗ lend_tok α Q.
  (** [fbor]: Modified [fbor_tok] *)
  Definition fbor δ (α : lft) (Φ : Qp → nPropL (;ᵞ)) : iProp Σ := False.
End iris.

(** Utility *)
Notation borrow_wsat'' := (borrow_wsat (bupdw proph_wsat)).
Notation fbor_mapsto δ α l v := (fbor δ α (λ q, l ↦{#q} v)%n).
Notation "l ↦( δ ) [ α ] v" := (fbor_mapsto δ α l v)
  (at level 20, format "l  ↦( δ ) [ α ]  v") : bi_scope.
