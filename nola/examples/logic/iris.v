(** * Iris preliminaries *)

From nola.examples.logic Require Export prop.
From nola.iris Require Export deriv wp sinv inv na_inv pborrow.
From iris.base_logic.lib Require Export cancelable_invariants.
From nola.examples.heap_lang Require Export definitions.

(** ** Iris resources *)

(** [nintpGS]: Iris resource *)
Class nintpGS Σ := NintpGS {
  nintpGS_sinv :: sinvGS (nPropS (;ᵞ)) Σ;
  nintpGS_ninv :: ninvGS (nPropS (;ᵞ)) Σ;
  nintpGS_na_ninv :: na_ninvGS (nPropS (;ᵞ)) Σ;
  nintpGS_na_inv :: na_invG Σ;
  nintpGS_cinv :: cinvG Σ;
  nintpGS_pborrow :: pborrowGS nsynty (nPropS (;ᵞ)) Σ;
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

Implicit Type (N : namespace) (p : na_inv_pool_name) (α : lft) (q : Qp)
  (X : nsynty).

Section iris.
  Context (* Iris resources *) `{!nintpGS Σ}.
  Implicit Type δ : nderiv_ty Σ.

  (** [sinv]: [sinv_tok] in the accessor style *)
  Definition sinv_def δ P : iProp Σ :=
    □ ⸨ n_sinv_wsat -∗ P ∗ (P -∗ n_sinv_wsat) ⸩(δ).
  Local Lemma sinv_aux : seal sinv_def. Proof. by eexists. Qed.
  Definition sinv := sinv_aux.(unseal).
  Lemma sinv_unseal : sinv = sinv_def. Proof. exact: seal_eq. Qed.

  (** [ninv]: [inv_tok] in the accessor style *)
  Definition ninv_def δ N P : iProp Σ :=
    □ ⸨ ∀ E, ⌜↑N ⊆ E⌝ → |=[n_inv_wsat]{E,E∖↑N}=>
          P ∗ (P =[n_inv_wsat]{E∖↑N,E}=∗ True) ⸩(δ).
  Local Lemma ninv_aux : seal ninv_def. Proof. by eexists. Qed.
  Definition ninv := ninv_aux.(unseal).
  Lemma ninv_unseal : ninv = ninv_def. Proof. exact: seal_eq. Qed.

  (** [na_ninv]: [na_ninv] in the accessor style *)
  Definition na_ninv_def δ p N P : iProp Σ :=
    □ ⸨ ∀ E F, ⌜↑N ⊆ E⌝ → ⌜↑N ⊆ F⌝ → n_na_own p F =[n_na_inv_wsat]{E}=∗
          n_na_own p (F∖↑N) ∗ P ∗
          (n_na_own p (F∖↑N) -∗ P =[n_na_inv_wsat]{E}=∗ n_na_own p F) ⸩(δ).
  Local Lemma na_ninv_aux : seal na_ninv_def. Proof. by eexists. Qed.
  Definition na_ninv := na_ninv_aux.(unseal).
  Lemma na_ninv_unseal : na_ninv = na_ninv_def. Proof. exact: seal_eq. Qed.

  Implicit Type (P : nPropS (;ᵞ)).

  (** [borc]: Modified [nbor_ctok] *)
  Definition borc δ α P : iProp Σ :=
    ∃ Q, ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) ∗ ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) ∗ nbor_ctok α Q.
  (** [bor]: Modified [nbor_tok] *)
  Definition bor δ α P : iProp Σ :=
    ∃ Q, ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) ∗ ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) ∗ nbor_tok α Q.
  (** [obor]: Modified [onbor_tok] *)
  Definition obor δ α q P : iProp Σ :=
    ∃ Q, ⸨ ↑ˡ P ==∗ ↑ˡ Q ⸩(δ) ∗ onbor_tok α q Q.
  (** [lend]: Modified [nlend_tok] *)
  Definition lend δ α P : iProp Σ := ∃ Q, ⸨ ↑ˡ Q ==∗ ↑ˡ P ⸩(δ) ∗ nlend_tok α Q.
  (** [fbor]: Fractured borrower *)
  Definition fbor δ α (Φ : Qp → nPropS (;ᵞ)) : iProp Σ :=
    ∃ β Ψ, α ⊑□ β ∗
      □ ⸨ ∀ q, ↑ˡ Φ q ==∗ ↑ˡ Ψ q ⸩(δ) ∗ □ ⸨ ∀ q, ↑ˡ Ψ q ==∗ ↑ˡ Φ q ⸩(δ) ∗
      sinv_tok (∃ q, n_bor' [] β (Ψ q))%n.

  (** [pborc]: Modified [pbor_ctok] *)
  Definition pborc {X} δ α x ξ (Φ : X → nPropS (;ᵞ)) : iProp Σ :=
    ∃ Ψ, ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) ∗ ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) ∗
      pbor_ctok α x ξ Ψ.
  (** [pbor]: Modified [pbor_tok] *)
  Definition pbor {X} δ α x ξ (Φ : X → nPropS (;ᵞ)) : iProp Σ :=
    ∃ Ψ, ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) ∗ ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) ∗
      pbor_tok α x ξ Ψ.
  (** [opbor]: Modified [opbor_tok] *)
  Definition opbor {X} δ α q ξ (Φ : X → nPropS (;ᵞ)) : iProp Σ :=
    ∃ Ψ, ⸨ ∀ x, ↑ˡ Φ x ==∗ ↑ˡ Ψ x ⸩(δ) ∗ opbor_tok α q ξ Ψ.
  (** [plend]: Modified [plend_tok] *)
  Definition plend {X} δ α xπ (Φ : X → nPropS (;ᵞ)) : iProp Σ :=
    ∃ Ψ, ⸨ ∀ x, ↑ˡ Ψ x ==∗ ↑ˡ Φ x ⸩(δ) ∗ plend_tok α xπ Ψ.
End iris.

(** Utility *)
Notation fbor_mapsto δ α l v := (fbor δ α (λ q, l ↦{#q} v)%n).
Notation "l ↦( δ ) [ α ] v" := (fbor_mapsto δ α l v)
  (at level 20, format "l  ↦( δ ) [ α ]  v") : bi_scope.
