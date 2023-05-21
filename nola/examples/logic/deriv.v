(** * Judgment derivability *)

From nola.examples.logic Require Export intp.
From nola Require Export util.wft deriv.
From iris.base_logic.lib Require Import iprop.

Implicit Type (d : nderiv_ty) (δ : npderiv_ty) (i j : nat).

(** ** Basic notions *)

(** [nJudg]: Judgment *)
Definition nJudg Σ `{!nintpG Σ} : judg :=
  Judg nat (λ _, nJudgTy) (λ d _ '(NJudg P Q), ⟦ P ⟧(d) ⊢ ⟦ Q ⟧(d)).

(** *[nderivy], [ninderivy], [nderiv]: Derivability *)
Class nderivy Σ `{!nintpG Σ} δ := Nderivy {
  nderivy_derivy :: derivy (nJudg Σ) δ;
}.
Class ninderivy Σ `{!nintpG Σ} δ' δ d i := Ninderivy {
  ninderivy_inderivy :: inderivy (nJudg Σ) δ' δ d i;
}.
#[export] Instance ninderivy_nderivy {Σ} `{!nintpG Σ, !ninderivy Σ δ' δ d i} :
  nderivy Σ δ'.
Proof. split. apply _. Qed.

Definition nderiv Σ `{!nintpG Σ} : npderiv_ty := deriv (nJudg Σ).

(** Operations on [nderiv_ty] *)
Definition Falseⁿᵈ : nderiv_ty := Dwrap (λ _ _, False).
Notation "⊥ⁿᵈ" := Falseⁿᵈ : nola_scope.
Definition orⁿᵈ d d' : nderiv_ty :=
  Dwrap (λ i '(NJudg P Q), (P ⊢{d,i} Q) ∨ (P ⊢{d',i} Q)).
Infix "∨ⁿᵈ" := orⁿᵈ (at level 50, left associativity) : nola_scope.
Definition apporⁿᵈ δ d : nderiv_ty := δ d ∨ⁿᵈ d.
Infix "$∨ⁿᵈ" := apporⁿᵈ (at level 50, left associativity) : nola_scope.
Definition implⁿᵈ d d' : Prop := ∀ i P Q, (P ⊢{d,i} Q) → P ⊢{d',i} Q.
Infix "→ⁿᵈ" := implⁿᵈ (at level 99, right associativity) : nola_scope.

(** ** Lemmas *)

(** Basic laws for [nderivy] *)
Section basic.
  Context `{!nintpG Σ, !nderivy Σ δ}.

  (** [δ] is monotone over the coinductive hypothesis *)
  Lemma n_mono {d d'} : (d →ⁿᵈ d') → δ d →ⁿᵈ δ d'.
  Proof.
    move=> dd' ???. apply (derivy_mono (JU:=nJudg Σ))=>/= ?[??]. apply dd'.
  Qed.

  (** [δ] can accumulate the coinductive hypothesis *)
  Lemma n_acc {d} res : (res →ⁿᵈ δ (d ∨ⁿᵈ res)) → res →ⁿᵈ δ d.
  Proof.
    move=> resto ???. apply (derivy_acc (JU:=nJudg Σ))=> ?[??]. by apply resto.
  Qed.

  (** [δ] can be proved by its semantics *)
  Lemma n_bysem {d i P Q} :
    (∀ δ', ninderivy Σ δ' δ d i → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ)) →
    P ⊢{δ d, i} Q.
  Proof. move=> H. apply (derivy_bysem (JU:=nJudg Σ))=> ??. by apply H. Qed.

  (** We can get Iris [⊢] out of [⊢{δ d, i}] under [ninderivy Σ δ' δ] *)
  Lemma nin_sem {δ' : npderiv_ty} `{!ninderivy Σ δ' δ d i} {P Q} :
    P ⊢{δ d, i} Q → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ).
  Proof. apply (inderivy_sem (JU:=nJudg Σ)). Qed.

  (** We can turn [δ $∨ⁿᵈ d] into [δ' ⊥ⁿᵈ] under [ninderivy] *)
  Lemma nin_turn `{!ninderivy Σ δ' δ d i} : δ $∨ⁿᵈ d →ⁿᵈ δ' ⊥ⁿᵈ.
  Proof. move=> ???. apply (inderivy_turn (JU:=nJudg Σ)). Qed.

  (** We can get Iris [⊢] out of [⊢{δ', j}] for [j < i]
    under [ninderivy Σ δ' δ d i] *)
  Lemma nin_semlow `{!ninderivy Σ δ' δ d i} {j P Q} :
    j < i → P ⊢{δ' ⊥ⁿᵈ, j} Q → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ).
  Proof. move=> ji PQ. apply (inderivy_semlow (JU:=nJudg Σ) _ ji _ PQ). Qed.

  (** Utility lemmas *)
  Lemma nin_turn_l `{!ninderivy Σ δ' δ d i} : δ d →ⁿᵈ δ' ⊥ⁿᵈ.
  Proof. move=> *. apply nin_turn. by left. Qed.
  Lemma nin_turn_r `{!ninderivy Σ δ' δ d i} : d →ⁿᵈ δ' ⊥ⁿᵈ.
  Proof. move=> *. apply nin_turn. by right. Qed.
  Lemma nin_turn_semlow `{!ninderivy Σ δ' δ d i} {j P Q} :
    j < i → P ⊢{δ $∨ⁿᵈ d, j} Q → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ).
  Proof. move=> ji ?. by apply (nin_semlow ji), nin_turn. Qed.
  Lemma nin_turn_semlow_l `{!ninderivy Σ δ' δ d i} {j P Q} :
    j < i → P ⊢{δ d, j} Q → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ).
  Proof. move=> ji ?. by apply (nin_semlow ji), nin_turn_l. Qed.
  Lemma nin_turn_semlow_r `{!ninderivy Σ δ' δ d i} {j P Q} :
    j < i → P ⊢{d, j} Q → ⟦ P ⟧(δ' ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(δ' ⊥ⁿᵈ).
  Proof. move=> ji ?. by apply (nin_semlow ji), nin_turn_r. Qed.

  (** [δ d] is monotone over the index *)
  Lemma n_up {i j d P Q} : i ≤ j → P ⊢{δ d, i} Q → P ⊢{δ d, j} Q.
  Proof.
    move=> /Nat.lt_eq_cases [|<-]; [|done]=> ? H. apply n_bysem=> ??.
    by apply nin_turn_semlow_l in H.
  Qed.
End basic.

(** On [nderiv] *)
Section nderiv.
  Context `{!nintpG Σ}.

  (** [nderiv] satisfies [nderivy] *)
  #[export] Instance nderiv_nderivy : nderivy Σ (nderiv Σ).
  Proof. split. apply _. Qed.

  (** [nderiv] is sound *)
  Lemma nderiv_sound {i P Q} :
    P ⊢{nderiv Σ ⊥ⁿᵈ, i} Q → ⟦ P ⟧(nderiv Σ ⊥ⁿᵈ) ⊢ ⟦ Q ⟧(nderiv Σ ⊥ⁿᵈ).
  Proof. apply (deriv_sound (JU:=nJudg Σ)). Qed.
End nderiv.
