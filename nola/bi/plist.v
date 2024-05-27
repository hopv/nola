(** * On [plist] *)

From nola.util Require Export plist.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
Import ProdNotation.

Fixpoint big_sepPL {PROP : bi} {A} {F : A → Type} {al} (Φ : ∀ a, F a → PROP)
  : plist F al → PROP :=
  match al with [] => λ _, emp | _ :: _ =>
    λ '(x, xl)', Φ _ x ∗ big_sepPL Φ xl end%I.

Module PlistNotation.
  Notation "[∗ plist] a ∈ al ; x ∈ xl , P" := (big_sepPL (al:=al) (λ a x, P) xl)
    (at level 200, al at level 10, xl at level 10, a binder, x binder,
      only parsing) : bi_scope.
  Notation "[∗ plist] a ; x ∈ xl , P" := (big_sepPL (λ a x, P) xl)
    (at level 200, xl at level 10, a binder, x binder,
      format "[∗  plist]  a ;  x  ∈  xl ,  P") : bi_scope.
  Notation "[∗ plist] x ∈ xl , P" := (big_sepPL (λ _ x, P) xl)
    (at level 200, xl at level 10, x binder,
      format "[∗  plist]  x  ∈  xl ,  P") : bi_scope.
End PlistNotation.
Import PlistNotation.

Section big_sepPL.
  Context {PROP : bi} {A} {F : A → Type}.

  (** [big_sepPL] is non-expansive *)
  #[export] Instance big_sepPL_ne {n al} :
    Proper
      (forall_relation (λ _, pointwise_relation _ (≡{n}≡)) ==> (=) ==> (≡{n}≡))
      (@big_sepPL PROP A F al).
  Proof.
    move=> ?? eq xl _<-. elim: al xl; [done|]=>/= ?? IH ?. by rewrite eq IH.
  Qed.
  (** [big_sepPL] is proper *)
  #[export] Instance big_sepPL_proper {al} :
    Proper
      (forall_relation (λ _, pointwise_relation _ (⊣⊢)) ==> (=) ==> (⊣⊢))
      (@big_sepPL PROP A F al).
  Proof.
    move=> ?? eq xl _<-. elim: al xl; [done|]=>/= ?? IH ?. by rewrite eq IH.
  Qed.
  (** [big_sepPL] is monotone *)
  #[export] Instance big_sepPL_mono {al} :
    Proper
      (forall_relation (λ _, pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
      (@big_sepPL PROP A F al).
  Proof.
    move=> ?? eq xl _<-. elim: al xl; [done|]=>/= ?? IH ?. by rewrite eq IH.
  Qed.
  #[export] Instance big_sepPL_mono' {al} :
    Proper
      (forall_relation (λ _, pointwise_relation _ (flip (⊢))) ==> (=) ==>
        flip (⊢))
      (@big_sepPL PROP A F al).
  Proof.
    move=> ?? eq xl _<-. elim: al xl; [done|]=>/= ?? IH ?. by rewrite eq IH.
  Qed.

  (** [big_sepL] over [of_plist] as [big_sepPL] *)
  Lemma big_sepL_of_plist {B}
    (f : ∀ a, F a → B) (Φ : B → PROP) {al} (xl : plist F al) :
    ([∗ list] y ∈ of_plist f xl, Φ y) ⊣⊢ [∗ plist] x ∈ xl, Φ (f _ x).
  Proof. elim: al xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

  (** [big_sepPL] preserves [Persistent] *)
  #[export] Instance big_sepPL_persistent {Φ : ∀ a, F a → PROP}
    {al} {xl : plist F al} `{!∀ a x, Persistent (Φ a x)} :
    Persistent ([∗ plist] x ∈ xl, Φ _ x).
  Proof. elim: al xl; exact _. Qed.

  (** Merge [big_sepPL]s *)
  Lemma big_sepPL_sep {Φ Ψ : ∀ a, F a → PROP} {al} {xl : plist F al} :
    ([∗ plist] x ∈ xl, Φ _ x ∗ Ψ _ x) ⊣⊢
      ([∗ plist] x ∈ xl, Φ _ x) ∗ [∗ plist] x ∈ xl, Ψ _ x.
  Proof.
    elim: al xl=>/=; [move=> _; by rewrite left_id|]=> ?? IH [??].
    rewrite IH. iSplit; iIntros "[[$$][$$]]".
  Qed.
  Lemma big_sepPL_sep_2 {Φ Ψ : ∀ a, F a → PROP} {al} {xl : plist F al} :
    ([∗ plist] x ∈ xl, Φ _ x) -∗ ([∗ plist] x ∈ xl, Ψ _ x) -∗
      [∗ plist] x ∈ xl, Φ _ x ∗ Ψ _ x.
  Proof. rewrite big_sepPL_sep. iIntros. iFrame. Qed.

  (** Modify [big_sepPL] *)
  Lemma big_sepPL_impl {Φ Ψ : ∀ a, F a → PROP} {al} {xl : plist F al} :
    ([∗ plist] x ∈ xl, Φ _ x) -∗ □ (∀ a x, Φ a x -∗ Ψ a x) -∗
      [∗ plist] x ∈ xl, Ψ _ x.
  Proof.
    elim: al xl; [by iIntros|]=>/= ?? IH [??]. iIntros "[Φ Φl] #→".
    iDestruct (IH with "Φl →") as "$". by iApply "→".
  Qed.

  (** [big_sepPL] and [plist_map] *)
  Lemma big_sepPL_map {G : A → Type} (f : ∀ a, F a → G a)
    (Φ : ∀ a, G a → PROP) {al} (xl : plist F al) :
    ([∗ plist] x ∈ plist_map f xl, Φ _ x) ⊣⊢ [∗ plist] x ∈ xl, Φ _ (f _ x).
  Proof. elim: al xl=>/=; [done|]=> ?? IH [??]. by rewrite IH. Qed.
End big_sepPL.
