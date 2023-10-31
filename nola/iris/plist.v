(** * On [plist] *)

From nola.util Require Export plist.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Fixpoint big_sepPL {PROP : bi} {A} {F : A → Type} (Φ : ∀ a, F a → PROP) {al}
  : plist F al → PROP :=
  match al with [] => λ _, emp | _ :: _ =>
    λ '(x, xl)', Φ _ x ∗ big_sepPL Φ xl end%I.
Notation "[∗ plist] a ; x ∈ xl , P" := (big_sepPL (λ a x, P) xl)
  (at level 200, xl at level 10, a binder, x binder,
    format "[∗  plist]  a ;  x  ∈  xl ,  P") : bi_scope.
Notation "[∗ plist] x ∈ xl , P" := (big_sepPL (λ _ x, P) xl)
  (at level 200, xl at level 10, x binder,
    format "[∗  plist]  x  ∈  xl ,  P") : bi_scope.

Section big_sepPL.
  Context {PROP : bi} {A} {F : A → Type}.

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
