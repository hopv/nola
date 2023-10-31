(** * On [plist] *)

From nola.util Require Export plist.
From iris.bi Require Import bi.

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
End big_sepPL.
