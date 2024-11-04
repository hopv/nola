(** * On internal equality *)

From nola Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : bi.

(** ** Lemmas on [internal_eq] *)
Section internal_ne.
  Context `{!BiInternalEq PROP}.

  (** Variants of [f_equivI] *)
  Lemma f_equivI_exist {A PROP'} {Φ Ψ : A → PROP'} :
    (∀ a, Φ a ≡ Ψ a) ⊢@{PROP} (∃ a, Φ a) ≡ (∃ a, Ψ a).
  Proof. rewrite -discrete_fun_equivI. apply f_equivI. solve_proper. Qed.
  Lemma f_equivI_forall {A PROP'} {Φ Ψ : A → PROP'} :
    (∀ a, Φ a ≡ Ψ a) ⊢@{PROP} (∀ a, Φ a) ≡ (∀ a, Ψ a).
  Proof. rewrite -discrete_fun_equivI. apply f_equivI. solve_proper. Qed.
End internal_ne.

(** ** [internal_ne] Non-expansiveness inside [PROP] *)
Section internal_ne.
  Context `{!BiInternalEq PROP, !BiPlainly PROP}.
  Implicit Type A B : ofe.

  Definition internal_ne {A B} (f : A -d> B) : PROP :=
    ∀ a a', a ≡ a' → f a ≡ f a'.
  (** [internal_ne] is non-expansive *)
  #[export] Instance internal_ne_ne {A B} : NonExpansive (@internal_ne A B).
  Proof. solve_proper. Qed.
  #[export] Instance internal_ne_proper {A B} :
    Proper ((≡) ==> (≡)) (@internal_ne A B).
  Proof. solve_proper. Qed.
  (** [internal_ne] is plain *)
  #[export] Instance internal_ne_plain {A B f} : Plain (@internal_ne A B f).
  Proof. exact _. Qed.
  #[export] Instance internal_ne_persistent {A B f} :
    Persistent (@internal_ne A B f).
  Proof. exact _. Qed.
  (** [NonExpansive] entails [internal_ne] *)
  Lemma ne_internal_ne {A B f} : NonExpansive f → ⊢ @internal_ne A B f.
  Proof. iIntros (???) "≡". by iRewrite "≡". Qed.
End internal_ne.
Arguments internal_ne : simpl never.
