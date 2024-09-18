(** * Utility on equality *)

From nola Require Export prelude.
Import EqNotations.

(** UIP over a type *)
Notation Uip A := (∀ a a', ProofIrrel (@eq A a a')).

(** On [eq_sym] *)
Lemma rew_sym_l {A} {a a' : A} {X : A → Type} (eq : a = a') (x : X a) :
  rew[X] eq_sym eq in rew[X] eq in x = x.
Proof. by subst. Qed.
Lemma rew_sym_r {A} {a a' : A} {X : A → Type} (eq : a = a') (x : X a') :
  rew[X] eq in rew[X] eq_sym eq in x = x.
Proof. by subst. Qed.
