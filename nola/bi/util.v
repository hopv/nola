(** * Basic utility *)

From nola Require Export prelude.
From iris.bi Require Export bi.

(** ** On [step_fupdN] *)

(** [step_fupdN] is non-expansive *)
Lemma step_fupdN_ne `{!BiFUpd PROP} {n E E' k} {P Q : PROP} :
  P ≡{n}≡ Q → (|={E}[E']▷=>^k P)%I ≡{n}≡ (|={E}[E']▷=>^k Q)%I.
Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
Lemma step_fupdN_proper `{!BiFUpd PROP} {E E' k} {P Q : PROP} :
  P ⊣⊢ Q → (|={E}[E']▷=>^k P) ⊣⊢ |={E}[E']▷=>^k Q.
Proof.
  move=> PQ. apply equiv_dist=> n. apply step_fupdN_ne. by rewrite PQ.
Qed.
