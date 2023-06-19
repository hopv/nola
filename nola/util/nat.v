(** * Utility for natural numbers *)

From nola Require Export prelude.
From stdpp Require Import base.

(** ** [≤ⁿ], [<ⁿ]: [≤] and [<] over [nat] as a type class *)
Class nle (m n : nat) : Prop := Nle { unnle : m ≤ n }.
Add Printing Constructor nle.
Class nlt (m n : nat) : Prop := Nlt { unnlt : m < n }.
Add Printing Constructor nlt.
Infix "≤ⁿ" := nle (at level 70, no associativity) : nola_scope.
Infix "<ⁿ" := nlt (at level 70, no associativity) : nola_scope.
Definition nle' := flip nle.
Arguments nle' /. Existing Class nle'.
Definition nlt' := flip nlt.
Arguments nlt' /. Existing Class nlt'.
Notation "(.≤ⁿ i )" := (nle' i) (format "(.≤ⁿ  i )") : nola_scope.
Notation "(.<ⁿ i )" := (nlt' i) (format "(.<ⁿ  i )") : nola_scope.

(** Construct [≤ⁿ] *)
#[export] Instance nle_n {n} : n ≤ⁿ n.
Proof. by split. Qed.
#[export] Instance nle_S `(!m ≤ⁿ n) : m ≤ⁿ S n | 1.
Proof. split. apply le_S, unnle. Qed.
Lemma nle_trans {m n p} `(!m ≤ⁿ n, !n ≤ⁿ p) : m ≤ⁿ p.
Proof. split. etrans; apply unnle. Qed.
#[export] Instance nle'_nle `(!m ≤ⁿ n) : nle' n m.
Proof. simpl. apply _. Qed.

(** Construct [<ⁿ] *)
#[export] Instance nlt_n {n} : n <ⁿ S n.
Proof. split. apply le_n. Qed.
#[export] Instance nlt_S `{!m <ⁿ n} : m <ⁿ S n | 1.
Proof. split. apply le_S, unnlt. Qed.
Lemma nle_nlt_trans {m n p} `(!m ≤ⁿ n, !n <ⁿ p) : m <ⁿ p.
Proof. split. eapply Nat.le_lt_trans; [apply unnle|apply unnlt]. Qed.
Lemma nlt_nle_trans {m n p} `(!m <ⁿ n, !n ≤ⁿ p) : m <ⁿ p.
Proof. split. eapply Nat.lt_le_trans; [apply unnlt|apply unnle]. Qed.
Lemma nlt_trans {m n p} `(!m <ⁿ n, !n <ⁿ p) : m <ⁿ p.
Proof. split. etrans; apply unnlt. Qed.
#[export] Instance nlt'_nlt `(!m <ⁿ n) : nlt' n m.
Proof. simpl. apply _. Qed.

(** Proof irrelevance *)
#[export] Instance nle_pi {x y} : ProofIrrel (x ≤ⁿ y).
Proof. move=> [?][?]. f_equal. apply proof_irrel. Qed.
#[export] Instance nlt_pi {x y} : ProofIrrel (x <ⁿ y).
Proof. move=> [?][?]. f_equal. apply proof_irrel. Qed.
