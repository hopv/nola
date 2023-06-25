(** * Utility for natural numbers *)

From nola Require Export prelude.
From stdpp Require Import base.

(** ** [≤ⁿ], [<ⁿ]: [≤] and [<] over [nat] as a type class *)
Definition nle := Nat.le. Definition nlt := Nat.lt.
Existing Class nle. Existing Class nlt.
#[export] Typeclasses Transparent nle nlt.
Infix "≤ⁿ" := nle (at level 70, no associativity) : nola_scope.
Infix "<ⁿ" := nlt (at level 70, no associativity) : nola_scope.
Definition nle' := flip nle. Definition nlt' := flip nlt.
Arguments nle' /. Arguments nlt' /.
Existing Class nle'. Existing Class nlt'.
Notation "(.≤ⁿ i )" := (nle' i) (format "(.≤ⁿ  i )") : nola_scope.
Notation "(.<ⁿ i )" := (nlt' i) (format "(.<ⁿ  i )") : nola_scope.

(** Construct [≤ⁿ] and [<ⁿ] *)
#[export] Instance nle_0 {n} : 0 ≤ⁿ n.
Proof. unfold nle. lia. Qed.
#[export] Instance nle_S `(H : ! m ≤ⁿ n) : S m ≤ⁿ S n.
Proof. move: H. unfold nle. lia. Qed.
#[export] Instance nlt_nle `{! S m ≤ⁿ n} : m <ⁿ n.
Proof. done. Qed.
#[export] Instance nle'_nle `{! m ≤ⁿ n} : nle' n m.
Proof. simpl. apply _. Qed.
#[export] Instance nlt'_nlt `{! m <ⁿ n} : nlt' n m.
Proof. simpl. apply _. Qed.
Lemma nlt_S_nle {m n} : m <ⁿ S n → m ≤ⁿ n.
Proof. unfold nlt, nle. lia. Qed.
Lemma nle_trans {l m n} : l ≤ⁿ m → m ≤ⁿ n → l ≤ⁿ n.
Proof. apply Nat.le_trans. Qed.
Lemma nlt_trans {l m n} : l <ⁿ m → m <ⁿ n → l <ⁿ n.
Proof. apply Nat.lt_trans. Qed.
Lemma nlt_nle_trans {l m n} : l <ⁿ m → m ≤ⁿ n → l <ⁿ n.
Proof. apply Nat.lt_le_trans. Qed.
Lemma nle_nlt_trans {l m n} : l ≤ⁿ m → m <ⁿ n → l <ⁿ n.
Proof. apply Nat.le_lt_trans. Qed.
