(** * Utility for natural numbers *)

From nola Require Export prelude.
From stdpp Require Import base.

(** ** [+']: Addition definitionally satisfying
  [S m +' n = m +' S n] and [0 +' n = n] *)
Fixpoint add' (m n : nat) :=
  match m with 0 => n | S m => add' m (S n) end.
Infix "+'" := add' (at level 50, left associativity) : nat_scope.

(** [+'] into [+] *)
Lemma add'_add {m n} : m +' n = m + n.
Proof. move: n. elim m; [done|]=>/= ? eq ?. rewrite eq. lia. Qed.

(** Simplify [+' 0] *)
Lemma add'_0_r {n} : n +' 0 = n.
Proof. rewrite add'_add. lia. Qed.

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
#[export] Instance nle_S `(mn : ! m ≤ⁿ n) : S m ≤ⁿ S n.
Proof. move: mn. unfold nle. lia. Qed.
#[export] Instance nle_refl {n} : n ≤ⁿ n | 3.
Proof. unfold nle. lia. Qed.
#[export] Instance nlt_0 {n} : 0 <ⁿ S n.
Proof. unfold nlt. lia. Qed.
#[export] Instance nlt_S `(mn : ! m <ⁿ n) : S m <ⁿ S n.
Proof. move: mn. unfold nlt. lia. Qed.
#[export] Instance nlt_refl {n} : n <ⁿ S n | 3.
Proof. unfold nlt. lia. Qed.
#[export] Instance nle'_nle `{! m ≤ⁿ n} : nle' n m.
Proof. simpl. exact _. Qed.
#[export] Instance nlt'_nlt `{! m <ⁿ n} : nlt' n m.
Proof. simpl. exact _. Qed.
Lemma nlt_no0 `{n0 : ! n <ⁿ 0} {A} : A.
Proof. move: n0. unfold nlt. lia. Qed.
Lemma nle_unS {m n} : S m ≤ⁿ S n → m ≤ⁿ n.
Proof. unfold nle. lia. Qed.
Lemma nlt_unS {m n} : S m <ⁿ S n → m <ⁿ n.
Proof. unfold nlt. lia. Qed.
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
Lemma nlt_nlt_S_trans {l m n} : l <ⁿ m → m <ⁿ S n → l <ⁿ n.
Proof. move=> lm mn. exact (nlt_nle_trans lm (nlt_S_nle mn)). Qed.
