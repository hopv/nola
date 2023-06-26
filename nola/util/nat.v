(** * Utility for natural numbers *)

From nola Require Export prelude.
From stdpp Require Import base.

(** ** [+']: Addition definitionally satisfying
  [S m +' n = m +' S n] and [0 +' n = n] *)
Fixpoint add' (m n : nat) :=
  match m with 0 => n | S m => add' m (S n) end.
Infix "+'" := add' (at level 50, left associativity) : nat_scope.

(** ** Equalities for [nat], defined directly for computation *)

(** Simplify [_ + 0] *)
Fixpoint add_0_r_d {m} : m + 0 = m :=
  match m with 0 => eq_refl | S m => f_equal S add_0_r_d end.

(** Simplify [_ + S _] *)
Fixpoint add_succ_r_d {m n} : m + S n = S (m + n) :=
  match m with 0 => eq_refl | S m => f_equal S add_succ_r_d end.

(** [+'] into [+] *)
Fixpoint add'_add_d {m n} : m +' n = m + n :=
  match m with 0 => eq_refl | S _ => eq_trans add'_add_d add_succ_r_d end.

(** Simplify [+' 0] *)
Definition add'_0_r_d {n} : n +' 0 = n := eq_trans add'_add_d add_0_r_d.

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
#[export] Instance nlt_0 {n} : 0 <ⁿ S n.
Proof. unfold nlt. lia. Qed.
#[export] Instance nlt_S `(mn : ! m <ⁿ n) : S m <ⁿ S n.
Proof. move: mn. unfold nlt. lia. Qed.
#[export] Instance nle'_nle `{! m ≤ⁿ n} : nle' n m.
Proof. simpl. apply _. Qed.
#[export] Instance nlt'_nlt `{! m <ⁿ n} : nlt' n m.
Proof. simpl. apply _. Qed.
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
