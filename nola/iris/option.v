(** * Utility for [option] *)

From nola Require Export prelude.
From iris.algebra Require Import cmra.

(** Unfold [≡] over [option] *)
Lemma option_equiv' {A : ofe} {o o' : option A} :
  o ≡ o' ↔
    match o, o' with
    | Some a, Some a' => a ≡ a'
    | None, None => True
    | _, _ => False
    end.
Proof. split; [by case|]. case: o; case: o'=>// *. by f_equiv. Qed.
(** Unfold [dist] over [option] *)
Lemma option_dist' {A : ofe} {n} {o o' : option A} :
  o ≡{n}≡ o' ↔
    match o, o' with
    | Some a, Some a' => a ≡{n}≡ a'
    | None, None => True
    | _, _ => False
    end.
Proof. split; [by case|]. case: o; case: o'=>// *. by f_equiv. Qed.

(** Unfold [≼] over [option] *)
Lemma option_included' {A : cmra} {o o' : option A} :
  o ≼ o' ↔
    match o, o' with
    | None, _ => True
    | Some a, Some a' => a ≡ a' ∨ a ≼ a'
    | _, _ => False
    end.
Proof. rewrite option_included. case: o; case: o'; naive_solver. Qed.
