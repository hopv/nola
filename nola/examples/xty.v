(** * Syntactic type *)

From nola.util Require Export prod proph.
Import ProdNotation.

(** Syntactic type *)
Inductive xpty :=
| aprvarₓ | prvarₓ (X : xpty) | xptyₓ
| Empty_setₓ | unitₓ | boolₓ | natₓ | Zₓ | Propₓ
| optionₓ (X : xpty) | listₓ (X : xpty) | vecₓ (X : xpty) (n : nat)
| prod'ₓ (X Y : xpty) | sumₓ (X Y : xpty) | funₓ (X Y : xpty).
Implicit Type (X Y : xpty).

Module NsyntyNotation.
  Notation "()ₓ" := unitₓ.
  Infix "*'ₓ" := prod'ₓ (at level 80, right associativity).
  Infix "+ₓ" := sumₓ (at level 85, right associativity).
  Infix "→ₓ" := funₓ (at level 99, right associativity).
End NsyntyNotation.
Import NsyntyNotation.

(** Decidable equality *)
#[export] Instance xpty_eq_dec : EqDecision xpty.
Proof. solve_decision. Defined.

(** [xpty] is inhabited *)
#[export] Instance xpty_inhabited : Inhabited xpty := populate Empty_setₓ.

(** Decidable inhabitedness *)
Fixpoint xpty_inhab X : bool :=
  match X with
  | Empty_setₓ => false
  | prvarₓ X | vecₓ X (S _) => xpty_inhab X
  | X *'ₓ Y => xpty_inhab X && xpty_inhab Y
  | X +ₓ Y => xpty_inhab X || xpty_inhab Y
  | X →ₓ Y => negb (xpty_inhab X) || xpty_inhab Y
  | _ => true
  end.

(** Syntactic pre-type structure *)
Canonical xpty_synpty : synpty :=
  {| synpty_car := xpty; synpty_inhab := xpty_inhab; |}.

Notation aprvarn := (aprvar xpty).

(** Interpret [xpty] as a type *)
Fixpoint xpty_ty (X : xpty) : Type :=
  match X with
  | aprvarₓ => aprvarn | prvarₓ X => prvar X | xptyₓ => xpty
  | Empty_setₓ => Empty_set | unitₓ => () | boolₓ => bool | natₓ => nat
  | Zₓ => Z | Propₓ => Prop
  | optionₓ X => option (xpty_ty X) | listₓ X => list (xpty_ty X)
  | vecₓ X n => vec (xpty_ty X) n
  | X *'ₓ Y => xpty_ty X *' xpty_ty Y | X +ₓ Y => xpty_ty X + xpty_ty Y
  | X →ₓ Y => xpty_ty X → xpty_ty Y
  end.
Coercion xpty_ty: xpty >-> Sortclass.

(** [xpty_inhab] is equivalent to inhabitance *)
Local Lemma of_either_xpty_inhab {X} :
  (xpty_inhab X → X) * (negb (xpty_inhab X) → X → False).
Proof.
  move: X. fix FIX 1. move=> X. split.
  - case: X=>//=; try by (move=> *; exact inhabitant).
    + move=> ?. by apply (aprvar_by_inhab unitₓ).
    + move=> X h. exact (prvar_by_inhab X h).
    + move=> ?[|?]?; [exact inhabitant|]. by apply vreplicate, FIX.
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> X ?. case eq: (xpty_inhab X)=>/= H.
      { apply inl, FIX. by rewrite eq. } { by apply inr, FIX. }
    + move=> X ?. case eq: (xpty_inhab X)=>/= ??; [by apply FIX|].
      exfalso. eapply FIX; [|done]. by rewrite eq.
  - case: X=>//=.
    + move=> X /negb_True. apply (prvar_neg_inhab X).
    + move=> X ? + v. case: v; [done|]=> ????. by eapply FIX.
    + move=> X ?. rewrite negb_andb.
      case eq: (xpty_inhab X)=>/= ?[a b]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite eq.
    + move=> ??. by rewrite negb_orb=> /andb_True[??] [a|b];
      eapply FIX; [|apply a| |apply b].
    + move=> ??. rewrite negb_orb negb_involutive=> /andb_True[??] f.
      eapply FIX; [done|]. by apply f, FIX.
Qed.
Lemma of_xpty_inhab {X} : xpty_inhab X → X.
Proof. apply of_either_xpty_inhab. Qed.
Lemma of_neg_xpty_inhab {X} : negb (xpty_inhab X) → X → False.
Proof. apply of_either_xpty_inhab. Qed.
Lemma to_xpty_inhab {X} (x : X) : xpty_inhab X.
Proof.
  case eq: (xpty_inhab X); [done|]. exfalso. eapply of_neg_xpty_inhab; [|done].
  by rewrite eq.
Qed.
Lemma to_neg_xpty_inhab {X} (f : X → False) : negb (xpty_inhab X).
Proof.
  case eq: (xpty_inhab X); [|done]. exfalso. apply f, of_xpty_inhab.
  by rewrite eq.
Qed.

(** Syntactic type structure *)
Program Canonical xty : synty := {| synty_pty := xpty; synty_ty := xpty_ty; |}.
Next Obligation. by move=> ? /of_xpty_inhab. Qed.
Next Obligation. by move=> ? /to_xpty_inhab. Qed.
