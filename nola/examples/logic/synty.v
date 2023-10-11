(** * Syntactic type *)

From nola.iris Require Export prophecy.

(** Syntactic type *)
Inductive nsynty := Empty_setₛ | natₛ | Zₛ | boolₛ | unitₛ | Propₛ
| optionₛ (X : nsynty) | listₛ (X : nsynty) | prodₛ (X Y : nsynty)
| sumₛ (X Y : nsynty) | funₛ (X Y : nsynty).
Implicit Type (X Y : nsynty).

Declare Scope nsynty_scope.
Bind Scope nsynty_scope with nsynty.
Delimit Scope nsynty_scope with ST.
Notation "()" := unitₛ : nsynty_scope.
Infix "*" := prodₛ : nsynty_scope. Infix "+" := sumₛ : nsynty_scope.
Infix "→" := funₛ : nsynty_scope.

(** Interpret [nsynty] as a type *)
Fixpoint nsynty_ty (X: nsynty) : Type :=
  match X with
  | Empty_setₛ => Empty_set | natₛ => nat | Zₛ => Z | boolₛ => bool
  | unitₛ => () | Propₛ => Prop | optionₛ X => option (nsynty_ty X)
  | listₛ X => list (nsynty_ty X) | prodₛ X Y => nsynty_ty X * nsynty_ty Y
  | sumₛ X Y => nsynty_ty X + nsynty_ty Y
  | funₛ X Y => nsynty_ty X → nsynty_ty Y
  end.
Coercion nsynty_ty: nsynty >-> Sortclass.

(** Decidable equality *)
#[export] Instance nsynty_eq_dec : EqDecision nsynty.
Proof. solve_decision. Defined.

(** Decidable inhabitedness *)

Fixpoint nsynty_inhab X : bool :=
  match X with
  | Empty_setₛ => false | prodₛ X Y => nsynty_inhab X && nsynty_inhab Y
  | sumₛ X Y => nsynty_inhab X || nsynty_inhab Y
  | funₛ X Y => negb (nsynty_inhab X) || nsynty_inhab Y
  | _ => true
  end.

Local Lemma of_either_nsynty_inhab {X} :
  (nsynty_inhab X → X) * (negb (nsynty_inhab X) → X → False).
Proof.
  move: X. fix FIX 1. move=> X. split.
  - case: X=>//=; try by (move=> *; exact inhabitant).
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> X ?. case eq: (nsynty_inhab X)=>/= H.
      * apply inl, FIX. by rewrite eq.
      * by apply inr, FIX.
    + move=> X ?. case eq: (nsynty_inhab X)=>/= ??; [by apply FIX|].
      exfalso. eapply FIX; [|done]. by rewrite eq.
  - case: X=>//=.
    + move=> X ?. rewrite negb_andb.
      case eq: (nsynty_inhab X)=>/= ?[a?]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite eq.
    + move=> ??. by rewrite negb_orb=> /andb_True[??] [a|b];
      eapply FIX; [|apply a| |apply b].
    + move=> ??. rewrite negb_orb negb_involutive=> /andb_True[??] f.
      eapply FIX; [done|]. by apply f, FIX.
Qed.
Lemma of_nsynty_inhab {X} : nsynty_inhab X → X.
Proof. apply of_either_nsynty_inhab. Qed.
Lemma of_neg_nsynty_inhab {X} : negb (nsynty_inhab X) → X → False.
Proof. apply of_either_nsynty_inhab. Qed.
Lemma to_nsynty_inhab {X} (x: X) : nsynty_inhab X.
Proof.
  case eq: (nsynty_inhab X); [done|]. exfalso.
  eapply of_neg_nsynty_inhab; [|done]. by rewrite eq.
Qed.
Lemma to_neg_nsynty_inhab {X} (f: X → False) : negb (nsynty_inhab X).
Proof.
  case eq: (nsynty_inhab X); [|done]. exfalso. apply f, of_nsynty_inhab.
  by rewrite eq.
Qed.

(** [nsynty] is [synty] *)
Program Canonical nsynty_synty : synty := {|
  synty_car := nsynty; synty_ty := nsynty_ty; synty_inhab := nsynty_inhab;
|}.
Next Obligation. by move=> ? /of_nsynty_inhab. Qed.
Next Obligation. by move=> ? /to_nsynty_inhab. Qed.

Notation prvarn := (prvar nsynty).
Notation aprvarn := (aprvar nsynty).
Notation proph_asnn := (proph_asn nsynty).
Notation prophn A := (proph nsynty A).
