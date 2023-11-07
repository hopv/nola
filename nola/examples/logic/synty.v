(** * Syntactic type *)

From nola.util Require Export prod proph.

(** Syntactic type *)
Inductive nsynty := Empty_setₛ | unitₛ | boolₛ | natₛ | Zₛ | Propₛ | nsyntyₛ
| aprvarₛ | prvarₛ (X : nsynty) | optionₛ (X : nsynty) | listₛ (X : nsynty)
| prod'ₛ (X Y : nsynty) | sumₛ (X Y : nsynty) | funₛ (X Y : nsynty).
Implicit Type (X Y : nsynty).

Notation "()ₛ" := unitₛ : nola_scope.
Infix "*'ₛ" := prod'ₛ (at level 80, right associativity) : nola_scope.
Infix "+ₛ" := sumₛ (at level 85, right associativity) : nola_scope.
Infix "→ₛ" := funₛ (at level 99, right associativity) : nola_scope.

(** Decidable equality *)
#[export] Instance nsynty_eq_dec : EqDecision nsynty.
Proof. solve_decision. Defined.

(** [nsynty] is inhabited *)
#[export] Instance nsynty_inhabited : Inhabited nsynty := populate Empty_setₛ.

(** Decidable inhabitedness *)
Fixpoint nsynty_inhab X : bool :=
  match X with
  | Empty_setₛ => false | prvarₛ X => nsynty_inhab X
  | X *'ₛ Y => nsynty_inhab X && nsynty_inhab Y
  | X +ₛ Y => nsynty_inhab X || nsynty_inhab Y
  | X →ₛ Y => negb (nsynty_inhab X) || nsynty_inhab Y
  | _ => true
  end.

(** Syntactic pre-type structure *)
Canonical nsynty_synpty : synpty :=
  {| synpty_car := nsynty; synpty_inhab := nsynty_inhab; |}.

Notation aprvarn := (aprvar nsynty).

(** Interpret [nsynty] as a type *)
Fixpoint nsynty_ty (X : nsynty) : Type :=
  match X with
  | Empty_setₛ => Empty_set | unitₛ => () | boolₛ => bool | natₛ => nat
  | Zₛ => Z | Propₛ => Prop | nsyntyₛ => nsynty | aprvarₛ => aprvarn
  | prvarₛ X => prvar X | optionₛ X => option (nsynty_ty X)
  | listₛ X => list (nsynty_ty X) | X *'ₛ Y => nsynty_ty X *' nsynty_ty Y
  | X +ₛ Y => nsynty_ty X + nsynty_ty Y
  | X →ₛ Y => nsynty_ty X → nsynty_ty Y
  end.
Coercion nsynty_ty: nsynty >-> Sortclass.

(** [nsynty_inhab] is equivalent to inhabitance *)
Local Lemma of_either_nsynty_inhab {X} :
  (nsynty_inhab X → X) * (negb (nsynty_inhab X) → X → False).
Proof.
  move: X. fix FIX 1. move=> X. split.
  - case: X=>//=; try by (move=> *; exact inhabitant).
    + move=> ?. by apply (aprvar_by_inhab unitₛ).
    + move=> X h. exact (prvar_by_inhab X h).
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> X ?. case eq: (nsynty_inhab X)=>/= H.
      * apply inl, FIX. by rewrite eq.
      * by apply inr, FIX.
    + move=> X ?. case eq: (nsynty_inhab X)=>/= ??; [by apply FIX|].
      exfalso. eapply FIX; [|done]. by rewrite eq.
  - case: X=>//=.
    + move=> X /negb_True. apply (prvar_neg_inhab X).
    + move=> X ?. rewrite negb_andb.
      case eq: (nsynty_inhab X)=>/= ?[a b]; [by eapply FIX|].
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
Lemma to_nsynty_inhab {X} (x : X) : nsynty_inhab X.
Proof.
  case eq: (nsynty_inhab X); [done|]. exfalso.
  eapply of_neg_nsynty_inhab; [|done]. by rewrite eq.
Qed.
Lemma to_neg_nsynty_inhab {X} (f : X → False) : negb (nsynty_inhab X).
Proof.
  case eq: (nsynty_inhab X); [|done]. exfalso. apply f, of_nsynty_inhab.
  by rewrite eq.
Qed.

(** Syntactic type structure *)
Program Canonical nsynty_synty : synty :=
  {| synty_pty := nsynty_synpty; synty_ty := nsynty_ty; |}.
Next Obligation. by move=> ? /of_nsynty_inhab. Qed.
Next Obligation. by move=> ? /to_nsynty_inhab. Qed.

Notation proph_asnn := (proph_asn nsynty).
