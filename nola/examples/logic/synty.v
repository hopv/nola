(** * Syntactic type *)

From nola.util Require Export prod.
From nola.iris Require Export prophecy.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From iris.proofmode Require Import proofmode.

(** Syntactic type *)
Inductive nsynty := Empty_setₛ | unitₛ | boolₛ | natₛ | Zₛ | Propₛ | nsyntyₛ
| aprvarₛ | prvarₛ (X : nsynty) | optionₛ (X : nsynty) | listₛ (X : nsynty)
| prod'ₛ (X Y : nsynty) | sumₛ (X Y : nsynty) | funₛ (X Y : nsynty).
Implicit Type (X Y : nsynty).

Declare Scope nsynty_scope.
Bind Scope nsynty_scope with nsynty.
Delimit Scope nsynty_scope with ST.
Notation "()" := unitₛ : nsynty_scope.
Infix "*'" := prod'ₛ : nsynty_scope. Infix "+" := sumₛ : nsynty_scope.
Infix "→" := funₛ : nsynty_scope.

(** Decidable equality *)
#[export] Instance nsynty_eq_dec : EqDecision nsynty.
Proof. solve_decision. Defined.

(** [nsynty] is inhabited *)
#[export] Instance nsynty_inhabited : Inhabited nsynty := populate Empty_setₛ.

(** Decidable inhabitedness *)
Fixpoint nsynty_inhab X : bool :=
  match X with
  | Empty_setₛ => false | prvarₛ X => nsynty_inhab X
  | prod'ₛ X Y => nsynty_inhab X && nsynty_inhab Y
  | sumₛ X Y => nsynty_inhab X || nsynty_inhab Y
  | funₛ X Y => negb (nsynty_inhab X) || nsynty_inhab Y
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
  | listₛ X => list (nsynty_ty X) | prod'ₛ X Y => nsynty_ty X *' nsynty_ty Y
  | sumₛ X Y => nsynty_ty X + nsynty_ty Y
  | funₛ X Y => nsynty_ty X → nsynty_ty Y
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
Notation prophn A := (proph nsynty A).

(** Existential type over a syntactic type *)
#[projections(primitive)]
Record anyty := Anyty {
  anyty_ty : nsynty;
  anyty_val : anyty_ty;
}.
Add Printing Constructor anyty.

(** Ghost state *)
Class anyty_varG Σ := anyty_varG_in :: ghost_varG Σ anyty.
Definition anyty_varΣ := ghost_varΣ anyty.
#[export] Instance subG_anyty_varΣ `{!subG anyty_varΣ Σ} : anyty_varG Σ.
Proof. solve_inG. Qed.

(** Agreement over [anyty] *)
Notation anyty_var γ q X x := (ghost_var γ q (Anyty X x)).
Notation "γ ⤇{ X } ( q ) x" := (anyty_var γ q X x)
  (at level 20, only parsing) : bi_scope.
Notation "γ ⤇( q ) x" := (anyty_var γ q _ x)
  (at level 20, format "γ  ⤇( q )  x") : bi_scope.

Section anyty_var.
  Context `{!anyty_varG Σ}.

  (** [anyty_var] is timeless and fractional *)
  Fact anyty_var_timeless {X γ q x} : Timeless (γ ⤇{X}(q) x).
  Proof. exact _. Qed.
  Fact anyty_var_fractional {X γ x} : Fractional (λ q, γ ⤇{X}(q) x)%I.
  Proof. exact _. Qed.

  (** Allocate [anyty_var] *)
  Lemma anyty_var_alloc {X x} : ⊢ |==> ∃ γ, γ ⤇{X}(1) x.
  Proof. iApply ghost_var_alloc. Qed.

  (** Agreement between [anyty_var]s *)
  Lemma anyty_var_agree {X γ x y q r} : γ ⤇{X}(q) x -∗ γ ⤇{X}(r) y -∗ ⌜x = y⌝.
  Proof.
    iIntros "x y". iDestruct (ghost_var_agree with "x y") as %?. by simplify_eq.
  Qed.
End anyty_var.
