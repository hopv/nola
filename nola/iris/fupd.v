(** * On fancy updates *)

From nola Require Export prelude.
From iris.base_logic Require Import fancy_updates.

(** ** Fancy update with a custom world satisfaction [W] *)

Reserved Notation "|=[ W ] => P" (at level 99, W at level 50, P at level 200,
  format "'[  ' |=[ W ] =>  '/' P ']'").
Reserved Notation "P =[ W ]=∗ Q" (at level 99, W at level 50, Q at level 200,
  format "'[' P  =[ W ]=∗  '/' '[' Q ']' ']'").
Reserved Notation "|=[ W ] { E , E' }=> P" (at level 99, W at level 50,
  P at level 200, format "'[  ' |=[ W ] '/' { E , E' }=>  '/' P ']'").
Reserved Notation "|=[ W ] { E }=> P" (at level 99, W at level 50,
  P at level 200, format "'[  ' |=[ W ] '/' { E }=>  '/' P ']'").
Reserved Notation "P =[ W ] { E , E' }=∗ Q" (at level 99, W at level 50,
  Q at level 200, format "'[' P  =[ W ] '/' { E , E' }=∗  '/' '[' Q ']' ']'").
Reserved Notation "P =[ W ] { E }=∗ Q" (at level 99, W at level 50,
  Q at level 200, format "'[' P  =[ W ] '/' { E }=∗  '/' '[' Q ']' ']'").

Notation "|=[ W ] => P" := (W ==∗ W ∗ P)%I : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%I : bi_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : stdpp_scope.
Notation "|=[ W ] { E , E' }=> P" := (W ={E,E'}=∗ W ∗ P)%I : bi_scope.
Notation "|=[ W ] { E }=> P" := (|=[W]{E,E}=> P)%I : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q)%I : bi_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q) : stdpp_scope.
Notation "P =[ W ] { E }=∗ Q" := (P =[W]{E,E}=∗ Q)%I : bi_scope.
Notation "P =[ W ] { E }=∗ Q" := (P =[W]{E,E}=∗ Q) : stdpp_scope.

(** ** Lemmas *)
Section fupd.
  Context `{!BiFUpd PROP}.

  (** [step_fupdN] is non-expansive *)
  Lemma step_fupdN_ne {n E E' k} {P Q : PROP} :
    P ≡{n}≡ Q → (|={E}[E']▷=>^k P)%I ≡{n}≡ (|={E}[E']▷=>^k Q)%I.
  Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
  Lemma step_fupdN_proper {E E' k} {P Q : PROP} :
    P ⊣⊢ Q → (|={E}[E']▷=>^k P) ⊣⊢ |={E}[E']▷=>^k Q.
  Proof.
    move=> PQ. apply equiv_dist=> n. apply step_fupdN_ne. by rewrite PQ.
  Qed.

  (** [fupd] is non-expansive *)

  (** Fancy update with the world satisfaction is non-expansive *)
  Lemma fupdpw_ne {n E E'} {W W' P Q : PROP} :
    W ≡{n}≡ W' → P ≡{n}≡ Q → (|=[W]{E,E'}=> P)%I ≡{n}≡ (|=[W']{E,E'}=> Q)%I.
  Proof. move=> ??. f_equiv; [done|]. by do 2 f_equiv. Qed.
  Lemma fupdpw_proper {E E'} {W W' P Q : PROP} :
    W ⊣⊢ W' → P ⊣⊢ Q → (|=[W]{E,E'}=> P)%I ⊣⊢ (|=[W']{E,E'}=> Q)%I.
  Proof. by move=> ->->. Qed.
End fupd.
