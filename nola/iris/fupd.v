(** * On fancy updates *)

From iris.base_logic Require Import fancy_updates.

Section fupd.
  Context `{!BiFUpd PROP}.

  (** [step_fupdN] is non-expansive *)
  Lemma step_fupdN_ne {n Eo Ei k} {P Q : PROP} :
    P ≡{n}≡ Q → (|={Eo}[Ei]▷=>^k P)%I ≡{n}≡ (|={Eo}[Ei]▷=>^k Q)%I.
  Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
End fupd.

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
