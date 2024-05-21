(** * [cit]: Coinductive-inductive tree *)

From nola Require Export prelude.
From nola.util Require Import rel order.
Import EqNotations OeqvNotation.

Implicit Type S CIT : Type.

(** ** [citI]: Intermediate inductive tree *)
Section citI.
  Context S (I C D : S → Type) CIT.
  Inductive citI := CitI {
    (** Selector *) cit_sel : S;
    (** Inductive children *) cit_ikidsI : I cit_sel → citI;
    (** Coinductive children *) cit_ckids : C cit_sel → CIT;
    (** Data *) cit_data : D cit_sel;
  }.
End citI.
Add Printing Constructor citI.
Arguments CitI {_ _ _ _ _}. Arguments cit_sel {_ _ _ _ _}.
Arguments cit_ikidsI {_ _ _ _ _}. Arguments cit_ckids {_ _ _ _ _}.
Arguments cit_data {_ _ _ _ _}.

(** ** [cit]: Coinductive-inductive tree *)
Section cit.
  Context S (I C D : S → Type).
  CoInductive cit := of_citI { to_citI : citI S I C D cit; }.
End cit.
Add Printing Constructor cit.
Arguments of_citI {_ _ _ _}. Arguments to_citI {_ _ _ _}.
Notation cit' S I C D := (citI S I C D (cit S I C D)).
Notation Cit s ik ck d := (of_citI (CitI s ik ck d)).
Notation cit_ikids t i := (of_citI (t.(cit_ikidsI) i)).
#[warning="-uniform-inheritance"] Coercion to_citI : cit >-> cit'.

(** ** [cit_forall2I]: Intermediate universal relation between [citI]s *)
Section cit_forall2I.
  Context {S} {I C D D' : S → Type}.
  Context (R : ∀ s, D s → D' s → Prop)
    (CITF : cit S I C D → cit S I C D' → Prop).
  Inductive cit_forall2I (t : cit S I C D) (t' : cit S I C D') : Prop := Citf2 {
    citf2_sel : t.(cit_sel) = t'.(cit_sel);
    citf2_ikids : ∀ i, cit_forall2I
      (cit_ikids t i) (cit_ikids t' (rew citf2_sel in i));
    citf2_ckids : ∀ c, CITF
      (t.(cit_ckids) c) (t'.(cit_ckids) (rew citf2_sel in c));
    citf2_data : ∀ s eq, R s
      (rew eq_trans citf2_sel eq in t.(cit_data)) (rew eq in t'.(cit_data));
  }.
End cit_forall2I.
Arguments Citf2 {_ _ _ _ _ _ _ _ _}. Arguments citf2_sel {_ _ _ _ _ _ _ _ _}.
Arguments citf2_ikids {_ _ _ _ _ _ _ _ _}.
Arguments citf2_ckids {_ _ _ _ _ _ _ _ _}.
Arguments citf2_data {_ _ _ _ _ _ _ _ _}.

Section cit_forall2I.
  Context {S} {I C : S → Type}.
  Implicit Type D : S → Type.

  (** [cit_forall2I] is monotone over [R] and [CITF] *)
  #[export] Instance cit_forall2I_mono {D D'} :
    Mono2 (@cit_forall2I _ I C D D').
  Proof.
    move=>/= ?? to ?? to' ??. elim=> ?? eq ? IH ??.
    apply (Citf2 eq); [done|..]=> *; by [apply to'|apply to].
  Qed.
  #[export] Instance cit_forall2I_mono' {D D' R} :
    Mono (@cit_forall2I _ I C D D' R).
  Proof. exact mono2_mono_2. Qed.

  (** [cit_forall2I] preserves the reflexivity *)
  #[export] Instance cit_forall2I_refl
    `{!∀ s, @Reflexive (D s) (R s), !Reflexive CITF} :
    Reflexive (@cit_forall2I _ I C D _ R CITF).
  Proof.
    case=> t. elim: t=> *. apply (Citf2 eq_refl); [done..|]=> ? eq. by case eq.
  Qed.

  (** Flip [cit_forall2I] *)
  Lemma cit_forall2I_flip {D D' R CITF t t'} :
    cit_forall2I (λ s, flip (R s)) (flip CITF) t' t →
      @cit_forall2I _ I C D D' R CITF t t'.
  Proof.
    elim=> ?? eq ? IH Hc Hd.
    have E : ∀ X x, x = rew eq in rew[X] eq_sym eq in x.
    { move=> ? x. rewrite rew_compose. move: x. by case eq. }
    apply (Citf2 (eq_sym eq)).
    - move=> i. rewrite {1}(E _ i). exact: IH.
    - move=> c. rewrite {1}(E _ c). exact: Hc.
    - move=> ? eq'. suff E': eq' = eq_trans eq (eq_trans (eq_sym eq) eq').
      { rewrite {2}E'. exact: Hd. } { clear. by case eq, eq'. }
  Qed.

  (** Compose [cit_forall2I]s *)
  Lemma cit_forall2I_trans {D D' D'' R R' CITF CITF' t t' t''} :
    @cit_forall2I _ I C D D' R CITF t t' →
    cit_forall2I (D':=D'') R' CITF' t' t'' →
      cit_forall2I (λ s, rcompose (R s) (R' s)) (rcompose CITF CITF') t t''.
  Proof.
    move=> F. move: t''. elim: F=> ?? eq ? IH ???[eq' ???].
    apply (Citf2 (eq_trans eq eq')).
    - move=> ?. apply IH. by rewrite -rew_compose.
    - move=> ?. eexists _. split; [done|]. by rewrite -rew_compose.
    - move=> ? eq''. eexists _. split; [|done]. by rewrite -eq_trans_assoc.
  Qed.

  (** Convert universally quantified [cit_forall2I], under UIP over [S] *)
  Lemma cit_forall2I_forall `{!∀ s s' : S, ProofIrrel (s = s'), !Inhabited A}
    {D D' R CITF t t'} :
    (∀ a : A, @cit_forall2I _ I C D D' (R a) (CITF a) t t') →
      cit_forall2I (λ _ d d', ∀ a, R a _ d d') (λ t t', ∀ a, CITF a t t') t t'.
  Proof.
    move=> Fs. induction (Fs inhabitant) as [t t' eq _ IH _ _].
    have E: ∀ a, (Fs a).(citf2_sel) = eq by move=> ?; exact: proof_irrel.
    apply (Citf2 eq).
    - move=> i. apply IH=> a. rewrite -(E a). exact: (Fs a).(citf2_ikids).
    - move=> c a. rewrite -(E a). exact: (Fs a).(citf2_ckids).
    - move=> s eq' a. rewrite -(E a). exact: (Fs a).(citf2_data).
  Qed.
End cit_forall2I.

(** ** [cit_forall2]: Universal relation between [cit]s *)
Definition cit_forall2 {S I C D D'} R : cit S I C D → cit S I C D' → Prop :=
  gfp (cit_forall2I R).

Section cit_forall2.
  Context {S} {I C : S → Type}.
  Implicit Type D : S → Type.

  (** Unfold [cit_forall2] *)
  Lemma cit_forall2_unfold {D D' R t t'} :
    @cit_forall2 _ I C D D' R t t' ↔ cit_forall2I R (cit_forall2 R) t t'.
  Proof. split; apply (gfp_unfold (f:=cit_forall2I _)). Qed.
  Lemma cit_forall2_unfold_1 {D D' R t t'} :
    @cit_forall2 _ I C D D' R t t' → cit_forall2I R (cit_forall2 R) t t'.
  Proof. apply cit_forall2_unfold. Qed.
  Lemma cit_forall2_unfold_2 {D D' R t t'} :
    cit_forall2I R (cit_forall2 R) t t' → @cit_forall2 _ I C D D' R t t'.
  Proof. apply cit_forall2_unfold. Qed.
  #[warning="-uniform-inheritance"]
  Coercion cit_forall2_unfold_1 : cit_forall2 >-> cit_forall2I.

  (** Coinduction on [cit_forall2] *)
  Lemma cit_forall2_coind {D D' R t t'}
    (CH : cit S I C D → cit S I C D' → Prop) :
    CH t t' → (CH ⊑ cit_forall2I R CH) → cit_forall2 R t t'.
  Proof. move=> ??. by apply (gfp_coind (o:=CH)). Qed.

  (** [cit_forall2] is monotone *)
  #[export] Instance cit_forall2_mono {D D'} :
    Mono (@cit_forall2 _ I C D D').
  Proof. move=> *. by apply gfp_mono, mono. Qed.

  (** [cit_forall2] preserves the reflexivity *)
  #[export] Instance cit_forall2_refl `{!∀ s, @Reflexive (D s) (R s)} :
    Reflexive (cit_forall2 (I:=I) (C:=C) R).
  Proof.
    move=> ?. apply (cit_forall2_coind (λ t t', t = t')); [done|]=> ??<-.
    exact: _.
  Qed.

  (** Flip [cit_forall2] *)
  Lemma cit_forall2_flip {D D' R t t'} :
    cit_forall2 (λ s, flip (R s)) t' t → @cit_forall2 _ I C D D' R t t'.
  Proof.
    move=> ?.
    apply (cit_forall2_coind (flip (cit_forall2 (λ s, flip (R s))))); [done|].
    move=> ?? /cit_forall2_unfold ?. exact: cit_forall2I_flip.
  Qed.
  (** [cit_forall2] preserves the symmetricity *)
  #[export] Instance cit_forall2_sym `{!∀ s, @Symmetric (D s) (R s)} :
    Symmetric (cit_forall2 (I:=I) (C:=C) R).
  Proof.
    move=> ?? F. apply cit_forall2_flip. move: F. by apply cit_forall2_mono.
  Qed.

  (** Compose [cit_forall2]s *)
  Lemma cit_forall2_compose {D D' D'' R R' t t' t''} :
    @cit_forall2 _ I C D D' R t t' → cit_forall2 (D':=D'') R' t' t'' →
      cit_forall2 (λ s, rcompose (R s) (R' s)) t t''.
  Proof.
    move=> ??.
    apply (cit_forall2_coind (rcompose (cit_forall2 R) (cit_forall2 R'))).
    { by eexists _. }
    move=> ??[?[/cit_forall2_unfold ? /cit_forall2_unfold ?]].
    by apply: cit_forall2I_trans.
  Qed.
  (** [cit_forall2] preserves the transitivity *)
  #[export] Instance cit_forall2_trans `{!∀ s, @Transitive (D s) (R s)} :
    Transitive (cit_forall2 (I:=I) (C:=C) R).
  Proof.
    move=> ??? F F'. move: (cit_forall2_compose F F'). apply cit_forall2_mono.
    move=> ???[?[??]]. by etrans.
  Qed.

  (** [cit_forall2] preserves the equivalence relation *)
  #[export] Instance cit_forall2_equiv `{!∀ s, @Equivalence (D s) (R s)} :
    Equivalence (cit_forall2 (I:=I) (C:=C) R).
  Proof. split; exact _. Qed.

  (** Convert universally quantified [cit_forall2], under UIP over [S] *)
  Lemma cit_forall2_forall `{!∀ s s' : S, ProofIrrel (s = s'), !Inhabited A}
    {D D' R t t'} :
    (∀ a : A, @cit_forall2 _ I C D D' (R a) t t') →
      cit_forall2 (λ _ d d', ∀ a, R a _ d d') t t'.
  Proof.
    move=> ?.
    apply (cit_forall2_coind (λ t t', ∀ a, cit_forall2 (R a) t t')); [done|].
    move=> ???. apply cit_forall2I_forall=> ?. by apply cit_forall2_unfold.
  Qed.
End cit_forall2.
