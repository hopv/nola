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
    (** Inductive children *) cit_ikids : I cit_sel → citI;
    (** Coinductive children *) cit_ckids : C cit_sel → CIT;
    (** Data *) cit_data : D cit_sel;
  }.
End citI.
Add Printing Constructor citI.
Arguments CitI {_ _ _ _ _}. Arguments cit_sel {_ _ _ _ _}.
Arguments cit_ikids {_ _ _ _ _}. Arguments cit_ckids {_ _ _ _ _}.
Arguments cit_data {_ _ _ _ _}.

(** ** [cit]: Coinductive-inductive tree *)
Section cit.
  Context S (I C D : S → Type).
  CoInductive cit := of_citI { to_citI : citI S I C D cit; }.
End cit.
Add Printing Constructor cit.
Arguments of_citI {_ _ _ _}. Arguments to_citI {_ _ _ _}.
Notation Cit s ik ck d := (of_citI (CitI s ik ck d)).
#[warning="-uniform-inheritance"] Coercion to_citI : cit >-> citI.

(** ** [citI_forall2]: Intermediate universal relation between [citI]s *)
Section citI_forall2.
  Context {S} {I C D D' : S → Type}.
  Context (R : ∀ s, D s → D' s → Prop)
    (CITF : cit S I C D → cit S I C D' → Prop).
  Inductive citI_forall2 (t : cit S I C D) (t' : cit S I C D') : Prop :=
    CitIForall2 {
    citf_sel : t.(cit_sel) = t'.(cit_sel);
    citf_ikids : ∀ i, citI_forall2 (of_citI (t.(cit_ikids) i))
      (of_citI (t'.(cit_ikids) (rew citf_sel in i)));
    citf_ckids : ∀ c, CITF
      (t.(cit_ckids) c) (t'.(cit_ckids) (rew citf_sel in c));
    citf_data : ∀ s eq, R s
      (rew eq_trans citf_sel eq in t.(cit_data)) (rew eq in t'.(cit_data));
  }.
End citI_forall2.
Arguments CitIForall2 {_ _ _ _ _ _ _ _ _}.
Arguments citf_sel {_ _ _ _ _ _ _ _ _}.
Arguments citf_ikids {_ _ _ _ _ _ _ _ _}.
Arguments citf_ckids {_ _ _ _ _ _ _ _ _}.
Arguments citf_data {_ _ _ _ _ _ _ _ _}.

Section citI_forall2.
  Context {S} {I C : S → Type}.
  Implicit Type D : S → Type.

  (** [citI_forall2] is monotone over [R] and [CITF] *)
  #[export] Instance citI_forall2_mono {D D'} :
    Mono2 (citI_forall2 (I:=I) (C:=C) (D:=D) (D':=D')).
  Proof.
    move=>/= ?? to ?? to' ??. elim=> ?? eq ? IH ??.
    apply (CitIForall2 eq); [done|..]=> *; by [apply to'|apply to].
  Qed.
  #[export] Instance citI_forall2_mono' {D D' R} :
    Mono (citI_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R).
  Proof. exact mono2_mono_2. Qed.

  (** [citI_forall2] preserves the reflexivity *)
  #[export] Instance citI_forall2_refl
    `{!∀ s, @Reflexive (D s) (R s), !Reflexive CITF} :
    Reflexive (citI_forall2 (I:=I) (C:=C) (D:=D) R CITF).
  Proof.
    case=> t. elim: t=> *. apply (CitIForall2 eq_refl); [done..|]=> ? eq.
    by case eq.
  Qed.

  (** Flip [citI_forall2] *)
  Lemma citI_forall2_flip {D D' R CITF t t'} :
    citI_forall2 (λ s, flip (R s)) (flip CITF) t' t →
      citI_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R CITF t t'.
  Proof.
    elim=> ?? eq ? IH Hc Hd.
    have E : ∀ X x, x = rew eq in rew[X] eq_sym eq in x.
    { move=> ? x. rewrite rew_compose. move: x. by case eq. }
    apply (CitIForall2 (eq_sym eq)).
    - move=> i. rewrite {1}(E _ i). exact: IH.
    - move=> c. rewrite {1}(E _ c). exact: Hc.
    - move=> ? eq'. suff E': eq' = eq_trans eq (eq_trans (eq_sym eq) eq').
      { rewrite {2}E'. exact: Hd. } { clear. by case eq, eq'. }
  Qed.

  (** Compose [citI_forall2]s *)
  Lemma citI_forall2_trans {D D' D'' R R' CITF CITF' t t' t''} :
    citI_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R CITF t t' →
    citI_forall2 (D':=D'') R' CITF' t' t'' →
      citI_forall2 (λ s, rcompose (R s) (R' s)) (rcompose CITF CITF') t t''.
  Proof.
    move=> F. move: t''. elim: F=> ?? eq ? IH ???[eq' ???].
    apply (CitIForall2 (eq_trans eq eq')).
    - move=> ?. apply IH. by rewrite -rew_compose.
    - move=> ?. eexists _. split; [done|]. by rewrite -rew_compose.
    - move=> ? eq''. eexists _. split; [|done]. by rewrite -eq_trans_assoc.
  Qed.
End citI_forall2.

(** ** [cit_forall2]: Universal relation between [cit]s *)
Definition cit_forall2 {S I C D D'} R : cit S I C D → cit S I C D' → Prop :=
  gfp (citI_forall2 R).

Section cit_forall2.
  Context {S} {I C : S → Type}.
  Implicit Type D : S → Type.

  (** Unfold [cit_forall2] *)
  Lemma cit_forall2_unfold {D D' R t t'} :
    cit_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R t t' ↔
      citI_forall2 R (cit_forall2 R) t t'.
  Proof. split; apply (gfp_unfold (f:=citI_forall2 _)). Qed.
  (** Coinduction on [cit_forall2] *)
  Lemma cit_forall2_coind {D D' R t t'}
    (CH : cit S I C D → cit S I C D' → Prop) :
    CH t t' → (CH ⊑ citI_forall2 R CH) → cit_forall2 R t t'.
  Proof. move=> ??. by apply (gfp_coind (o:=CH)). Qed.

  (** [cit_forall2] is monotone *)
  #[export] Instance cit_forall2_mono {D D'} :
    Mono (cit_forall2 (I:=I) (C:=C) (D:=D) (D':=D')).
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
    cit_forall2 (λ s, flip (R s)) t' t →
      cit_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R t t'.
  Proof.
    move=> ?.
    apply (cit_forall2_coind (flip (cit_forall2 (λ s, flip (R s))))); [done|].
    move=> ?? /cit_forall2_unfold ?. exact: citI_forall2_flip.
  Qed.
  (** [cit_forall2] preserves the symmetricity *)
  #[export] Instance cit_forall2_sym `{!∀ s, @Symmetric (D s) (R s)} :
    Symmetric (cit_forall2 (I:=I) (C:=C) R).
  Proof.
    move=> ?? F. apply cit_forall2_flip. move: F. by apply cit_forall2_mono.
  Qed.

  (** Compose [cit_forall2]s *)
  Lemma cit_forall2_compose {D D' D'' R R' t t' t''} :
    cit_forall2 (I:=I) (C:=C) (D:=D) (D':=D') R t t' →
    cit_forall2 (D':=D'') R' t' t'' →
      cit_forall2 (λ s, rcompose (R s) (R' s)) t t''.
  Proof.
    move=> ??.
    apply (cit_forall2_coind (rcompose (cit_forall2 R) (cit_forall2 R'))).
    { by eexists _. }
    move=> ??[?[/cit_forall2_unfold ? /cit_forall2_unfold ?]].
    by apply: citI_forall2_trans.
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
End cit_forall2.
