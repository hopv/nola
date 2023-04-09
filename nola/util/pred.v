(** * Utility for predicates *)

From nola Require Import prelude.

(** ** Basics *)

(** Lifted [False], [True], [∨], [∧] and [→] *)

Definition False1 {A} (a : A) : Prop := False.
Definition True1 {A} (a : A) : Prop := True.

Definition or1 {A} (φ ψ : A → Prop) a : Prop := φ a ∨ ψ a.
Infix "∨1" := or1 (at level 50, left associativity).
Notation "(∨1)" := or1 (only parsing).

Definition and1 {A} (φ ψ : A → Prop) a : Prop := φ a ∧ ψ a.
Infix "∧1" := and1 (at level 40, left associativity).
Notation "(∧1)" := and1 (only parsing).

Definition impl1 {A} (φ ψ : A → Prop) : Prop := ∀ a, φ a → ψ a.
Infix "→1" := impl1 (at level 99, right associativity).
Notation "(→1)" := impl1 (only parsing).

(** Parameterized predicate weakened/strengthened by the parameter *)
Definition por {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∨1 φ.
Definition pand {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∧1 φ.

(** Monotonicity *)

Class Mono1 A (p : (A → Prop) → A → Prop) : Prop := {
  mono1 : ∀{φ ψ} , (φ →1 ψ) → p φ →1 p ψ;
}.

(** ** [pnu]: Parameterized greatest fixpoint *)

Section pnu.
  Context {A : Type} (F : (A → Prop) → A → Prop).

  (** [pnu]: Parameterized greatest fixpoint *)
  CoInductive pnu (φ : A → Prop) a : Prop := Pnu {
    pnu_out : ∃ pnuor, (pnuor →1 por pnu φ) ∧ F pnuor a;
  }.

  (** Fold [pnu] *)
  Lemma pnu_fold φ a : F (por pnu φ) a → pnu φ a.
  Proof.
    move=> Fpnuor. split. exists (por pnu φ). split; by [move=> >|].
  Qed.

  (** Unfold [pnu] *)
  Lemma pnu_unfold `{Mono1 _ F} φ a : pnu φ a → F (por pnu φ) a.
  Proof.
    move=> /pnu_out[pnuor[pnuorto ?]]. by apply (mono1 pnuorto).
  Qed.

  (** Monotonicity of [pnu] *)
  Global Instance pnu_mono : Mono1 _ pnu.
  Proof.
    split=> φ ψ φψ. cofix FIX=> a /pnu_out[pnuor[pnuorto ?]]. split.
    exists pnuor. split; [|done]=> ? /pnuorto[/FIX|/φψ]; by [left|right].
  Qed.

  (** Accumulate coinductive hypotheses *)
  Lemma pnu_acc `{Mono1 _ F} φ ψ : (ψ →1 pnu (φ ∨1 ψ)) → ψ →1 pnu φ.
  Proof.
    move=> topnuφψ=> a /topnuφψ +. move: a. cofix FIX=> a /pnu_unfold ?.
    split. exists (por pnu (φ ∨1 ψ)). split; [|done]. clear dependent a.
    move=> ? [/FIX|[|/topnuφψ/FIX]]; by [left|right|left].
  Qed.

  (** [nu]: Non-parameterized greatest fixpoint *)
  Definition nu : A → Prop := pnu False1.

  (** Fold [nu] *)
  Lemma nu_fold `{Mono1 _ F} a : F nu a → nu a.
  Proof.
    move=> Fnua. apply pnu_fold. eapply mono1; [|exact Fnua].
    clear dependent a=> a nua. left. by eapply mono1; [|exact nua]=> +.
  Qed.

  (** Unfold [nu] *)
  Lemma nu_unfold `{Mono1 _ F} a : nu a → F nu a.
  Proof.
    move=> /pnu_unfold FnuFa. eapply mono1; [|exact FnuFa]. move=> _ [//|[]].
  Qed.
End pnu.

(** ** [pmu]: Parameterized least fixpoint *)

Section pmu.
  Context {A : Type} (F : (A → Prop) → A → Prop).

  (** [pmu]: Parameterized least fixpoint *)
  Inductive pmu (φ : A → Prop) a : Prop := Pmu {
    pmu_out : ∃ pmuand, (pmuand →1 pand pmu φ) ∧ F pmuand a;
  }.

  (** Fold [pmu] *)
  Lemma pmu_fold φ a : F (pand pmu φ) a → pmu φ a.
  Proof.
    move=> Fpmuand. split. exists (pand pmu φ). split; by [move=> >|].
  Qed.

  (** Unfold [pmu] *)
  Lemma pmu_unfold `{Mono1 _ F} φ a : pmu φ a → F (pand pmu φ) a.
  Proof.
    move=> /pmu_out[pmuand[pmuandto ?]]. by apply (mono1 pmuandto).
  Qed.

  (** Monotonicity of [pmu] *)
  Global Instance pmu_mono : Mono1 _ pmu.
  Proof.
    split=> φ ψ φψ +. fix FIX 2=> a /pmu_out[pmuand[pmuandto ?]]. split.
    exists pmuand. split; [|done]=> ? /pmuandto[/FIX+ /φψ]//.
  Qed.

  (** Accumulate inductive hypotheses *)
  Lemma pmu_acc `{Mono1 _ F} φ ψ : (pmu (φ ∧1 ψ) →1 ψ) → pmu φ →1 ψ.
  Proof.
    move=> topmuφψ a pmuφa. apply topmuφψ. move: a pmuφa. fix FIX 2=> a.
    move=> [[pmuand[pmuandto Fpmuanda]]]. apply pmu_fold.
    eapply mono1; [|exact Fpmuanda]. clear dependent a=> a pmuanda.
    move: (pmuandto _ pmuanda)=> [/FIX pmuφψa φa]. split; [done|].
    split; [done|]. by apply topmuφψ.
  Qed.

  (** [mu]: Non-parameterized least fixpoint *)
  Definition mu : A → Prop := pmu True1.

  (** Fold [mu] *)
  Lemma mu_fold `{Mono1 _ F} a : F mu a → mu a.
  Proof.
    move=> Fmua. apply pmu_fold. eapply mono1; [|exact Fmua].
    clear dependent a=> a mua. split; [|done]. by eapply mono1; [|exact mua].
  Qed.

  (** Unfold [mu] *)
  Lemma mu_unfold `{Mono1 _ F} a : mu a → F mu a.
  Proof.
    move=> /pmu_unfold FmuFa. eapply mono1; [|exact FmuFa]. by move=> ?[??].
  Qed.
End pmu.
