(** * Utility for predicates *)

From nola Require Import prelude.

(** ** Basics *)

(** Lifted [False], [True], [∨], [∧] and [→] *)

Definition False1 {A} (a : A) : Prop := False.
Definition True1 {A} (a : A) : Prop := True.

Definition or1 {A} (φ ψ : A → Prop) a : Prop := φ a ∨ ψ a.
Infix "∨1" := or1 (at level 50, left associativity).
Notation "(∨1)" := or1 (only parsing) : nola_scope.

Definition and1 {A} (φ ψ : A → Prop) a : Prop := φ a ∧ ψ a.
Infix "∧1" := and1 (at level 40, left associativity).
Notation "(∧1)" := and1 (only parsing) : nola_scope.

Infix "→0" := impl (at level 99, right associativity).
Notation "(→0)" := impl (only parsing) : nola_scope.
Notation "(→0@{ A } )" := (@impl A) (only parsing) : nola_scope.

Definition impl1 {A} := pointwise_relation A impl.
Infix "→1" := impl1 (at level 99, right associativity).
Notation "(→1@{ A } )" := (@impl1 A) (only parsing) : nola_scope.
Notation "(→1)" := (impl1) (only parsing) : nola_scope.

(** Parameterized predicate weakened/strengthened by the parameter *)
Definition por {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∨1 φ.
Definition pand {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∧1 φ.

(** ** Monotonicity *)

Notation "Mono1@{ A , B }" := (Proper ((→1@{A}) ==> (→1@{B})))
  (only parsing) : nola_scope.
Notation Mono1 := (Mono1@{_, _}).

Lemma go_mono1 `(monop : Mono1@{A,B} p) φ ψ a : (φ →1 ψ) → p φ a → p ψ a.
Proof. by move=> /monop->. Qed.

(** Simplifies the goal [p φ a → p ψ a] into [φ →1 ψ] *)
Ltac go_mono1 := apply go_mono1; [apply _|].
(** Simplifies the goal [p ψ a] into [φ →1 ψ] consuming [x : p φ a] *)
Tactic Notation "go_mono1" "with" constr(x) := move: x; go_mono1.

(** Proper instances for [Mono1] *)

Global Instance Mono1_flip `(Mono1@{A,B} p) : Proper ((→1) --> flip (→1)) p.
Proof. move=> ψ φ /=? a +. by go_mono1. Qed.

Global Instance Mono1_impl `(Mono1@{A,B} p) : Proper ((→1) ==> (=) ==> (→0)) p.
Proof. move=> φ ψ /=? a _ <- +. by go_mono1. Qed.

Global Instance Mono1_flip_impl `(Mono1@{A,B} p) :
  Proper ((→1) --> (=) ==> flip (→0)) p.
Proof. move=> ψ φ /=? a _ <- +. by go_mono1. Qed.

(** ** [pnu]: Parameterized greatest fixpoint *)

Section pnu.
  Context {A : Type} (F : (A → Prop) → A → Prop).

  (** [pnu]: Parameterized greatest fixpoint *)
  CoInductive pnu (φ : A → Prop) a : Prop := {
    (* The type is equivalent to [F (por pnu φ) a] if [F] is monotone;
      parameterization by [pnuor] serves for strict positivity *)
    pnu_out : ∃ pnuor, (pnuor →1 por pnu φ) ∧ F pnuor a;
  }.

  (** Fold [pnu] *)
  Lemma pnu_fold φ a : F (por pnu φ) a → pnu φ a.
  Proof. move=> ?. split. exists (por pnu φ). split; by [move=> >|]. Qed.

  (** Unfold [pnu] *)
  Lemma pnu_unfold `(Mono1 F) φ a : pnu φ a → F (por pnu φ) a.
  Proof. move=> /pnu_out[_[->]]. done. Qed.

  (** Monotonicity of [pnu] *)
  Global Instance pnu_mono : Mono1 pnu.
  Proof.
    move=> φ ψ φψ. cofix FIX=> a /pnu_out[pnuor[pnuorto ?]]. split.
    exists pnuor. split; [|done]=> ? /pnuorto[/FIX|/φψ]; by [left|right].
  Qed.

  (** Accumulate coinductive hypotheses *)
  Lemma pnu_acc `(Mono1 F) φ ψ : (ψ →1 pnu (φ ∨1 ψ)) → ψ →1 pnu φ.
  Proof.
    move=> topnuφψ=> a /topnuφψ +. move: a. cofix FIX=> a /pnu_unfold ?.
    split. exists (por pnu (φ ∨1 ψ)). split; [|done]. clear dependent a.
    move=> ? [/FIX|[|/topnuφψ/FIX]]; by [left|right|left].
  Qed.

  (** [nu]: Non-parameterized greatest fixpoint *)
  Definition nu : A → Prop := pnu False1.

  (** Fold [nu] *)
  Lemma nu_fold `(Mono1 F) a : F nu a → nu a.
  Proof.
    move=> Fnua. apply pnu_fold. go_mono1 with Fnua. clear a=> a nua. left.
    by go_mono1 with nua.
  Qed.

  (** Unfold [nu] *)
  Lemma nu_unfold `(Mono1 F) a : nu a → F nu a.
  Proof. move/pnu_unfold. go_mono1. move=> _ [//|[]]. Qed.
End pnu.

(** ** [pmu]: Parameterized least fixpoint *)

Section pmu.
  Context {A : Type} (F : (A → Prop) → A → Prop).

  (** [pmu]: Parameterized least fixpoint *)
  Inductive pmu (φ : A → Prop) a : Prop := {
    (* The type is equivalent to [F (pand pmu φ) a] if [F] is monotone;
      parameterization by [pmuand] serves for strict positivity *)
    pmu_out : ∃ pmuand, (pmuand →1 pand pmu φ) ∧ F pmuand a;
  }.

  (** Fold [pmu] *)
  Lemma pmu_fold φ a : F (pand pmu φ) a → pmu φ a.
  Proof. move=> ?. split. exists (pand pmu φ). split; by [move=> >|]. Qed.

  (** Unfold [pmu] *)
  Lemma pmu_unfold `(Mono1 F) φ a : pmu φ a → F (pand pmu φ) a.
  Proof. move=> /pmu_out[_[->]]. done. Qed.

  (** Monotonicity of [pmu] *)
  Global Instance pmu_mono : Mono1 pmu.
  Proof.
    move=> φ ψ φψ ++. fix FIX 2=> a /pmu_out[pmuand[pmuandto ?]]. split.
    exists pmuand. split; [|done]=> ? /pmuandto[/FIX+ /φψ]//.
  Qed.

  (** Accumulate inductive hypotheses *)
  Lemma pmu_acc `(Mono1 F) φ ψ : (pmu (φ ∧1 ψ) →1 ψ) → pmu φ →1 ψ.
  Proof.
    move=> topmuφψ a pmuφa. apply topmuφψ. move: a pmuφa. fix FIX 2=> a.
    move=> [[pmuand[pmuandto Fpmuanda]]]. apply pmu_fold.
    go_mono1 with Fpmuanda. clear a=> a /pmuandto[/FIX pmuφψa φa].
    split; [done|]. split; [done|]. by apply topmuφψ.
  Qed.

  (** [mu]: Non-parameterized least fixpoint *)
  Definition mu : A → Prop := pmu True1.

  (** Fold [mu] *)
  Lemma mu_fold `(Mono1 F) a : F mu a → mu a.
  Proof.
    move=> Fmua. apply pmu_fold. go_mono1 with Fmua. clear a=> a mua.
    split; [|done]. by go_mono1 with mua.
  Qed.

  (** Unfold [mu] *)
  Lemma mu_unfold `(Mono1 F) a : mu a → F mu a.
  Proof. move/pmu_unfold. go_mono1. by move=> ?[??]. Qed.
End pmu.
