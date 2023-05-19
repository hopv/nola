(** * Utility for predicates *)

From nola Require Export prelude.

(** ** Basics *)

(** Lifted [False], [True], [∨], [∧] and [→] *)

Definition False₁ {A} (a : A) : Prop := False.
Notation "⊥₁" := False₁ : nola_scope.
Definition True₁ {A} (a : A) : Prop := True.
Notation "⊤₁" := True₁ : nola_scope.

Definition or₁ {A} (φ ψ : A → Prop) a : Prop := φ a ∨ ψ a.
Infix "∨₁" := or₁ (at level 50, left associativity) : nola_scope.
Notation "(∨₁)" := or₁ (only parsing) : nola_scope.

Definition and₁ {A} (φ ψ : A → Prop) a : Prop := φ a ∧ ψ a.
Infix "∧₁" := and₁ (at level 40, left associativity) : nola_scope.
Notation "(∧₁)" := and₁ (only parsing) : nola_scope.

Infix "→₀" := impl (at level 99, right associativity).
Notation "(→₀)" := impl (only parsing) : nola_scope.
Notation "(→₀@{ A } )" := (@impl A) (only parsing) : nola_scope.

Definition impl₁ {A} := pointwise_relation A impl.
Infix "→₁" := impl₁ (at level 99, right associativity) : nola_scope.
Notation "(→₁@{ A } )" := (@impl₁ A) (only parsing) : nola_scope.
Notation "(→₁)" := (impl₁) (only parsing) : nola_scope.

(** Parameterized predicate weakened/strengthened by the parameter *)
Definition appor₁ {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∨₁ φ.
Infix "$∨₁" := appor₁ (at level 50, left associativity) : nola_scope.
Definition appand₁ {A} (p : (A → Prop) → A → Prop) (φ : A → Prop) : A → Prop :=
  p φ ∧₁ φ.
Infix "$∧₁" := appand₁ (at level 40, left associativity) : nola_scope.

(** ** [Mono₁₁]: Monotonicity *)

Notation Mono₁₁' A B := (Proper ((→₁@{A}) ==> (→₁@{B}))) (only parsing).
Notation Mono₁₁ := (Mono₁₁' _ _).

(** Utility for [Mono₁₁] *)

Lemma use_mono₁₁ `{monop : Mono₁₁' A B p} φ ψ : (φ →₁ ψ) → p φ →₁ p ψ.
Proof. by move=> /monop->. Qed.

(** Proper instances for [Mono₁₁] *)

#[export] Instance Mono₁₁_flip `{Mono₁₁' A B p} : Proper ((→₁) --> flip (→₁)) p.
Proof. move=> ψ φ /=? a +. by apply use_mono₁₁. Qed.

#[export] Instance Mono₁₁_impl `{Mono₁₁' A B p} :
  Proper ((→₁) ==> (=) ==> (→₀)) p.
Proof. move=> φ ψ /=? a _ <- +. by apply use_mono₁₁. Qed.

#[export] Instance Mono₁₁_flip_impl `{Mono₁₁' A B p} :
  Proper ((→₁) --> (=) ==> flip (→₀)) p.
Proof. move=> ψ φ /=? a _ <- +. by apply use_mono₁₁. Qed.

(** ** [pnu]: Parameterized greatest fixpoint *)

Section pnu.
  Context {A : Type} {F : (A → Prop) → A → Prop}.

  (** [pnu]: Parameterized greatest fixpoint *)
  CoInductive pnu (φ : A → Prop) a : Prop := {
    (* The type is equivalent to [F (pnu $∨₁ φ) a] if [F] is monotone;
      parameterization by [pnuφ] serves for strict positivity *)
    pnu_out : ∃ pnuφ, (pnuφ →₁ pnu $∨₁ φ) ∧ F pnuφ a;
  }.

  (** Fold [pnu] *)
  Lemma pnu_fold {φ a} : F (pnu $∨₁ φ) a → pnu φ a.
  Proof. move=> ?. split. exists (pnu $∨₁ φ). split; by [move=> >|]. Qed.

  (** Unfold [pnu] *)
  Lemma pnu_unfold `{Mono₁₁ F} {φ a} : pnu φ a → F (pnu $∨₁ φ) a.
  Proof. move=> [[_[->]]]. done. Qed.

  (** Monotonicity of [pnu] *)
  #[export] Instance pnu_mono : Mono₁₁ pnu.
  Proof.
    move=> φ ψ φψ. cofix FIX=> a [[pnuφ[pnuφto ?]]]. split.
    exists pnuφ. split; [|done]=> ? /pnuφto[/FIX|/φψ]; by [left|right].
  Qed.

  (** Accumulate coinductive hypotheses *)
  Lemma pnu_acc `{Mono₁₁ F} {φ} ψ : (ψ →₁ pnu (φ ∨₁ ψ)) → ψ →₁ pnu φ.
  Proof.
    move=> topnuφψ=> a /topnuφψ +. move: a. cofix FIX=> a /pnu_unfold Fxa.
    split. exists (pnu $∨₁ (φ ∨₁ ψ)). split; [|done].
    move{a Fxa}=> ? [/FIX|[|/topnuφψ/FIX]]; by [left|right|left].
  Qed.

  (** [nu]: Non-parameterized greatest fixpoint *)
  Definition nu : A → Prop := pnu ⊥₁.

  (** Fold [nu] *)
  Lemma nu_fold `{Mono₁₁ F} {a} : F nu a → nu a.
  Proof.
    move=> Fnua. apply pnu_fold. move: Fnua. apply use_mono₁₁. move{a}=> a nua.
    left. move: nua. by apply use_mono₁₁.
  Qed.

  (** Unfold [nu] *)
  Lemma nu_unfold `{Mono₁₁ F} {a} : nu a → F nu a.
  Proof. move/pnu_unfold. apply use_mono₁₁. move=> _ [//|[]]. Qed.

  (** Prove a lower bound of [nu] via [pnu] *)
  Lemma nu_pnu `{Mono₁₁ F} φ : (φ →₁ pnu φ) → φ →₁ nu.
  Proof.
    move=> φpnuφ. apply pnu_acc=> a /φpnuφ. apply use_mono₁₁. move{a}=> a φa.
    by right.
  Qed.

  (** Prove a lower bound of [nu] via [F] *)
  Lemma nu_coind `{Mono₁₁ F} φ : (φ →₁ F φ) → φ →₁ nu.
  Proof.
    move=> φFφ. apply nu_pnu=> a /φFφ Fφa. apply pnu_fold. move: Fφa.
    apply use_mono₁₁. move{a}=> a Fφa. by right.
  Qed.
End pnu.

Arguments pnu {A} F φ a.
Arguments nu {A} F a.

(** ** [pmu]: Parameterized least fixpoint *)

Section pmu.
  Context {A : Type} {F : (A → Prop) → A → Prop}.

  (** [pmu]: Parameterized least fixpoint *)
  Inductive pmu (φ : A → Prop) a : Prop := {
    (* The type is equivalent to [F (pmu $∧₁ φ) a] if [F] is monotone;
      parameterization by [pmuφ] serves for strict positivity *)
    pmu_out : ∃ pmuφ, (pmuφ →₁ pmu $∧₁ φ) ∧ F pmuφ a;
  }.

  (** Fold [pmu] *)
  Lemma pmu_fold {φ a} : F (pmu $∧₁ φ) a → pmu φ a.
  Proof. move=> ?. split. exists (pmu $∧₁ φ). split; by [move=> >|]. Qed.

  (** Unfold [pmu] *)
  Lemma pmu_unfold `{Mono₁₁ F} {φ a} : pmu φ a → F (pmu $∧₁ φ) a.
  Proof. move=> [[_[->]]]. done. Qed.

  (** Monotonicity of [pmu] *)
  #[export] Instance pmu_mono : Mono₁₁ pmu.
  Proof.
    move=> φ ψ φψ ++. fix FIX 2=> a [[pmuφ[pmuφto ?]]]. split.
    exists pmuφ. split; [|done]=> ? /pmuφto[/FIX+ /φψ]//.
  Qed.

  (** Accumulate inductive hypotheses *)
  Lemma pmu_acc `{Mono₁₁ F} {φ} ψ : (pmu (φ ∧₁ ψ) →₁ ψ) → pmu φ →₁ ψ.
  Proof.
    move=> topmuφψ a pmuφa. apply topmuφψ. move: a pmuφa. fix FIX 2=> a.
    move=> [[pmuφ[pmuφto Fpmuφa]]]. apply pmu_fold. move: Fpmuφa.
    apply use_mono₁₁. move{a}=> a /pmuφto[/FIX pmuφψa φa].
    split; [done|]. split; [done|]. by apply topmuφψ.
  Qed.

  (** [mu]: Non-parameterized least fixpoint *)
  Definition mu : A → Prop := pmu ⊤₁.

  (** Fold [mu] *)
  Lemma mu_fold `{Mono₁₁ F} {a} : F mu a → mu a.
  Proof.
    move=> Fmua. apply pmu_fold. move: Fmua. apply use_mono₁₁. move{a}=> a mua.
    split; [|done]. move: mua. by apply use_mono₁₁.
  Qed.

  (** Unfold [mu] *)
  Lemma mu_unfold `{Mono₁₁ F} {a} : mu a → F mu a.
  Proof. move/pmu_unfold. apply use_mono₁₁. by move=> ?[??]. Qed.

  (** Prove an upper bound of [mu] via [pmu] *)
  Lemma mu_pmu `{Mono₁₁ F} {φ} : (pmu φ →₁ φ) → mu →₁ φ.
  Proof.
    move=> pmuφφ. apply pmu_acc=> a pmuφφa. apply pmuφφ. move: pmuφφa.
    apply use_mono₁₁. move{a}=> a [_]. done.
  Qed.

  (** Prove an upper bound of [mu] via [F] *)
  Lemma mu_ind `{Mono₁₁ F} φ : (F φ →₁ φ) → mu →₁ φ.
  Proof.
    move=> Fφφ. apply mu_pmu=> a /pmu_unfold Fpmuφa. apply Fφφ. move: Fpmuφa.
    apply use_mono₁₁. move{a}=> a [_]. done.
  Qed.
End pmu.

Arguments pmu {A} F φ a.
Arguments mu {A} F a.
