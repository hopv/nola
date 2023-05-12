(** * [nProp]: Syntactic proposition *)

From nola.examples.logic Require Export ctx.
From iris.bi Require Import notation.

(** ** [nProp]: Nola syntactic proposition

  Its universe level is strictly higher than those of [V : npvar]
  and the domain [A : Type] of [n_forall]/[n_exist].

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γₒ, Γᵢ] for smooth type inference

  In nominal proposition arguments (e.g., [n_deriv]'s arguments), outer
  variables are flushed into inner, with the context [(; Γₒ ^++ Γᵢ)];
  for connectives with such arguments we make [Γₒ] explicit for the users
  to aid type inference around [^++] *)

Inductive nProp : nsort → nctx → Type :=

(** Pure proposition *)
| n_pure {σ Γ} : Prop → nProp σ Γ
(** Conjunction *)
| n_and {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Disjunction *)
| n_or {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Implication *)
| n_impl {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Universal quantification *)
| n_forall {σ Γ} {A : Type} : (A → nProp σ Γ) → nProp σ Γ
(** Existential quantification *)
| n_exist {σ Γ} {A : Type} : (A → nProp σ Γ) → nProp σ Γ

(** Separating conjunction *)
| n_sep {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Magic wand *)
| n_wand {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Persistence modality *)
| n_persistently {σ Γ} : nProp σ Γ → nProp σ Γ
(** Plainly modality *)
| n_plainly {σ Γ} : nProp σ Γ → nProp σ Γ
(** Basic update modality *)
| n_bupd {σ Γ} : nProp σ Γ → nProp σ Γ

(** Later modality *)
| n_later {σ} Γₒ {Γᵢ} : nProp nL (; Γₒ ^++ Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Judgment derivability *)
| n_deriv {σ} Γₒ {Γᵢ} :
    nat → nProp nL (; Γₒ ^++ Γᵢ) → nProp nL (; Γₒ ^++ Γᵢ) → nProp σ (Γₒ; Γᵢ)

(** Recursive small proposition *)
| n_recs {σ Γₒ Γᵢ} {A : Type} :
    (A → nProp nS (A →nPS ^:: Γₒ; Γᵢ)) → A → nProp σ (Γₒ; Γᵢ)
(** Recursive large proposition *)
| n_recl {Γₒ Γᵢ} {A : Type} :
    (A → nProp nL (A →nPL ^:: Γₒ; Γᵢ)) → A → nProp nL (Γₒ; Γᵢ)
(** Universal quantification over [A → nProp] *)
| n_n_forall {σ Γₒ Γᵢ} V : nProp σ (V ^:: Γₒ; Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Existential quantification over [A → nProp] *)
| n_n_exist {σ Γₒ Γᵢ} V : nProp σ (V ^:: Γₒ; Γᵢ) → nProp σ (Γₒ; Γᵢ)

(** Inner small variable *)
| n_varis {σ Γₒ Γᵢ} : csum (nparg nS) Γᵢ → nProp σ (Γₒ; Γᵢ)
(** Inner large variable, [nPropL] only *)
| n_varil {Γₒ Γᵢ} : csum (nparg nL) Γᵢ → nProp nL (Γₒ; Γᵢ)
(** Outer small variable, [nPropL] only *)
| n_varos {Γₒ Γᵢ} : csum (nparg nS) Γₒ → nProp nL (Γₒ; Γᵢ).

Notation nPropS := (nProp nS).
Notation nPropL := (nProp nL).

(** ** Notations for [nProp] connectives *)

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.

Notation "'⌜' φ '⌝'" := (n_pure φ%type%stdpp%nola) : nProp_scope.
Notation "'True'" := (n_pure True) : nProp_scope.
Notation "'False'" := (n_pure False) : nProp_scope.
Infix "∧" := n_and : nProp_scope.
Notation "(∧)" := n_and (only parsing) : nProp_scope.
Infix "∨" := n_or : nProp_scope.
Notation "(∨)" := n_or (only parsing) : nProp_scope.
Infix "→" := n_impl : nProp_scope.
Notation "¬ P" := (n_impl P (n_pure False)) : nProp_scope.
Notation "∀' Φ" := (n_forall Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "∀ x .. z , P" :=
  (n_forall (λ x, .. (n_forall (λ z, P%n)) ..)) : nProp_scope.
Notation "∃' Φ" := (n_exist Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "∃ x .. z , P" :=
  (n_exist (λ x, .. (n_exist (λ z, P%n)) ..)) : nProp_scope.

Infix "∗" := n_sep : nProp_scope.
Notation "(∗)" := n_sep (only parsing) : nProp_scope.
Infix "-∗" := n_wand : nProp_scope.
Notation "□ P" := (n_persistently P) : nProp_scope.
Notation "■ P" := (n_plainly P) : nProp_scope.
Notation "|==> P" := (n_bupd P) : nProp_scope.

Notation "▷{ Γₒ } P" := (n_later Γₒ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_later _ P) : nProp_scope.
Notation "P ⊢!{ i }{ Γₒ } Q" := (n_deriv Γₒ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i } Q" := (n_deriv _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nProp_scope.

Notation "rec:ₛ' Φ" := (n_recs Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "rec:ₛ x , P" := (n_recs (λ x, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ₛ  x ,  '/' P ']' ']'") : nProp_scope.
Notation "rec:ₗ' Φ" := (n_recl Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "rec:ₗ x , P" := (n_recl (λ x, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ₗ  x ,  '/' P ']' ']'") : nProp_scope.
Notation "∀: V , P" := (n_n_forall V P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: V , P" := (n_n_exist V P)
  (at level 200, right associativity,
    format "'[' '[' ∃:  V ']' ,  '/' P ']'") : nProp_scope.

Notation "%ᵢₛ a" := (n_varis a) (at level 20, right associativity)
  : nProp_scope.
Notation "%ᵢₗ a" := (n_varil a) (at level 20, right associativity)
  : nProp_scope.
Notation "%ₒₛ a" := (n_varos a) (at level 20, right associativity)
  : nProp_scope.

(** ** [nlarge]: Turn [nProp σ] into [nPropL σ]
  Although the main interest is the case [σ = nS],
  we keep the function polymorphic over [σ] for ease of definition *)
Fixpoint nlarge {σ Γ} (P : nProp σ Γ) : nPropL Γ :=
  match P with
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => nlarge P ∧ nlarge Q
  | P ∨ Q => nlarge P ∨ nlarge Q
  | P → Q => nlarge P → nlarge Q
  | P ∗ Q => nlarge P ∗ nlarge Q
  | P -∗ Q => nlarge P -∗ nlarge Q
  | ∀' Φ => ∀' nlarge ∘ Φ
  | ∃' Φ => ∃' nlarge ∘ Φ
  | □ P => □ nlarge P
  | ■ P => ■ nlarge P
  | |==> P => |==> nlarge P
  | ▷ P => ▷ P
  | P ⊢!{i} Q => P ⊢!{i} Q
  | (rec:ₛ' Φ) a => (rec:ₛ' Φ) a
  | (rec:ₗ' Φ) a => (rec:ₗ' Φ) a
  | ∀: V, P => ∀: V, nlarge P
  | ∃: V, P => ∃: V, nlarge P
  | %ᵢₛ a => %ᵢₛ a
  | %ᵢₗ a => %ᵢₗ a
  | %ₒₛ a => %ₒₛ a
  end%n.
