(** * [nProp]: Nola syntactic proposition *)

From nola.logic Require Export sx ctx.
From nola.util Require Export wft.
From iris.bi Require Import notation.

(** ** [nProp]: Nola syntactic proposition

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [n_forall]/[n_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nProp]

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γₒ, Γᵢ] for smooth type inference

  In nominal proposition arguments (e.g., [n_deriv]'s arguments), outer
  variables are flushed into inner, with the context [(; Γₒ ^++ Γᵢ)];
  for connectives with such arguments we make [Γₒ] explicit for the users
  to aid type inference around [^++] *)

Inductive nProp {Ξ : nsx} : nsort → nctx → Type :=
(** Inner small variable *)
| n_varis {σ Γₒ Γᵢ} : csum (nparg nS) Γᵢ → nProp σ (Γₒ; Γᵢ)
(** Inner large variable, [nPropL] only *)
| n_varil {Γₒ Γᵢ} : csum (nparg nL) Γᵢ → nProp nL (Γₒ; Γᵢ)
(** Outer small variable, [nPropL] only *)
| n_varos {Γₒ Γᵢ} : csum (nparg nS) Γₒ → nProp nL (Γₒ; Γᵢ)
(** Judgment derivability *)
| n_deriv {σ} Γₒ {Γᵢ} (I : wft) :
    I → nProp nL (; Γₒ ^++ Γᵢ) → nProp nL (; Γₒ ^++ Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Pure proposition *)
| n_pure {σ Γ} : Prop → nProp σ Γ
(** Conjunction *)
| n_and {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Disjunction *)
| n_or {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Implication *)
| n_impl {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Separating conjunction *)
| n_sep {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Magic wand *)
| n_wand {σ Γ} : nProp σ Γ → nProp σ Γ → nProp σ Γ
(** Universal quantification *)
| n_forall {σ Γ} {A : Type} : (A → nProp σ Γ) → nProp σ Γ
(** Existential quantification *)
| n_exist {σ Γ} {A : Type} : (A → nProp σ Γ) → nProp σ Γ
(** Universal quantification over [A → nProp] *)
| n_n_forall {σ Γₒ Γᵢ} V : nProp σ (V ^:: Γₒ; Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Existential quantification over [A → nProp] *)
| n_n_exist {σ Γₒ Γᵢ} V : nProp σ (V ^:: Γₒ; Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Persistence modality *)
| n_persistently {σ Γ} : nProp σ Γ → nProp σ Γ
(** Plainly modality *)
| n_plainly {σ Γ} : nProp σ Γ → nProp σ Γ
(** Later modality *)
| n_later {σ} Γₒ {Γᵢ} : nProp nL (; Γₒ ^++ Γᵢ) → nProp σ (Γₒ; Γᵢ)
(** Basic update modality *)
| n_bupd {σ Γ} : nProp σ Γ → nProp σ Γ
(** Proposition by [Ξ.(nsx_s)] *)
| n_sxs {σ} Γₒ {Γᵢ} d :
    (Ξ.(nsx_s).(nesx_pu) d → nProp σ (Γₒ; Γᵢ)) →
    (Ξ.(nsx_s).(nesx_pns) d → nProp nS (; Γₒ ^++ Γᵢ)) →
    (Ξ.(nsx_s).(nesx_pnl) d → nProp nL (; Γₒ ^++ Γᵢ)) → nProp σ (Γₒ; Γᵢ)
(** Proposition by [Ξ.(nsx_l)], [nProp nL] only *)
| n_sxl Γₒ {Γᵢ} d :
    (Ξ.(nsx_l).(nesx_pu) d → nProp nL (Γₒ; Γᵢ)) →
    (Ξ.(nsx_l).(nesx_pns) d → nProp nS (; Γₒ ^++ Γᵢ)) →
    (Ξ.(nsx_l).(nesx_pnl) d → nProp nL (; Γₒ ^++ Γᵢ)) → nProp nL (Γₒ; Γᵢ).

Arguments nProp Ξ σ Γ : clear implicits.

(** Small [nProp] *)
Notation nPropS Ξ := (nProp Ξ nS).

(** Large [nProp] *)
Notation nPropL Ξ := (nProp Ξ nL).

(** Propositions by [⊑esx] *)

Notation n_subsxs Γₒ d Φᵤ Φₙₛ Φₙₗ :=
  (n_sxs Γₒ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).
Notation n_subsxl Γₒ d Φᵤ Φₙₛ Φₙₗ :=
  (n_sxl Γₒ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).

(** ** Notations for [nProp] connectives *)

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.

Notation "%ᵢₛ a" := (n_varis a) (at level 20, right associativity)
  : nProp_scope.
Notation "%ᵢₗ a" := (n_varil a) (at level 20, right associativity)
  : nProp_scope.
Notation "%ₒₛ a" := (n_varos a) (at level 20, right associativity)
  : nProp_scope.

Notation "P ⊢!{ i @ I }{ Γₒ } Q" := (n_deriv Γₒ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i }{ Γₒ } Q " := (n_deriv Γₒ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i @ I } Q" := (n_deriv _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i } Q" := (n_deriv _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nProp_scope.

Notation "'⌜' φ '⌝'" := (n_pure φ%type%stdpp%nola) : nProp_scope.
Notation "'True'" := (n_pure True) : nProp_scope.
Notation "'False'" := (n_pure False) : nProp_scope.
Infix "∧" := n_and : nProp_scope.
Notation "(∧)" := n_and (only parsing) : nProp_scope.
Infix "∨" := n_or : nProp_scope.
Notation "(∨)" := n_or (only parsing) : nProp_scope.
Infix "→" := n_impl : nProp_scope.
Notation "¬ P" := (n_impl P (n_pure False)) : nProp_scope.

Infix "∗" := n_sep : nProp_scope.
Notation "(∗)" := n_sep (only parsing) : nProp_scope.
Infix "-∗" := n_wand : nProp_scope.

Notation "∀' Φ" := (n_forall Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "∀ x .. z , P" :=
  (n_forall (λ x, .. (n_forall (λ z, P%n)) ..)) : nProp_scope.
Notation "∃' Φ" := (n_exist Φ)
  (at level 200, right associativity, only parsing) : nProp_scope.
Notation "∃ x .. z , P" :=
  (n_exist (λ x, .. (n_exist (λ z, P%n)) ..)) : nProp_scope.

Notation "∀: V , P" := (n_n_forall V P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: V , P" := (n_n_exist V P)
  (at level 200, right associativity,
    format "'[' '[' ∃:  V ']' ,  '/' P ']'") : nProp_scope.

Notation "□ P" := (n_persistently P) : nProp_scope.
Notation "■ P" := (n_plainly P) : nProp_scope.
Notation "▷{ Γₒ } P" := (n_later Γₒ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_later _ P) : nProp_scope.
Notation "|==> P" := (n_bupd P) : nProp_scope.

Notation "+!! { Γₒ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxs Γₒ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_sxs _ d Φᵤ Φₙₛ Φₙₗ) : nProp_scope.
Notation "+!!ₗ { Γₒ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxl Γₒ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_sxl _ d Φᵤ Φₙₛ Φₙₗ) : nProp_scope.

Notation "+! { Γₒ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxs Γₒ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_subsxs _ d Φᵤ Φₙₛ Φₙₗ) : nProp_scope.
Notation "+!ₗ { Γₒ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxl Γₒ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxl _ d Φᵤ Φₙₛ Φₙₗ) : nProp_scope.
