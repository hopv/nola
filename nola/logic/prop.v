(** * [nProp]: Nola syntactic proposition *)

From nola.logic Require Export sx ctx.
From nola.util Require Export wft.
From iris.bi Require Import notation.

(** ** [nsort]: Sort of [nProp], [nS] or [nL] *)
Variant nsort : Set := (* small *) nS | (* large *) nL.

(** ** [nProp]: Nola syntactic proposition

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [n_forall]/[n_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nProp]

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γₒₛ, Γₛ] for smooth type inference

  In nominal proposition arguments (e.g., [n_deriv]'s arguments), outer
  variables are flushed into inner, with the context [(Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)];
  for connectives with such arguments we make [Γₒₛ, Γₒₗ] explicit for the users
  to aid type inference around [^++] *)

Inductive nProp {Ξ : nsx} : nsort → nctx → Type :=
(** Inner small variable *)
| n_vars {σ Γₒₛ Γₛ Γₒₗ Γₗ} : tysum Γₛ → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Inner large variable *)
| n_varl {σ Γₒₛ Γₛ Γₒₗ Γₗ} : tysum Γₗ → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Outer small variable, [nPropL] only *)
| n_varos {Γₒₛ Γₛ Γₒₗ Γₗ} : tysum Γₒₛ → nProp nL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Judgment derivability *)
| n_deriv {σ} Γₒₛ {Γₛ} Γₒₗ {Γₗ} (I : wft) :
    I → nProp nL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nProp nL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) →
    nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
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
(** Universal quantification over [A → nPropS] *)
| n_ns_forall {σ Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nProp σ (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Existential quantification over [A → nPropS] *)
| n_ns_exist {σ Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nProp σ (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Universal quantification over [A → nPropL] *)
| n_nl_forall {σ Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nProp σ (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Existential quantification over [A → nPropL] *)
| n_nl_exist {σ Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nProp σ (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Persistence modality *)
| n_persistently {σ Γ} : nProp σ Γ → nProp σ Γ
(** Plainly modality *)
| n_plainly {σ Γ} : nProp σ Γ → nProp σ Γ
(** Later modality *)
| n_later {σ} Γₒₛ {Γₛ} Γₒₗ {Γₗ} :
    nProp nL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Basic update modality *)
| n_bupd {σ Γ} : nProp σ Γ → nProp σ Γ
(** Proposition by [Ξ.(nsx_s)] *)
| n_sxs {σ} Γₒₛ {Γₛ} Γₒₗ {Γₗ} d :
    (Ξ.(nsx_s).(nesx_pu) d → nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Ξ.(nsx_s).(nesx_pns) d → nProp nS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Ξ.(nsx_s).(nesx_pnl) d → nProp nL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    nProp σ (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Proposition by [Ξ.(nsx_l)], [nProp nL] only *)
| n_sxl Γₒₛ {Γₛ} Γₒₗ {Γₗ} d :
    (Ξ.(nsx_l).(nesx_pu) d → nProp nL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Ξ.(nsx_l).(nesx_pns) d → nProp nS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Ξ.(nsx_l).(nesx_pnl) d → nProp nL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    nProp nL (Γₒₛ, Γₛ; Γₒₗ, Γₗ).

Arguments nProp Ξ σ Γ : clear implicits.

(** Small [nProp] *)
Notation nPropS Ξ := (nProp Ξ nS).

(** Large [nProp] *)
Notation nPropL Ξ := (nProp Ξ nL).

(** Propositions by [⊑esx] *)

Notation n_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ :=
  (n_sxs Γₒₛ Γₒₗ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).
Notation n_subsxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ :=
  (n_sxl Γₒₛ Γₒₗ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).

(** ** Notations for [nProp] connectives *)

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.

Notation "%ₛ a" := (n_vars a) (at level 99, no associativity) : nProp_scope.
Notation "%ₗ a" := (n_varl a) (at level 99, no associativity) : nProp_scope.
Notation "%ₒₛ a" := (n_varos a) (at level 99, no associativity) : nProp_scope.

Notation "P ⊢!{ i @ I }{ Γₒₛ ; Γₒₗ } Q" := (n_deriv Γₒₛ Γₒₗ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i }{ Γₒₛ ; Γₒₗ } Q " := (n_deriv Γₒₛ Γₒₗ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ } Q" := (n_deriv Γₒₛ _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i }{ Γₒₛ } Q " := (n_deriv Γₒₛ _ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i @ I } Q" := (n_deriv _ _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i } Q" := (n_deriv _ _ _ i P Q)
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

Notation "∀: A →nS , P" := (n_ns_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nS ']' ,  '/' P ']'") : nProp_scope.
Notation "∀: 'nS' , P" := (n_ns_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nS' ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: A →nS , P" := (n_ns_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nS ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: 'nS' , P" := (n_ns_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nS' ']' ,  '/' P ']'") : nProp_scope.

Notation "∀: A →nL , P" := (n_nl_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nL ']' ,  '/' P ']'") : nProp_scope.
Notation "∀: 'nL' , P" := (n_nl_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nL' ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: A →nL , P" := (n_nl_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nL ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: 'nL' , P" := (n_nl_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nL' ']' ,  '/' P ']'") : nProp_scope.

Notation "□ P" := (n_persistently P) : nProp_scope.
Notation "■ P" := (n_plainly P) : nProp_scope.
Notation "▷{ Γₒₛ ; Γₒₗ } P" := (n_later Γₒₛ Γₒₗ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷{ Γₒₛ } P" := (n_later Γₒₛ _ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_later _ _ P) : nProp_scope.
Notation "|==> P" := (n_bupd P) : nProp_scope.

Notation "+!! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_sxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nProp_scope.
Notation "+!!ₗ { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!!ₗ { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_sxl Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_sxl _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nProp_scope.

Notation "+! { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+! { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxs Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+! ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" := (n_subsxs _ _ d Φᵤ Φₙₛ Φₙₗ)
  : nProp_scope.
Notation "+!ₗ { Γₒₛ ; Γₒₗ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!ₗ { Γₒₛ } ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxl Γₒₛ _ d Φᵤ Φₙₛ Φₙₗ) (only parsing) : nProp_scope.
Notation "+!ₗ ( d ; Φᵤ ; Φₙₛ ; Φₙₗ )" :=
  (n_subsxl _ _ d Φᵤ Φₙₛ Φₙₗ) : nProp_scope.
