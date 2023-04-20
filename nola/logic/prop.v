(** * [nPropS], [nPropL]: Nola syntactic proposition *)

From nola.util Require Export tlist wft.
From iris.bi Require Import notation.

(** ** [nsx]: Syntactic extension for [nProp] *)

(** [nsxs]: Syntactic extension for both [nPropS] and [nPropL] *)

#[projections(primitive)]
Structure nsxs : Type := Nsxs {
  (** Data *)
  nsxs_data : Type;
  (** Parameter for usual [nPropS]/[nPropL] arguments *)
  #[canonical=no] nsxs_paru : nsxs_data → Type;
  (** Parameter for nominal [nPropS] arguments *)
  #[canonical=no] nsxs_parns : nsxs_data → Type;
  (** Parameter for nominal [nPropL] arguments *)
  #[canonical=no] nsxs_parnl : nsxs_data → Type;
}.

(** [nsxl]: Syntactic extension for [nPropL] only *)

#[projections(primitive)]
Structure nsxl : Type := Nsxl {
  (** Data *)
  nsxl_data : Type;
  (** Parameter for usual [nPropL] arguments *)
  #[canonical=no] nsxl_paru : nsxl_data → Type;
  (** Parameter for nominal [nPropS] arguments *)
  #[canonical=no] nsxl_parns : nsxl_data → Type;
  (** Parameter for nominal [nPropL] arguments *)
  #[canonical=no] nsxl_parnl : nsxl_data → Type;
}.

(** [nsx]: Syntactic extension for [nProp], combination of [nsxs] and [nsxl] *)

#[projections(primitive)]
Record nsx : Type := Nsx { nsx_s :> nsxs; nsx_l :> nsxl; }.

(** ** [nctx]: Context of [nProp] *)

(** [nectx]: Elemental context of [nProp] *)
Definition nectx : Type := tlist Type.

(** [nctx]: Global context of [nProp] *)
#[projections(primitive)]
Record nctx : Type := Nctx {
  (** Outer small proposition variables *)
  nctx_os : nectx;
  (** Inner small proposition variables *)
  nctx_s : nectx;
  (** Outer large proposition variables *)
  nctx_ol : nectx;
  (** Inner large proposition variables *)
  nctx_l : nectx;
}.

Declare Scope nctx_scope.
Delimit Scope nctx_scope with nctx.
Bind Scope nctx_scope with nctx.
Notation "( Γₒₛ , Γₛ ; Γₒₗ , Γₗ )" := (Nctx Γₒₛ Γₛ Γₒₗ Γₗ) : nctx_scope.
Notation "( Γₛ ; Γₗ )" := (Nctx ^[] Γₛ ^[] Γₗ) : nctx_scope.
Notation "( Γₒₛ , Γₛ ; )" := (Nctx Γₒₛ Γₛ ^[] ^[]) : nctx_scope.
Notation "( Γₛ ; )" := (Nctx ^[] Γₛ ^[] ^[]) : nctx_scope.
Notation "( ; Γₒₗ , Γₗ )" := (Nctx ^[] ^[] Γₒₗ Γₗ)
  (format "( ;  Γₒₗ ,  Γₗ )") : nctx_scope.
Notation "( ; Γₗ )" := (Nctx ^[] ^[] ^[] Γₗ) (format "( ;  Γₗ )") : nctx_scope.
Notation "( ; )" := (Nctx ^[] ^[] ^[] ^[]) (format "( ; )") : nctx_scope.

(** Pick one variable in an elemental context with an argument value *)
Definition npick (Γₑ : nectx) : Type := [+] A ∈ Γₑ, A.

(** ** [nPropS], [nPropL]: Nola syntactic proposition, small and large

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [ns_forall]/[ns_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nPropS]/[nPropL]

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γₒₛ, Γₛ] for smooth type inference

  In nominal proposition arguments (e.g., [ns_deriv]'s arguments), outer
  variables are flushed into inner, with the context [(Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)];
  for connectives with such arguments we make [Γₒₛ, Γₒₗ] explicit for the users
  to aid type inference around [^++] *)

(** [nPropS]: Nola syntactic proposition, small *)
Inductive nPropS {Ξ : nsx} : nctx → Type :=
(** Inner small variable *)
| ns_vars {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₛ → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Inner large variable *)
| ns_varl {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₗ → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Judgment derivability *)
| ns_deriv Γₒₛ {Γₛ} Γₒₗ {Γₗ} (I : wft) :
    I → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) →
    nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Empty proposition *)
| ns_emp {Γ} : nPropS Γ
(** Pure proposition *)
| ns_pure {Γ} : Prop → nPropS Γ
(** Conjunction *)
| ns_and {Γ} : nPropS Γ → nPropS Γ → nPropS Γ
(** Disjunction *)
| ns_or {Γ} : nPropS Γ → nPropS Γ → nPropS Γ
(** Implication *)
| ns_impl {Γ} : nPropS Γ → nPropS Γ → nPropS Γ
(** Separating conjunction *)
| ns_sep {Γ} : nPropS Γ → nPropS Γ → nPropS Γ
(** Magic wand *)
| ns_wand {Γ} : nPropS Γ → nPropS Γ → nPropS Γ
(** Universal quantification *)
| ns_forall {Γ} {A : Type} : (A → nPropS Γ) → nPropS Γ
(** Existential quantification *)
| ns_exist {Γ} {A : Type} : (A → nPropS Γ) → nPropS Γ
(** Universal quantification over [A → nPropS] *)
| ns_ns_forall {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropS (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Existential quantification over [A → nPropS] *)
| ns_ns_exist {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropS (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Universal quantification over [A → nPropL] *)
| ns_nl_forall {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropS (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Existential quantification over [A → nPropL] *)
| ns_nl_exist {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropS (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Persistence modality *)
| ns_persistently {Γ} : nPropS Γ → nPropS Γ
(** Plainly modality *)
| ns_plainly {Γ} : nPropS Γ → nPropS Γ
(** Later modality *)
| ns_later Γₒₛ {Γₛ} Γₒₗ {Γₗ} :
    nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Basic update modality *)
| ns_bupd {Γ} : nPropS Γ → nPropS Γ
(** Extension by [Ξ.(nsx_s)] *)
| ns_exs Γₒₛ {Γₛ} Γₒₗ {Γₗ} : let '(Nsxs _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_s) in
    ∀ d, (Pᵤ d → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Pₙₛ d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Pₙₗ d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)

(** [nPropL]: Nola syntactic proposition, large

  Most connectives are the same as [nPropS] *)
with nPropL {Ξ : nsx} : nctx → Type :=
| nl_vars {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₛ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_varl {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₗ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Outer small variable, [nPropL] only *)
| nl_varos {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₛ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_deriv Γₒₛ {Γₛ} Γₒₗ {Γₗ} (I : wft) :
    I → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) →
    nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_emp {Γ} : nPropL Γ
| nl_pure {Γ} : Prop → nPropL Γ
| nl_and {Γ} : nPropL Γ → nPropL Γ → nPropL Γ
| nl_or {Γ} : nPropL Γ → nPropL Γ → nPropL Γ
| nl_impl {Γ} : nPropL Γ → nPropL Γ → nPropL Γ
| nl_sep {Γ} : nPropL Γ → nPropL Γ → nPropL Γ
| nl_wand {Γ} : nPropL Γ → nPropL Γ → nPropL Γ
| nl_forall {Γ} {A : Type} : (A → nPropL Γ) → nPropL Γ
| nl_exist {Γ} {A : Type} : (A → nPropL Γ) → nPropL Γ
| nl_ns_forall {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropL (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_ns_exist {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropL (A ^:: Γₒₛ, Γₛ; Γₒₗ, Γₗ) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_nl_forall {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropL (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_nl_exist {Γₒₛ Γₛ Γₒₗ Γₗ} (A : Type) :
    nPropL (Γₒₛ, Γₛ; A ^:: Γₒₗ, Γₗ) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_persistently {Γ} : nPropL Γ → nPropL Γ
| nl_plainly {Γ} : nPropL Γ → nPropL Γ
| nl_later Γₒₛ {Γₛ} Γₒₗ {Γₗ} :
    nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_bupd {Γ} : nPropL Γ → nPropL Γ
| nl_exs Γₒₛ {Γₛ} Γₒₗ {Γₗ} : let '(Nsxs _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_s) in
    ∀ d, (Pᵤ d → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Pₙₛ d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Pₙₗ d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Extension by [Ξ.(nsx_l)], [nPropL] only *)
| nl_exl Γₒₛ {Γₛ} Γₒₗ {Γₗ} : let '(Nsxl _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_l) in
    ∀ d, (Pᵤ d → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Pₙₛ d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Pₙₗ d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ).

Arguments nPropS Ξ Γ : clear implicits.
Arguments nPropL Ξ Γ : clear implicits.

(** Notations for connectives *)
Declare Scope nPropS_scope.
Delimit Scope nPropS_scope with nS.
Bind Scope nPropS_scope with nPropS.
Declare Scope nPropL_scope.
Delimit Scope nPropL_scope with nL.
Bind Scope nPropL_scope with nPropL.
Notation "%ₛ a" := (ns_vars a) (at level 99, no associativity) : nPropS_scope.
Notation "%ₛ a" := (nl_vars a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₗ a" := (ns_varl a) (at level 99, no associativity) : nPropS_scope.
Notation "%ₗ a" := (nl_varl a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₒₛ a" := (nl_varos a) (at level 99, no associativity) : nPropL_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ ; Γₒₗ } Q" := (ns_deriv Γₒₛ Γₒₗ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I }{ Γₒₛ ; Γₒₗ } Q" := (nl_deriv Γₒₛ Γₒₗ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i }{ Γₒₛ ; Γₒₗ } Q " := (ns_deriv Γₒₛ Γₒₗ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i }{ Γₒₛ ; Γₒₗ } Q" := (nl_deriv Γₒₛ Γₒₗ _ i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i @ I } Q" := (ns_deriv _ _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I } Q" := (nl_deriv _ _ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i } Q" := (ns_deriv _ _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nPropS_scope.
Notation "P ⊢!{ i } Q" := (nl_deriv _ _ _ i P Q)
  (format "P  ⊢!{ i }  Q") : nPropL_scope.
Notation "'emp'" := (ns_emp) : nPropS_scope.
Notation "'emp'" := (nl_emp) : nPropL_scope.
Notation "'⌜' φ '⌝'" := (ns_pure φ%type%stdpp%nola) : nPropS_scope.
Notation "'⌜' φ '⌝'" := (nl_pure φ%type%stdpp%nola) : nPropL_scope.
Notation "'True'" := (ns_pure True) : nPropS_scope.
Notation "'True'" := (nl_pure True) : nPropL_scope.
Notation "'False'" := (ns_pure False) : nPropS_scope.
Notation "'False'" := (nl_pure False) : nPropL_scope.
Infix "∧" := ns_and : nPropS_scope.
Infix "∧" := nl_and : nPropL_scope.
Notation "(∧)" := ns_and (only parsing) : nPropS_scope.
Notation "(∧)" := nl_and (only parsing) : nPropL_scope.
Infix "∨" := ns_or : nPropS_scope.
Infix "∨" := nl_or : nPropL_scope.
Notation "(∨)" := ns_or (only parsing) : nPropS_scope.
Notation "(∨)" := nl_or (only parsing) : nPropL_scope.
Infix "→" := ns_impl : nPropS_scope.
Infix "→" := nl_impl : nPropL_scope.
Notation "¬ P" := (P → False)%nS : nPropS_scope.
Notation "¬ P" := (P → False)%nL : nPropL_scope.
Infix "∗" := ns_sep : nPropS_scope.
Infix "∗" := nl_sep : nPropL_scope.
Notation "(∗)" := ns_sep (only parsing) : nPropS_scope.
Notation "(∗)" := nl_sep (only parsing) : nPropL_scope.
Infix "-∗" := ns_wand : nPropS_scope.
Infix "-∗" := nl_wand : nPropL_scope.
Notation "∀' Φ" := (ns_forall Φ)
  (at level 200, right associativity, only parsing) : nPropS_scope.
Notation "∀' Φ" := (nl_forall Φ) (only parsing) : nPropL_scope.
Notation "∀ x .. z , P" :=
  (ns_forall (λ x, .. (ns_forall (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∀ x .. z , P" :=
  (nl_forall (λ x, .. (nl_forall (λ z, P%nL)) ..)) : nPropL_scope.
Notation "∃' Φ" := (ns_exist Φ)
  (at level 200, right associativity, only parsing) : nPropS_scope.
Notation "∃' Φ" := (nl_exist Φ) (only parsing) : nPropL_scope.
Notation "∃ x .. z , P" :=
  (ns_exist (λ x, .. (ns_exist (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∃ x .. z , P" :=
  (nl_exist (λ x, .. (nl_exist (λ z, P%nL)) ..)) : nPropL_scope.
Notation "∀: A →nS , P" := (ns_ns_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nS , P" := (nl_ns_forall A P) : nPropL_scope.
Notation "∀: 'nS' , P" := (ns_ns_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: 'nS' , P" := (nl_ns_forall unit P) : nPropL_scope.
Notation "∃: A →nS , P" := (ns_ns_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nS , P" := (nl_ns_exist A P) : nPropL_scope.
Notation "∃: 'nS' , P" := (ns_ns_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: 'nS' , P" := (nl_ns_exist unit P) : nPropL_scope.
Notation "∀: A →nL , P" := (ns_nl_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nL ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nL , P" := (nl_nl_forall A P) : nPropL_scope.
Notation "∀: 'nL' , P" := (ns_nl_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nL' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: 'nL' , P" := (nl_nl_forall unit P) : nPropL_scope.
Notation "∃: A →nL , P" := (ns_nl_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nL ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nL , P" := (nl_nl_exist A P) : nPropL_scope.
Notation "∃: 'nL' , P" := (ns_nl_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nL' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: 'nL' , P" := (nl_nl_exist unit P) : nPropL_scope.
Notation "□ P" := (ns_persistently P) : nPropS_scope.
Notation "□ P" := (nl_persistently P) : nPropL_scope.
Notation "■ P" := (ns_plainly P) : nPropS_scope.
Notation "■ P" := (nl_plainly P) : nPropL_scope.
Notation "▷{ Γₒₛ ; Γₒₗ } P" := (ns_later Γₒₛ Γₒₗ P)
  (at level 20, right associativity, only parsing) : nPropS_scope.
Notation "▷{ Γₒₛ ; Γₒₗ } P" := (nl_later Γₒₛ Γₒₗ P)
  (only parsing) : nPropL_scope.
Notation "▷ P" := (ns_later _ _ P) : nPropS_scope.
Notation "▷ P" := (nl_later _ _ P) : nPropL_scope.
Notation "|==> P" := (ns_bupd P) : nPropS_scope.
Notation "|==> P" := (nl_bupd P) : nPropL_scope.

(** ** [nlarge]: Turn [nPropS] into [nPropL] *)

Fixpoint nlarge {Ξ : nsx} {Γ : nctx} (P : nPropS Ξ Γ) : nPropL Ξ Γ :=
  match P with
  | (%ₛ a)%nS => %ₛ a
  | (%ₗ a)%nS => %ₗ a
  | (P ⊢!{i} Q)%nS => P ⊢!{i} Q
  | emp%nS => emp
  | ⌜φ⌝%nS => ⌜φ⌝
  | (P ∧ Q)%nS => nlarge P ∧ nlarge Q
  | (P ∨ Q)%nS => nlarge P ∨ nlarge Q
  | (P → Q)%nS => nlarge P → nlarge Q
  | (P ∗ Q)%nS => nlarge P ∗ nlarge Q
  | (P -∗ Q)%nS => nlarge P -∗ nlarge Q
  | (∀' Φ)%nS => ∀' nlarge ∘ Φ
  | (∃' Φ)%nS => ∃' nlarge ∘ Φ
  | (∀: _ →nS, P)%nS => ∀: _ →nS, nlarge P
  | (∃: _ →nS, P)%nS => ∃: _ →nS, nlarge P
  | (∀: _ →nL, P)%nS => ∀: _ →nL, nlarge P
  | (∃: _ →nL, P)%nS => ∃: _ →nL, nlarge P
  | (□ P)%nS => □ nlarge P
  | (■ P)%nS => ■ nlarge P
  | (▷ P)%nS => ▷ P
  | (|==> P)%nS => |==> nlarge P
  | ns_exs _ _ d Φᵤ Φₙₛ Φₙₗ => nl_exs _ _ d (nlarge ∘ Φᵤ) Φₙₛ Φₙₗ
  end.

(** ** [Nsmall]: [nPropL] that can be turned into [nPropS] *)

Class Nsmall {Ξ Γ} (P : nPropL Ξ Γ) := {
  (** [nsmall]: Turn [P : nPropL] into [nPropS] *)
  nsmall : nPropS Ξ Γ;
  (** [nlarge (nsmall P) = P] *)
  nsmall_eq : nlarge nsmall = P
}.
Arguments nsmall {Ξ Γ} P {_}.

(** [Nsmall] instances *)

#[export] Instance nsmall_vars {Ξ Γ a} : @Nsmall Ξ Γ (%ₛ a) :=
  { nsmall := %ₛ a; nsmall_eq := eq_refl }.
#[export] Instance nsmall_varl {Ξ Γ a} : @Nsmall Ξ Γ (%ₗ a) :=
  { nsmall := %ₗ a; nsmall_eq := eq_refl }.
#[export] Instance nsmall_deriv {Ξ Γ I i P Q} : @Nsmall Ξ Γ (P ⊢!{i @ I} Q)
  := { nsmall := P ⊢!{i} Q; nsmall_eq := eq_refl }.
#[export] Instance nsmall_pure {Ξ Γ φ} : @Nsmall Ξ Γ ⌜φ⌝ :=
  { nsmall := ⌜φ⌝; nsmall_eq := eq_refl }.
#[export] Instance nsmall_emp {Ξ Γ} : @Nsmall Ξ Γ emp :=
  { nsmall := emp; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_and {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∧ Q) := { nsmall := nsmall P ∧ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_or {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∨ Q) := { nsmall := nsmall P ∨ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_impl {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P → Q) := { nsmall := nsmall P → nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_sep {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P ∗ Q) := { nsmall := nsmall P ∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_wand {Ξ Γ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ (P -∗ Q) := { nsmall := nsmall P -∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_forall {Ξ Γ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ (∀' Φ) := { nsmall := ∀ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exist {Ξ Γ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ (∃' Φ) := { nsmall := ∃ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_ns_forall {Ξ Γ A} `{!Nsmall P}
  : @Nsmall Ξ Γ (∀: A →nS, P) := { nsmall := ∀: _ →nS, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_ns_exist {Ξ Γ A} `{!Nsmall P}
  : @Nsmall Ξ Γ (∃: A →nS, P) := { nsmall := ∃: _ →nS, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_nl_forall {Ξ Γ A} `{!Nsmall P}
  : @Nsmall Ξ Γ (∀: A →nL, P) := { nsmall := ∀: _ →nL, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_nl_exist {Ξ Γ A} `{!Nsmall P}
  : @Nsmall Ξ Γ (∃: A →nL, P) := { nsmall := ∃: _ →nL, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_persistently {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (□ P) := { nsmall := □ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_plainly {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (■ P) := { nsmall := ■ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_later {Ξ Γ P}
  : @Nsmall Ξ Γ (▷ P) := { nsmall := ▷ P; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_bupd {Ξ Γ} `{!Nsmall P}
  : @Nsmall Ξ Γ (|==> P) := { nsmall := |==> nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exs {Ξ Γ d Φᵤ Φₙₛ Φₙₗ}
  `{!∀ x, Nsmall (Φᵤ x)} : @Nsmall Ξ Γ (nl_exs _ _ d Φᵤ Φₙₛ Φₙₗ) :=
  { nsmall := ns_exs _ _ d (λ x, nsmall (Φᵤ x)) Φₙₛ Φₙₗ}.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.