(** * [nPropS], [nPropL]: Nola syntactic proposition *)

From nola.logic Require Export sx.
From nola.util Require Import tlist wft.

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
(** Proposition by [Ξ.(nsx_s)] *)
| ns_sxs Γₒₛ {Γₛ} Γₒₗ {Γₗ} d :
    (Ξ.(nsx_s).(nesx_pu) d → nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Ξ.(nsx_s).(nesx_pns) d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Ξ.(nsx_s).(nesx_pnl) d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    nPropS (Γₒₛ, Γₛ; Γₒₗ, Γₗ)

(** [nPropL]: Nola syntactic proposition, large

  Most connectives are the same as [nPropS] *)
with nPropL {Ξ : nsx} : nctx → Type :=
| nl_vars {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₛ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_varl {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₗ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Outer small variable, [nPropL] only *)
| nl_varos {Γₒₛ Γₛ Γₒₗ Γₗ} : npick Γₒₛ → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
| nl_deriv Γₒₛ {Γₛ} Γₒₗ {Γₗ} (I : wft) :
    I → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ) →
    nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
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
| nl_sxs Γₒₛ {Γₛ} Γₒₗ {Γₗ} d :
    (Ξ.(nsx_s).(nesx_pu) d → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Ξ.(nsx_s).(nesx_pns) d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Ξ.(nsx_s).(nesx_pnl) d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)
(** Proposition by [Ξ.(nsx_l)], [nPropL] only *)
| nl_sxl Γₒₛ {Γₛ} Γₒₗ {Γₗ} d :
    (Ξ.(nsx_l).(nesx_pu) d → nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ)) →
    (Ξ.(nsx_l).(nesx_pns) d → nPropS (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    (Ξ.(nsx_l).(nesx_pnl) d → nPropL (Γₒₛ ^++ Γₛ; Γₒₗ ^++ Γₗ)) →
    nPropL (Γₒₛ, Γₛ; Γₒₗ, Γₗ).

Arguments nPropS Ξ Γ : clear implicits.
Arguments nPropL Ξ Γ : clear implicits.

(** Propositions by [⊑esx] *)

Notation ns_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ :=
  (ns_sxs Γₒₛ Γₒₗ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).
Notation nl_subsxs Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ :=
  (nl_sxs Γₒₛ Γₒₗ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).
Notation nl_subsxl Γₒₛ Γₒₗ d Φᵤ Φₙₛ Φₙₗ :=
  (nl_sxl Γₒₛ Γₒₗ (nsubesx_d d)
    (Φᵤ ∘ nsubesx_pu d) (Φₙₛ ∘ nsubesx_pns d) (Φₙₗ ∘ nsubesx_pnl d)).
