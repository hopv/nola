(** * [nProp]: Nola syntactic proposition *)

From nola.util Require Export tlist wft.
From iris.bi Require Import notation.

(** ** [nsx]: Syntactic extension for [nProp] *)

(** [nsxs]: Syntactic extension for both [nPropS] and [nPropL] *)
Structure nsxs : Type := Nsxs {
  (** Data *)
  nsxs_data : Type;
  (** Parameter for usual [nPropS]/[nPropL] arguments *)
  nsxs_paru : nsxs_data → Type;
  (** Parameter for contractive [nPropS] arguments *)
  nsxs_parcs : nsxs_data → Type;
  (** Parameter for contractive [nPropL] arguments *)
  nsxs_parcl : nsxs_data → Type;
}.

(** [nsxl]: Syntactic extension for [nPropL] only *)
Structure nsxl : Type := Nsxl {
  (** Data *)
  nsxl_data : Type;
  (** Parameter for usual [nPropL] arguments *)
  nsxl_paru : nsxl_data → Type;
  (** Parameter for contractive [nPropS] arguments *)
  nsxl_parcs : nsxl_data → Type;
  (** Parameter for contractive [nPropL] arguments *)
  nsxl_parcl : nsxl_data → Type;
}.

(** [nsx]: Syntactic extension for [nProp], combination of [nsxs] and [nsxl] *)
Record nsx : Type := Nsx { nsx_s :> nsxs; nsx_l :> nsxl; }.

(** ** [nctx]: Context of [nProp] *)

(** Context of variables, where each list element [A : Type] represents
  a function to small propositions [A → nPropSc] *)
Definition nctx := tlist Type.

(** [nvar]: Choice of a variable with an argument,
  representing a small proposition [nPropSc] *)
Definition nvar (Γ : nctx) : Type := [+] A ∈ Γ, A.

(** ** [nProp]: Nola syntactic proposition *)

(** [nsort]: Sort of [nProp], [nS] or [nL] *)
Variant nsort : Set := (** small *) nS | (** large *) nL.

(** [nProp]: Nola syntactic proposition

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [np_forall]/[np_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nProp] *)

Inductive nProp {Ξ : nsx} : nsort → tlist Type → tlist Type → Type :=
| (** Inner variable *) np_var {σ Γ Δ} : nvar Δ → nProp σ Γ Δ
| (** Outer variable, available only in [nPropL] *)
  np_ovar {Γ Δ} : nvar Γ → nProp nL Γ Δ
| (** Judgment derivability *)
  np_deriv {σ Δ} Γ (I : wft) :
    I → nProp nL ^[] (Γ ^++ Δ) → nProp nL ^[] (Γ ^++ Δ) → nProp σ Γ Δ
| (** Empty proposition *) np_emp {σ Γ Δ} : nProp σ Γ Δ
| (** Pure proposition *) np_pure {σ Γ Δ} : Prop → nProp σ Γ Δ
| (** Conjunction *) np_and {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ → nProp σ Γ Δ
| (** Disjunction *) np_or {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ → nProp σ Γ Δ
| (** Implication *) np_impl {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ → nProp σ Γ Δ
| (** Separating conjunction *)
  np_sep {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ → nProp σ Γ Δ
| (** Magic wand *) np_wand {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ → nProp σ Γ Δ
| (** Universal quantification *)
  np_forall {σ Γ Δ} (A : Type) : (A → nProp σ Γ Δ) → nProp σ Γ Δ
| (** Existential quantification *)
  np_exist {σ Γ Δ} (A : Type) : (A → nProp σ Γ Δ) → nProp σ Γ Δ
| (** Second-order universal quantification *)
  np_so_forall {σ Γ Δ} (A : Type) : nProp σ (A ^:: Γ) Δ → nProp σ Γ Δ
| (** Second-order existential quantification *)
  np_so_exist {σ Γ Δ} (A : Type) : nProp σ (A ^:: Γ) Δ → nProp σ Γ Δ
| (** Persistence modality *)
  np_persistently {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ
| (** Plainly modality *) np_plainly {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ
| (** Later modality

    Because it is contractive, its argument proposition can be in [nPropL]
    and have outer variables flushed

    For the users to aid type inference around [^++], we expose [Γ]
    as the explicit parameter (the same applies to [np_ex] and [np_exl]) *)
  np_later {σ} Γ {Δ} : nProp nL ^[] (Γ ^++ Δ) → nProp σ Γ Δ
| (** Basic update modality *) np_bupd {σ Γ Δ} : nProp σ Γ Δ → nProp σ Γ Δ
| (** Extension by [Ξ.(nsx_s)] *)
  np_ex {σ} Γ {Δ} d :
    (Ξ.(nsxs_paru) d → nProp σ Γ Δ) →
    (Ξ.(nsxs_parcs) d → nProp nS ^[] (Γ ^++ Δ)) →
    (Ξ.(nsxs_parcl) d → nProp nL ^[] (Γ ^++ Δ)) → nProp σ Γ Δ
| (** Extension by [Ξ.(nsx_l)] *)
  np_exl Γ {Δ} d :
    (Ξ.(nsxs_paru) d → nProp nL Γ Δ) →
    (Ξ.(nsxs_parcs) d → nProp nS ^[] (Γ ^++ Δ)) →
    (Ξ.(nsxs_parcl) d → nProp nL ^[] (Γ ^++ Δ)) → nProp nL Γ Δ.

Arguments nProp Ξ σ Γ Δ : clear implicits.

(** Notations for large or small [nProp] *)
Notation nPropL Ξ := (nProp Ξ nL).
Notation nPropS Ξ := (nProp Ξ nS).

(** Notations for closed [nProp] *)
Notation nPropLc Ξ := (nPropL Ξ ^[] ^[]).
Notation nPropSc Ξ := (nPropS Ξ ^[] ^[]).

(** Notations for connectives *)
Declare Scope nProp_scope.
Delimit Scope nProp_scope with nP.
Bind Scope nProp_scope with nProp.
Notation "% a" := (np_var a) (at level 99, no associativity) : nProp_scope.
Notation "%ₒ a" := (np_ovar a) (at level 99, no associativity) : nProp_scope.
Notation "P ⊢!{ i @ I }{ Γ } Q" := (np_deriv Γ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i }{ Γ } Q " := (np_deriv Γ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i @ I } Q" := (np_deriv _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢!{ i } Q" := (np_deriv _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nProp_scope.
Notation "'emp'" := (np_emp) : nProp_scope.
Notation "'⌜' φ '⌝'" := (np_pure φ%type%stdpp%nola) : nProp_scope.
Notation "'True'" := (np_pure True) : nProp_scope.
Notation "'False'" := (np_pure False) : nProp_scope.
Infix "∧" := np_and : nProp_scope.
Notation "(∧)" := np_and (only parsing) : nProp_scope.
Infix "∨" := np_or : nProp_scope.
Notation "(∨)" := np_or (only parsing) : nProp_scope.
Infix "→" := np_impl : nProp_scope.
Notation "¬ P" := (P → False)%nP : nProp_scope.
Infix "∗" := np_sep : nProp_scope.
Notation "(∗)" := np_sep (only parsing) : nProp_scope.
Infix "-∗" := np_wand : nProp_scope.
Notation "∀ x .. z , P" :=
  (np_forall _ (λ x, .. (np_forall _ (λ z, P%nP)) ..)) : nProp_scope.
Notation "∃ x .. z , P" :=
  (np_exist _ (λ x, .. (np_exist _ (λ z, P%nP)) ..)) : nProp_scope.
Notation "∀: A →nP , P" := (np_so_forall A P)
  (at level 200, right associativity,
  format "'[' '[' ∀:  A  →nP ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: A →nP , P" := (np_so_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nP ']' ,  '/' P ']'") : nProp_scope.
Notation "□ P" := (np_persistently P) : nProp_scope.
Notation "■ P" := (np_plainly P) : nProp_scope.
Notation "▷{ Γ } P" := (np_later Γ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (np_later _ P) : nProp_scope.
Notation "|==> P" := (np_bupd P) : nProp_scope.
