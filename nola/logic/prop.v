(** * [nPropS], [nPropL]: Nola syntactic proposition *)

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

(** ** [nPropS], [nPropL]: Nola syntactic proposition, small and large

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [nps_forall]/[nps_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nPropS]/[nPropL] *)

(** [nPropS]: Nola syntactic proposition, small *)
Inductive nPropS {Ξ : nsx} : tlist Type → tlist Type → Type :=
(** Inner variable *)
| nps_var {Γ Δ} : nvar Δ → nPropS Γ Δ
(** Judgment derivability *)
| nps_deriv Γ {Δ} (I : wft) :
    I → nPropL ^[] (Γ ^++ Δ) → nPropL ^[] (Γ ^++ Δ) → nPropS Γ Δ
(** Empty proposition *)
| nps_emp {Γ Δ} : nPropS Γ Δ
(** Pure proposition *)
| nps_pure {Γ Δ} : Prop → nPropS Γ Δ
(** Conjunction *)
| nps_and {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Disjunction *)
| nps_or {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Implication *)
| nps_impl {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Separating conjunction *)
| nps_sep {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Magic wand *)
| nps_wand {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Universal quantification *)
| nps_forall {Γ Δ} (A : Type) : (A → nPropS Γ Δ) → nPropS Γ Δ
(** Existential quantification *)
| nps_exist {Γ Δ} (A : Type) : (A → nPropS Γ Δ) → nPropS Γ Δ
(** Second-order universal quantification over [A → nPropS] *)
| nps_so_forall {Γ Δ} (A : Type) : nPropS (A ^:: Γ) Δ → nPropS Γ Δ
(** Second-order existential quantification over [A → nPropS] *)
| nps_so_exist {Γ Δ} (A : Type) : nPropS (A ^:: Γ) Δ → nPropS Γ Δ
(** Persistence modality *)
| nps_persistently {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Plainly modality *)
| nps_plainly {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Later modality

  Because it is contractive, its argument proposition can be in [nPropL]
  and have outer variables flushed

  For the users to aid type inference around [^++], we expose [Γ]
  as the explicit parameter (the same applies to [nps_ex] and [nps_exl]) *)
| nps_later Γ {Δ} : nPropL ^[] (Γ ^++ Δ) → nPropS Γ Δ
(** Basic update modality *)
| nps_bupd {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Extension by [Ξ.(nsx_s)] *)
| nps_exs Γ {Δ} d :
    (Ξ.(nsxs_paru) d → nPropS Γ Δ) →
    (Ξ.(nsxs_parcs) d → nPropS ^[] (Γ ^++ Δ)) →
    (Ξ.(nsxs_parcl) d → nPropL ^[] (Γ ^++ Δ)) → nPropS Γ Δ

(** [nPropL]: Nola syntactic proposition, large

  Most connectives are the same as [nPropS] *)
with nPropL {Ξ : nsx} : tlist Type → tlist Type → Type :=
| npl_var {Γ Δ} : nvar Δ → nPropL Γ Δ
(** Outer variable, [nPropL] only *)
| npl_ovar {Γ Δ} : nvar Γ → nPropL Γ Δ
| npl_deriv Γ {Δ} (I : wft) :
    I → nPropL ^[] (Γ ^++ Δ) → nPropL ^[] (Γ ^++ Δ) → nPropL Γ Δ
| npl_emp {Γ Δ} : nPropL Γ Δ
| npl_pure {Γ Δ} : Prop → nPropL Γ Δ
| npl_and {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| npl_or {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| npl_impl {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| npl_sep {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| npl_wand {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| npl_forall {Γ Δ} (A : Type) : (A → nPropL Γ Δ) → nPropL Γ Δ
| npl_exist {Γ Δ} (A : Type) : (A → nPropL Γ Δ) → nPropL Γ Δ
| npl_so_forall {Γ Δ} (A : Type) : nPropL (A ^:: Γ) Δ → nPropL Γ Δ
| npl_so_exist {Γ Δ} (A : Type) : nPropL (A ^:: Γ) Δ → nPropL Γ Δ
| npl_persistently {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| npl_plainly {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| npl_later Γ {Δ} : nPropL ^[] (Γ ^++ Δ) → nPropL Γ Δ
| npl_bupd {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| npl_exs Γ {Δ} d :
    (Ξ.(nsxs_paru) d → nPropL Γ Δ) →
    (Ξ.(nsxs_parcs) d → nPropS ^[] (Γ ^++ Δ)) →
    (Ξ.(nsxs_parcl) d → nPropL ^[] (Γ ^++ Δ)) → nPropL Γ Δ
(** Extension by [Ξ.(nsx_l)], [nPropL] only *)
| npl_exl Γ {Δ} d :
    (Ξ.(nsxs_paru) d → nPropL Γ Δ) →
    (Ξ.(nsxs_parcs) d → nPropS ^[] (Γ ^++ Δ)) →
    (Ξ.(nsxs_parcl) d → nPropL ^[] (Γ ^++ Δ)) → nPropL Γ Δ.

Arguments nPropS Ξ Γ Δ : clear implicits.
Arguments nPropL Ξ Γ Δ : clear implicits.
(** Closed [nPropS]/[nPropL] *)
Notation nPropSc Ξ := (nPropS Ξ ^[] ^[]).
Notation nPropLc Ξ := (nPropL Ξ ^[] ^[]).

(** Notations for connectives *)
Declare Scope nPropS_scope.
Delimit Scope nPropS_scope with nS.
Bind Scope nPropS_scope with nPropS.
Declare Scope nPropL_scope.
Delimit Scope nPropL_scope with nL.
Bind Scope nPropL_scope with nPropL.
Notation "% a" := (nps_var a) (at level 99, no associativity) : nPropS_scope.
Notation "% a" := (npl_var a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₒ a" := (npl_ovar a) (at level 99, no associativity) : nPropL_scope.
Notation "P ⊢!{ i @ I }{ Γ } Q" := (nps_deriv Γ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I }{ Γ } Q" := (npl_deriv Γ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i }{ Γ } Q " := (nps_deriv Γ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i }{ Γ } Q" := (npl_deriv Γ _ i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i @ I } Q" := (nps_deriv _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I } Q" := (npl_deriv _ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i } Q" := (nps_deriv _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nPropS_scope.
Notation "P ⊢!{ i } Q" := (npl_deriv _ _ i P Q)
  (format "P  ⊢!{ i }  Q") : nPropL_scope.
Notation "'emp'" := (nps_emp) : nPropS_scope.
Notation "'emp'" := (npl_emp) : nPropL_scope.
Notation "'⌜' φ '⌝'" := (nps_pure φ%type%stdpp%nola) : nPropS_scope.
Notation "'⌜' φ '⌝'" := (npl_pure φ%type%stdpp%nola) : nPropL_scope.
Notation "'True'" := (nps_pure True) : nPropS_scope.
Notation "'True'" := (npl_pure True) : nPropL_scope.
Notation "'False'" := (nps_pure False) : nPropS_scope.
Notation "'False'" := (npl_pure False) : nPropL_scope.
Infix "∧" := nps_and : nPropS_scope.
Infix "∧" := npl_and : nPropL_scope.
Notation "(∧)" := nps_and (only parsing) : nPropS_scope.
Notation "(∧)" := npl_and (only parsing) : nPropL_scope.
Infix "∨" := nps_or : nPropS_scope.
Infix "∨" := npl_or : nPropL_scope.
Notation "(∨)" := nps_or (only parsing) : nPropS_scope.
Notation "(∨)" := npl_or (only parsing) : nPropL_scope.
Infix "→" := nps_impl : nPropS_scope.
Infix "→" := npl_impl : nPropL_scope.
Notation "¬ P" := (P → False)%nS : nPropS_scope.
Notation "¬ P" := (P → False)%nL : nPropL_scope.
Infix "∗" := nps_sep : nPropS_scope.
Infix "∗" := npl_sep : nPropL_scope.
Notation "(∗)" := nps_sep (only parsing) : nPropS_scope.
Notation "(∗)" := npl_sep (only parsing) : nPropL_scope.
Infix "-∗" := nps_wand : nPropS_scope.
Infix "-∗" := npl_wand : nPropL_scope.
Notation "∀ x .. z , P" :=
  (nps_forall _ (λ x, .. (nps_forall _ (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∀ x .. z , P" :=
  (npl_forall _ (λ x, .. (npl_forall _ (λ z, P%nL)) ..)) : nPropL_scope.
Notation "∃ x .. z , P" :=
  (nps_exist _ (λ x, .. (nps_exist _ (λ z, P%nS)) ..)) : nPropS_scope.
Notation "∃ x .. z , P" :=
  (npl_exist _ (λ x, .. (npl_exist _ (λ z, P%nL)) ..)) : nPropL_scope.
Notation "∀: A →nP , P" := (nps_so_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nP ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nP , P" := (npl_so_forall A P) : nPropL_scope.
Notation "∃: A →nP , P" := (nps_so_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nP ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nP , P" := (npl_so_exist A P) : nPropL_scope.
Notation "□ P" := (nps_persistently P) : nPropS_scope.
Notation "□ P" := (npl_persistently P) : nPropL_scope.
Notation "■ P" := (nps_plainly P) : nPropS_scope.
Notation "■ P" := (npl_plainly P) : nPropL_scope.
Notation "▷{ Γ } P" := (nps_later Γ P)
  (at level 20, right associativity, only parsing) : nPropS_scope.
Notation "▷{ Γ } P" := (npl_later Γ P) (only parsing) : nPropL_scope.
Notation "▷ P" := (nps_later _ P) : nPropS_scope.
Notation "▷ P" := (npl_later _ P) : nPropL_scope.
Notation "|==> P" := (nps_bupd P) : nPropS_scope.
Notation "|==> P" := (npl_bupd P) : nPropL_scope.
