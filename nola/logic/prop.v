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

(** Context of variables, where each list element [A : Type] represents
  a function to small propositions [A → nPropSc] *)
Definition nctx := tlist Type.

(** [nvar]: Choice of a variable with an argument,
  representing a small proposition [nPropSc] *)
Definition nvar (Γ : nctx) : Type := [+] A ∈ Γ, A.

(** ** [nPropS], [nPropL]: Nola syntactic proposition, small and large

  Its universe level is strictly higher than those of [Γ : nctx],
  the index [I : wft] of the judgment derivability,
  and the domain [A : Type] of [ns_forall]/[ns_exists]

  We make [Ξ] implicit for each constructor;
  we later make it explicit for [nPropS]/[nPropL] *)

(** [nPropS]: Nola syntactic proposition, small *)
Inductive nPropS {Ξ : nsx} : tlist Type → tlist Type → Type :=
(** Inner variable *)
| ns_var {Γ Δ} : nvar Δ → nPropS Γ Δ
(** Judgment derivability *)
| ns_deriv Γ {Δ} (I : wft) :
    I → nPropL ^[] (Γ ^++ Δ) → nPropL ^[] (Γ ^++ Δ) → nPropS Γ Δ
(** Empty proposition *)
| ns_emp {Γ Δ} : nPropS Γ Δ
(** Pure proposition *)
| ns_pure {Γ Δ} : Prop → nPropS Γ Δ
(** Conjunction *)
| ns_and {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Disjunction *)
| ns_or {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Implication *)
| ns_impl {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Separating conjunction *)
| ns_sep {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Magic wand *)
| ns_wand {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ → nPropS Γ Δ
(** Universal quantification *)
| ns_forall {Γ Δ} {A : Type} : (A → nPropS Γ Δ) → nPropS Γ Δ
(** Existential quantification *)
| ns_exist {Γ Δ} {A : Type} : (A → nPropS Γ Δ) → nPropS Γ Δ
(** Second-order universal quantification over [A → nPropS] *)
| ns_so_forall {Γ Δ} (A : Type) : nPropS (A ^:: Γ) Δ → nPropS Γ Δ
(** Second-order existential quantification over [A → nPropS] *)
| ns_so_exist {Γ Δ} (A : Type) : nPropS (A ^:: Γ) Δ → nPropS Γ Δ
(** Persistence modality *)
| ns_persistently {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Plainly modality *)
| ns_plainly {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Later modality

  Because it is contractive, its argument proposition can be in [nPropL]
  and have outer variables flushed

  For the users to aid type inference around [^++], we expose [Γ]
  as the explicit parameter (the same applies to [ns_ex] and [ns_exl]) *)
| ns_later Γ {Δ} : nPropL ^[] (Γ ^++ Δ) → nPropS Γ Δ
(** Basic update modality *)
| ns_bupd {Γ Δ} : nPropS Γ Δ → nPropS Γ Δ
(** Extension by [Ξ.(nsx_s)] *)
| ns_exs Γ {Δ} : let '(Nsxs _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_s) in
    ∀ d, (Pᵤ d → nPropS Γ Δ) → (Pₙₛ d → nPropS ^[] (Γ ^++ Δ)) →
    (Pₙₗ d → nPropL ^[] (Γ ^++ Δ)) → nPropS Γ Δ

(** [nPropL]: Nola syntactic proposition, large

  Most connectives are the same as [nPropS] *)
with nPropL {Ξ : nsx} : tlist Type → tlist Type → Type :=
| nl_var {Γ Δ} : nvar Δ → nPropL Γ Δ
(** Outer variable, [nPropL] only *)
| nl_ovar {Γ Δ} : nvar Γ → nPropL Γ Δ
| nl_deriv Γ {Δ} (I : wft) :
    I → nPropL ^[] (Γ ^++ Δ) → nPropL ^[] (Γ ^++ Δ) → nPropL Γ Δ
| nl_emp {Γ Δ} : nPropL Γ Δ
| nl_pure {Γ Δ} : Prop → nPropL Γ Δ
| nl_and {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| nl_or {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| nl_impl {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| nl_sep {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| nl_wand {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ → nPropL Γ Δ
| nl_forall {Γ Δ} {A : Type} : (A → nPropL Γ Δ) → nPropL Γ Δ
| nl_exist {Γ Δ} {A : Type} : (A → nPropL Γ Δ) → nPropL Γ Δ
| nl_so_forall {Γ Δ} (A : Type) : nPropL (A ^:: Γ) Δ → nPropL Γ Δ
| nl_so_exist {Γ Δ} (A : Type) : nPropL (A ^:: Γ) Δ → nPropL Γ Δ
| nl_persistently {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| nl_plainly {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| nl_later Γ {Δ} : nPropL ^[] (Γ ^++ Δ) → nPropL Γ Δ
| nl_bupd {Γ Δ} : nPropL Γ Δ → nPropL Γ Δ
| nl_exs Γ {Δ} : let '(Nsxs _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_s) in
    ∀ d, (Pᵤ d → nPropL Γ Δ) → (Pₙₛ d → nPropS ^[] (Γ ^++ Δ)) →
    (Pₙₗ d → nPropL ^[] (Γ ^++ Δ)) → nPropL Γ Δ
(** Extension by [Ξ.(nsx_l)], [nPropL] only *)
| nl_exl Γ {Δ} : let '(Nsxl _ Pᵤ Pₙₛ Pₙₗ) := Ξ.(nsx_l) in
    ∀ d, (Pᵤ d → nPropL Γ Δ) → (Pₙₛ d → nPropS ^[] (Γ ^++ Δ)) →
    (Pₙₗ d → nPropL ^[] (Γ ^++ Δ)) → nPropL Γ Δ.

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
Notation "% a" := (ns_var a) (at level 99, no associativity) : nPropS_scope.
Notation "% a" := (nl_var a) (at level 99, no associativity) : nPropL_scope.
Notation "%ₒ a" := (nl_ovar a) (at level 99, no associativity) : nPropL_scope.
Notation "P ⊢!{ i @ I }{ Γ } Q" := (ns_deriv Γ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I }{ Γ } Q" := (nl_deriv Γ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i }{ Γ } Q " := (ns_deriv Γ _ i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i }{ Γ } Q" := (nl_deriv Γ _ i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i @ I } Q" := (ns_deriv _ I i P Q)
  (at level 99, Q at level 200, only parsing) : nPropS_scope.
Notation "P ⊢!{ i @ I } Q" := (nl_deriv _ I i P Q)
  (only parsing): nPropL_scope.
Notation "P ⊢!{ i } Q" := (ns_deriv _ _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢!{ i }  Q") : nPropS_scope.
Notation "P ⊢!{ i } Q" := (nl_deriv _ _ i P Q)
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
Notation "∀: A →nS , P" := (ns_so_forall A P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: A →nS , P" := (nl_so_forall A P) : nPropL_scope.
Notation "∀: 'nS' , P" := (ns_so_forall unit P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∀: 'nS' , P" := (nl_so_forall unit P) : nPropL_scope.
Notation "∃: A →nS , P" := (ns_so_exist A P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  A  →nS ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: A →nS , P" := (nl_so_exist A P) : nPropL_scope.
Notation "∃: 'nS' , P" := (ns_so_exist unit P)
  (at level 200, right associativity,
  format "'[' '[' ∃:  'nS' ']' ,  '/' P ']'") : nPropS_scope.
Notation "∃: 'nS' , P" := (nl_so_exist unit P) : nPropL_scope.
Notation "□ P" := (ns_persistently P) : nPropS_scope.
Notation "□ P" := (nl_persistently P) : nPropL_scope.
Notation "■ P" := (ns_plainly P) : nPropS_scope.
Notation "■ P" := (nl_plainly P) : nPropL_scope.
Notation "▷{ Γ } P" := (ns_later Γ P)
  (at level 20, right associativity, only parsing) : nPropS_scope.
Notation "▷{ Γ } P" := (nl_later Γ P) (only parsing) : nPropL_scope.
Notation "▷ P" := (ns_later _ P) : nPropS_scope.
Notation "▷ P" := (nl_later _ P) : nPropL_scope.
Notation "|==> P" := (ns_bupd P) : nPropS_scope.
Notation "|==> P" := (nl_bupd P) : nPropL_scope.

(** ** [nlarge]: Turn [nPropS] into [nPropL] *)

Fixpoint nlarge {Ξ : nsx} {Γ Δ : nctx} (P : nPropS Ξ Γ Δ) : nPropL Ξ Γ Δ :=
  match P with
  | (% a)%nS => % a
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
  | (□ P)%nS => □ nlarge P
  | (■ P)%nS => ■ nlarge P
  | (▷ P)%nS => ▷ P
  | (|==> P)%nS => |==> nlarge P
  | ns_exs _ d Φᵤ Φₙₛ Φₙₗ => nl_exs _ d (nlarge ∘ Φᵤ) Φₙₛ Φₙₗ
  end.

(** ** [Nsmall]: [nPropL] that can be turned into [nPropS] *)

Class Nsmall {Ξ Γ Δ} (P : nPropL Ξ Γ Δ) := {
  (** [nsmall]: Turn [P : nPropL] into [nPropS] *)
  nsmall : nPropS Ξ Γ Δ;
  (** [nlarge (nsmall P) = P] *)
  nsmall_eq : nlarge nsmall = P
}.
Arguments nsmall {Ξ Γ Δ} P {_}.

(** [Nsmall] instances *)

#[export] Instance nsmall_var {Ξ Γ Δ a} : @Nsmall Ξ Γ Δ (% a) :=
  { nsmall := % a; nsmall_eq := eq_refl }.
#[export] Instance nsmall_deriv {Ξ Γ Δ I i P Q} : @Nsmall Ξ Γ Δ (P ⊢!{i @ I} Q)
  := { nsmall := P ⊢!{i} Q; nsmall_eq := eq_refl }.
#[export] Instance nsmall_pure {Ξ Γ Δ φ} : @Nsmall Ξ Γ Δ ⌜φ⌝ :=
  { nsmall := ⌜φ⌝; nsmall_eq := eq_refl }.
#[export] Instance nsmall_emp {Ξ Γ Δ} : @Nsmall Ξ Γ Δ emp :=
  { nsmall := emp; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_and {Ξ Γ Δ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ Δ (P ∧ Q) := { nsmall := nsmall P ∧ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_or {Ξ Γ Δ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ Δ (P ∨ Q) := { nsmall := nsmall P ∨ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_impl {Ξ Γ Δ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ Δ (P → Q) := { nsmall := nsmall P → nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_sep {Ξ Γ Δ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ Δ (P ∗ Q) := { nsmall := nsmall P ∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_wand {Ξ Γ Δ} `{!Nsmall P, !Nsmall Q}
  : @Nsmall Ξ Γ Δ (P -∗ Q) := { nsmall := nsmall P -∗ nsmall Q }.
Next Obligation. move=>/= >. by rewrite !nsmall_eq. Qed.
#[export] Program Instance nsmall_forall {Ξ Γ Δ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ Δ (∀' Φ) := { nsmall := ∀ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exist {Ξ Γ Δ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ Δ (∃' Φ) := { nsmall := ∃ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_so_forall {Ξ Γ Δ A} `{!Nsmall P}
  : @Nsmall Ξ Γ Δ (∀: A →nS, P) := { nsmall := ∀: _ →nS, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_so_exist {Ξ Γ Δ A} `{!Nsmall P}
  : @Nsmall Ξ Γ Δ (∃: A →nS, P) := { nsmall := ∃: _ →nS, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_persistently {Ξ Γ Δ} `{!Nsmall P}
  : @Nsmall Ξ Γ Δ (□ P) := { nsmall := □ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_plainly {Ξ Γ Δ} `{!Nsmall P}
  : @Nsmall Ξ Γ Δ (■ P) := { nsmall := ■ nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_later {Ξ Γ Δ P}
  : @Nsmall Ξ Γ Δ (▷ P) := { nsmall := ▷ P; nsmall_eq := eq_refl }.
#[export] Program Instance nsmall_bupd {Ξ Γ Δ} `{!Nsmall P}
  : @Nsmall Ξ Γ Δ (|==> P) := { nsmall := |==> nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exs {Ξ Γ Δ d Φᵤ Φₙₛ Φₙₗ}
  `{!∀ x, Nsmall (Φᵤ x)} : @Nsmall Ξ Γ Δ (nl_exs _ d Φᵤ Φₙₛ Φₙₗ) :=
  { nsmall := ns_exs Γ d (λ x, nsmall (Φᵤ x)) Φₙₛ Φₙₗ}.
Next Obligation. move=>/= >. f_equal. fun_ext=>/= ?. by rewrite nsmall_eq. Qed.
