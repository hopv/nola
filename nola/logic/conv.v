(** * Conversion of [nProp] *)

From nola.logic Require Export prop.
From nola.util Require Import funext.

(** ** [nlarge]: Turn [nProp Ξ σ Γ] into [nPropL Ξ Γ]

  Although the main interest is the case [σ = nS],
  we keep the function polymorphic over [σ] for ease of definition *)

Fixpoint nlarge {Ξ σ Γ} (P : nProp Ξ σ Γ) : nPropL Ξ Γ :=
  match P with
  | (% a)%n => % a
  | (%ₒ a)%n => %ₒ a
  | (P ⊢!{i} Q)%n => P ⊢!{i} Q
  | ⌜φ⌝%n => ⌜φ⌝
  | (P ∧ Q)%n => nlarge P ∧ nlarge Q
  | (P ∨ Q)%n => nlarge P ∨ nlarge Q
  | (P → Q)%n => nlarge P → nlarge Q
  | (P ∗ Q)%n => nlarge P ∗ nlarge Q
  | (P -∗ Q)%n => nlarge P -∗ nlarge Q
  | (∀' Φ)%n => ∀' nlarge ∘ Φ
  | (∃' Φ)%n => ∃' nlarge ∘ Φ
  | (∀: v, P)%n => ∀: v, nlarge P
  | (∃: v, P)%n => ∃: v, nlarge P
  | (□ P)%n => □ nlarge P
  | (■ P)%n => ■ nlarge P
  | (▷ P)%n => ▷ P
  | (|==> P)%n => |==> nlarge P
  | (+!! (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!! (d; nlarge ∘ Φᵤ; Φₙₛ; Φₙₗ)
  | (+!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!!ₗ (d; nlarge ∘ Φᵤ; Φₙₛ; Φₙₗ)
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

#[export] Instance nsmall_nlarge {Ξ Γ P} : @Nsmall Ξ Γ (nlarge P) | 100 :=
  { nsmall := P; nsmall_eq := eq_refl }.
#[export] Instance nsmall_var {Ξ Γ a} : @Nsmall Ξ Γ (% a) :=
  { nsmall := % a; nsmall_eq := eq_refl }.
#[export] Instance nsmall_deriv {Ξ Γ I i P Q} : @Nsmall Ξ Γ (P ⊢!{i @ I} Q) :=
  { nsmall := P ⊢!{i} Q; nsmall_eq := eq_refl }.
#[export] Instance nsmall_pure {Ξ Γ φ} : @Nsmall Ξ Γ ⌜φ⌝ :=
  { nsmall := ⌜φ⌝; nsmall_eq := eq_refl }.
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
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_exist {Ξ Γ} `{!∀ x : A, Nsmall (Φ x)}
  : @Nsmall Ξ Γ (∃' Φ) := { nsmall := ∃ x, nsmall (Φ x) }.
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_n_forall {Ξ Γ v} `{!Nsmall P}
  : @Nsmall Ξ Γ (∀: v, P) := { nsmall := ∀: v, nsmall P }.
Next Obligation. move=>/= >. by rewrite nsmall_eq. Qed.
#[export] Program Instance nsmall_n_exist {Ξ Γ v} `{!Nsmall P}
  : @Nsmall Ξ Γ (∃: v, P) := { nsmall := ∃: v, nsmall P }.
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
#[export] Program Instance nsmall_sxs {Ξ Γ d Φₙₛ Φₙₗ}
  `{!∀ x, Nsmall (Φᵤ x)} : @Nsmall Ξ Γ (+!! (d; Φᵤ; Φₙₛ; Φₙₗ)) :=
  { nsmall := +!! (d; λ x, nsmall (Φᵤ x); Φₙₛ; Φₙₗ) }.
Next Obligation. move=>/= >. f_equal. funext=>/= ?. by rewrite nsmall_eq. Qed.
