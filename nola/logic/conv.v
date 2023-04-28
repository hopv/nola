(** * Conversion of [nProp] *)

From nola.logic Require Export prop.
From nola.util Require Import funext.
Import EqNotations.

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

(** ** [nrewi eq P]: Rewrite the inner context of [P : nProp] with [eq] *)

Notation nrewi eq P := (rew[λ Γᵢ, nProp _ _ (; Γᵢ)] eq in P) (only parsing).

(** ** [ninserti], [ninserto]: Insert a variable to [nProp] *)

(** [ninserti]: Insert an inner variable to [nProp] *)

Fixpoint ninserti {Ξ σ Γₒ Γᵢ} (v : nvar) (i : nat) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (Γₒ; tinsert v i Γᵢ) :=
  match P with
  | (% a)%n => % cinsert v i a
  | (%ₒ a)%n => %ₒ a
  | (P ⊢!{ j } Q)%n =>
      nrewi tinsert_lapp (ninserti v _ P) ⊢!{ j }
        nrewi tinsert_lapp (ninserti v _ Q)
  | ⌜φ⌝%n => ⌜φ⌝
  | (P ∧ Q)%n => ninserti v i P ∧ ninserti v i Q
  | (P ∨ Q)%n => ninserti v i P ∨ ninserti v i Q
  | (P → Q)%n => ninserti v i P → ninserti v i Q
  | (P ∗ Q)%n => ninserti v i P ∗ ninserti v i Q
  | (P -∗ Q)%n => ninserti v i P -∗ ninserti v i Q
  | (∀' Φ)%n => ∀ a, ninserti v i (Φ a)
  | (∃' Φ)%n => ∃ a, ninserti v i (Φ a)
  | (∀: w, P)%n => ∀: w, ninserti v i P
  | (∃: w, P)%n => ∃: w, ninserti v i P
  | (□ P)%n => □ ninserti v i P
  | (■ P)%n => ■ ninserti v i P
  | (▷ P)%n => ▷ nrewi tinsert_lapp (ninserti v _ P)
  | (|==> P)%n => |==> ninserti v i P
  | (+!! (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!! (d; λ a, ninserti v i (Φᵤ a);
      λ a, nrewi tinsert_lapp (ninserti v _ (Φₙₛ a));
      λ a, nrewi tinsert_lapp (ninserti v _ (Φₙₗ a)))
  | (+!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!!ₗ (d; λ a, ninserti v i (Φᵤ a);
      λ a, nrewi tinsert_lapp (ninserti v _ (Φₙₛ a));
      λ a, nrewi tinsert_lapp (ninserti v _ (Φₙₗ a)))
  end.

(** [naddi]: Add an inner variable to [nProp] *)

Definition naddi {Ξ σ Γₒ Γᵢ} (v : nvar) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (Γₒ; v ^:: Γᵢ) := ninserti v 0 P.

(** [ninserto]: Insert an outer variable to [nProp] *)

Fixpoint ninserto {Ξ σ Γₒ Γᵢ} (v : nvar) (i : nat) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (tinsert v i Γₒ; Γᵢ) :=
  match P with
  | (% a)%n => % a
  | (%ₒ a)%n => %ₒ cinsert v i a
  | (P ⊢!{ j } Q)%n =>
      nrewi tinsert_rapp (ninserti v _ P) ⊢!{ j }
        nrewi tinsert_rapp (ninserti v _ Q)
  | ⌜φ⌝%n => ⌜φ⌝
  | (P ∧ Q)%n => ninserto v i P ∧ ninserto v i Q
  | (P ∨ Q)%n => ninserto v i P ∨ ninserto v i Q
  | (P → Q)%n => ninserto v i P → ninserto v i Q
  | (P ∗ Q)%n => ninserto v i P ∗ ninserto v i Q
  | (P -∗ Q)%n => ninserto v i P -∗ ninserto v i Q
  | (∀' Φ)%n => ∀ a, ninserto v i (Φ a)
  | (∃' Φ)%n => ∃ a, ninserto v i (Φ a)
  | (∀: w, P)%n => ∀: w, ninserto v (S i) P
  | (∃: w, P)%n => ∃: w, ninserto v (S i) P
  | (□ P)%n => □ ninserto v i P
  | (■ P)%n => ■ ninserto v i P
  | (▷ P)%n => ▷ nrewi tinsert_rapp (ninserti v _ P)
  | (|==> P)%n => |==> ninserto v i P
  | (+!! (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!! (d; λ a, ninserto v i (Φᵤ a);
      λ a, nrewi tinsert_rapp (ninserti v _ (Φₙₛ a));
      λ a, nrewi tinsert_rapp (ninserti v _ (Φₙₗ a)))
  | (+!!ₗ (d; Φᵤ; Φₙₛ; Φₙₗ))%n => +!!ₗ (d; λ a, ninserto v i (Φᵤ a);
      λ a, nrewi tinsert_rapp (ninserti v _ (Φₙₛ a));
      λ a, nrewi tinsert_rapp (ninserti v _ (Φₙₗ a)))
  end.

(** [naddo]: Add an outer variable to [nProp] *)

Definition naddo {Ξ σ Γₒ Γᵢ} (v : nvar) (P : nProp Ξ σ (Γₒ; Γᵢ))
  : nProp Ξ σ (v ^:: Γₒ; Γᵢ) := ninserto v 0 P.
