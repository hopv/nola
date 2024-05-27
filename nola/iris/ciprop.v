(** * [ciProp]: Coinductive-inductive proposition *)

From nola.util Require Export fn cit.
From nola.bi Require Import ofe.
From nola.iris Require Export ofe.
Import iPropAppNotation.

(** ** Data types *)

(** [cip_binsel]: Binary operator selector *)
Variant cip_binsel :=
| (** Conjunction *) cips_and
| (** Disjunction *) cips_or
| (** Implication *) cips_imp
| (** Separating conjunction *) cips_sep
| (** Magic wand *) cips_wand.

(** [cip_unsel]: Unary operator selector *)
Variant cip_unsel :=
| (** Plainly *) cips_plain
| (** Persistently *) cips_pers
| (** Basic update *) cips_bupd
| (** Except-0 *) cips_except0.

(** [cip_sel]: Selector *)
Variant cip_sel S :=
| (** Universal quantifier *) cips_all (A : Type)
| (** Existential quantifier *) cips_ex (A : Type)
| (** Binary operator *) cips_bin (s : cip_binsel)
| (** Unary operator *) cips_un (s : cip_unsel)
| (** Pure proposition *) cips_pure
| (** Later *) cips_later
| (** Custom selector *) cips_custom (s : S).
Arguments cips_all {_}. Arguments cips_ex {_}.
Arguments cips_bin {_}.  Arguments cips_un {_}.
Arguments cips_pure {_}. Arguments cips_later {_}. Arguments cips_custom {_}.

(** [cip_idom]: Domain for inductive parts *)
Definition cip_idom {S} (I : S → Type) (s : cip_sel S) : Type := match s with
  | cips_all A | cips_ex A => A | cips_bin _ => bool | cips_un _ => unit
  | cips_pure | cips_later => Empty_set | cips_custom s => I s
  end.

(** [cip_cdom]: Domain for coinductive parts *)
Definition cip_cdom {S} (C : S → Type) (s : cip_sel S) : Type := match s with
  | cips_all _ | cips_ex _ | cips_bin _ | cips_un _ | cips_pure | cips_later =>
      Empty_set
  | cips_custom s => C s
  end.

(** [cip_dataOF]: Data [oFunctor] *)
Definition cip_dataOF {S} (D : S → oFunctor) (s : cip_sel S) : oFunctor :=
  match s with
  | cips_all _ | cips_ex _ | cips_bin _ | cips_un _ => unitO
  | cips_pure => PropO | cips_later => laterOF ∙ | cips_custom s => D s
  end.

(** [cip_dataOF] is contractive *)
#[export] Instance cip_dataOF_contractive {S s}
  `{∀ s : S, oFunctorContractive (D s)} : oFunctorContractive (cip_dataOF D s).
Proof. case s=>/=; exact _. Qed.

(** ** [ciProp]: Coinductive-inductive proposition *)
Definition ciPropOF {S} I C D : oFunctor :=
  citOF (cip_idom (S:=S) I) (cip_cdom C) (cip_dataOF D).
Definition ciProp {S} I C D Σ : Type := ciPropOF (S:=S) I C D $oi Σ.

(** [ciPropOF] is contractive *)
Fact ciPropOF_contractive {S I C} `{∀ s, oFunctorContractive (D s)} :
  oFunctorContractive (@ciPropOF S I C D).
Proof. exact _. Qed.

(** ** Construct [ciProp] *)
Section ciProp.
  Context {S} {I C : S → Type} {D : S → oFunctor} {Σ : gFunctors}.
  Implicit Type Px Qx : ciProp I C D Σ.

  Definition cip_all {A} (Φxs : A -d> ciProp I C D Σ) : ciProp I C D Σ :=
    CitX (cips_all A) Φxs nullary ().
  Definition cip_ex {A} (Φxs : A -d> ciProp I C D Σ) : ciProp I C D Σ :=
    CitX (cips_ex A) Φxs nullary ().

  Definition cip_bin s Px Qx : ciProp I C D Σ :=
    CitX (cips_bin s) (binary Px Qx) nullary ().
  Definition cip_and := cip_bin cips_and.
  Definition cip_or := cip_bin cips_or.
  Definition cip_imp := cip_bin cips_imp.
  Definition cip_sep := cip_bin cips_sep.
  Definition cip_wand := cip_bin cips_wand.

  Definition cip_un s Px : ciProp I C D Σ :=
    CitX (cips_un s) (unary Px) nullary ().
  Definition cip_plain := cip_un cips_plain.
  Definition cip_pers := cip_un cips_pers.
  Definition cip_bupd := cip_un cips_bupd.
  Definition cip_except0 := cip_un cips_except0.

  Definition cip_pure (φ : Prop) : ciProp I C D Σ :=
    CitX cips_pure nullary nullary φ.
  Definition cip_later (P : iProp Σ) : ciProp I C D Σ :=
    CitX cips_later nullary nullary (Next P%I).

  Definition cip_custom s (Φxs : I s -d> ciProp I C D Σ)
    (Ψxs : C s -d> ciProp I C D Σ) (d : D s $oi Σ) : ciProp I C D Σ :=
    CitX (cips_custom s) Φxs Ψxs d.

  (** Non-expansiveness *)
  #[export] Instance cip_all_ne {A} : NonExpansive (@cip_all A).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_ex_ne {A} : NonExpansive (@cip_ex A).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_bin_ne {s} : NonExpansive2 (cip_bin s).
  Proof. move=> ???????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_un_ne {s} : NonExpansive (cip_un s).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_pure_ne : NonExpansive cip_pure.
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_later_ne : NonExpansive cip_later.
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cip_custom_ne {s} : NonExpansive3 (cip_custom s).
  Proof. move=> ??????????. apply Cit_ne, CitI_ne; solve_proper. Qed.
End ciProp.

Declare Scope ciProp_scope.
Delimit Scope ciProp_scope with n.
Bind Scope ciProp_scope with ciProp.
Notation "∀ x .. y , Px" :=
  (cip_all (λ x, .. (cip_all (λ y, Px%n)) ..)) : ciProp_scope.
Notation "∃ x .. y , Px" :=
  (cip_ex (λ x, .. (cip_ex (λ y, Px%n)) ..)) : ciProp_scope.
Infix "→" := cip_imp : ciProp_scope.
Infix "∗" := cip_sep : ciProp_scope.
Infix "-∗" := cip_wand : ciProp_scope.
Notation "■ Px" := (cip_plain Px) : ciProp_scope.
Notation "□ Px" := (cip_pers Px) : ciProp_scope.
Notation "|==> Px" := (cip_bupd Px) : ciProp_scope.
Notation "◇ Px" := (cip_except0 Px) : ciProp_scope.
Notation "⌜ φ ⌝" := (cip_pure φ) : ciProp_scope.
Notation "'True'" := (cip_pure True) : ciProp_scope.
Notation "'False'" := (cip_pure False) : ciProp_scope.
Notation "▷ P" := (cip_later P) : ciProp_scope.

(** ** [cip_intp]: Interpretation of [ciProp] *)
Section iris.
  Context {S} {I C : S → Type} {D : S → oFunctor} {Σ : gFunctors}.

  (** [cip_bintp]: Base interpretation for [ciProp] *)
  Definition cip_bintp
    (ip : ∀ s, (I s -d> iProp Σ) → (C s -d> ciProp I C D Σ) →
      D s $oi Σ → iProp Σ) s
    : (cip_idom I s -d> iProp Σ) → (cip_cdom C s -d> ciProp I C D Σ) →
        cip_dataOF D s $oi Σ → iProp Σ :=
    match s with
    | cips_all _ => λ Ps _ _, ∀ a, Ps a | cips_ex _ => λ Ps _ _, ∃ a, Ps a
    | cips_bin s => λ Ps _ _, let P := Ps true in let Q := Ps false in
        match s with
        | cips_and => P ∧ Q | cips_or => P ∨ Q | cips_imp => P → Q
        | cips_sep => P ∗ Q | cips_wand => P -∗ Q
        end
    | cips_un s => λ Ps _ _, let P := Ps () in
        match s with
        | cips_plain => ■ P | cips_pers => □ P | cips_bupd => |==> P
        | cips_except0 => ◇ P
        end
    | cips_pure => λ _ _ φ, ⌜φ⌝ | cips_later => λ _ _, laterl
    | cips_custom s => ip s
    end%I.

  (** [cip_bintp] is non-expansive *)
  #[export] Instance cip_bintp_ne `{!∀ s, NonExpansive3 (ip s)} {s} :
    NonExpansive3 (cip_bintp ip s).
  Proof.
    case s=>/=; try solve_proper. move=> ???????. by apply laterl_ne.
  Qed.

  (** [cip_intp]: Interpretation of [ciProp] *)
  Definition cip_intp ip : ciProp I C D Σ → iProp Σ := cit_intp (cip_bintp ip).

  (** [cip_intp ip] is non-expansive if [ip] is *)
  Fact cip_intp_ne `{!∀ s, NonExpansive3 (ip s)} : NonExpansive (cip_intp ip).
  Proof. exact _. Qed.
End iris.
Arguments cip_intp {_ _ _ _ _} _ _ /.
