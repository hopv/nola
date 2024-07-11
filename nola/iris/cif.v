(** * [cif]: Coinductive-inductive set of formulas *)

From nola.util Require Export fn cit.
From nola.bi Require Import ofe.
From nola.iris Require Export ofe.
Import iPropAppNotation.

(** ** Data types *)

(** [cif_binsel]: Binary operator selector *)
Variant cif_binsel :=
| (** Conjunction *) cifs_and
| (** Disjunction *) cifs_or
| (** Implication *) cifs_imp
| (** Separating conjunction *) cifs_sep
| (** Magic wand *) cifs_wand.

(** [cif_unsel]: Unary operator selector *)
Variant cif_unsel :=
| (** Plainly *) cifs_plain
| (** Persistently *) cifs_pers
| (** Basic update *) cifs_bupd
| (** Except-0 *) cifs_except0.

(** [cif_sel]: Selector *)
Variant cif_sel S :=
| (** Universal quantifier *) cifs_all (A : Type)
| (** Existential quantifier *) cifs_ex (A : Type)
| (** Binary operator *) cifs_bin (s : cif_binsel)
| (** Unary operator *) cifs_un (s : cif_unsel)
| (** Pure proposition *) cifs_pure
| (** Later *) cifs_later
| (** Custom selector *) cifs_custom (s : S).
Arguments cifs_all {_}. Arguments cifs_ex {_}.
Arguments cifs_bin {_}.  Arguments cifs_un {_}.
Arguments cifs_pure {_}. Arguments cifs_later {_}. Arguments cifs_custom {_}.

(** [cif_idom]: Domain for inductive parts *)
Definition cif_idom {S} (I : S → Type) (s : cif_sel S) : Type := match s with
  | cifs_all A | cifs_ex A => A | cifs_bin _ => bool | cifs_un _ => unit
  | cifs_pure | cifs_later => Empty_set | cifs_custom s => I s
  end.

(** [cif_cdom]: Domain for coinductive parts *)
Definition cif_cdom {S} (C : S → Type) (s : cif_sel S) : Type := match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ | cifs_pure | cifs_later =>
      Empty_set
  | cifs_custom s => C s
  end.

(** [cif_dataOF]: Data [oFunctor] *)
Definition cif_dataOF {S} (D : S → oFunctor) (s : cif_sel S) : oFunctor :=
  match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ => unitO
  | cifs_pure => PropO | cifs_later => laterOF ∙ | cifs_custom s => D s
  end.

(** [cif_dataOF] is contractive *)
#[export] Instance cif_dataOF_contractive {S s}
  `{∀ s : S, oFunctorContractive (D s)} : oFunctorContractive (cif_dataOF D s).
Proof. case s=>/=; exact _. Qed.

(** ** [cif]: Coinductive-inductive set of formulas *)
Definition cifOF {S} I C D : oFunctor :=
  citOF (cif_idom (S:=S) I) (cif_cdom C) (cif_dataOF D).
Definition cif {S} I C D Σ : Type := cifOF (S:=S) I C D $oi Σ.

(** [cifOF] is contractive *)
Fact cifOF_contractive {S I C} `{∀ s, oFunctorContractive (D s)} :
  oFunctorContractive (@cifOF S I C D).
Proof. exact _. Qed.

(** ** Construct [cif] *)
Section cif.
  Context {S} {I C : S → Type} {D : S → oFunctor} {Σ : gFunctors}.
  Implicit Type Px Qx : cif I C D Σ.

  Definition cif_all {A} (Φx : A -d> cif I C D Σ) : cif I C D Σ :=
    CitX (cifs_all A) Φx nullary ().
  Definition cif_ex {A} (Φx : A -d> cif I C D Σ) : cif I C D Σ :=
    CitX (cifs_ex A) Φx nullary ().

  Definition cif_bin s Px Qx : cif I C D Σ :=
    CitX (cifs_bin s) (binary Px Qx) nullary ().
  Definition cif_and := cif_bin cifs_and.
  Definition cif_or := cif_bin cifs_or.
  Definition cif_imp := cif_bin cifs_imp.
  Definition cif_sep := cif_bin cifs_sep.
  Definition cif_wand := cif_bin cifs_wand.

  Definition cif_un s Px : cif I C D Σ :=
    CitX (cifs_un s) (unary Px) nullary ().
  Definition cif_plain := cif_un cifs_plain.
  Definition cif_pers := cif_un cifs_pers.
  Definition cif_bupd := cif_un cifs_bupd.
  Definition cif_except0 := cif_un cifs_except0.

  Definition cif_pure (φ : Prop) : cif I C D Σ :=
    CitX cifs_pure nullary nullary φ.
  Definition cif_later (P : iProp Σ) : cif I C D Σ :=
    CitX cifs_later nullary nullary (Next P%I).

  Definition cif_custom s (Φx : I s -d> cif I C D Σ) (Ψx : C s -d> cif I C D Σ)
    (d : D s $oi Σ) : cif I C D Σ :=
    CitX (cifs_custom s) Φx Ψx d.

  (** Non-expansiveness *)
  #[export] Instance cif_all_ne {A} : NonExpansive (@cif_all A).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cif_ex_ne {A} : NonExpansive (@cif_ex A).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cif_bin_ne {s} : NonExpansive2 (cif_bin s).
  Proof. move=> ???????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cif_un_ne {s} : NonExpansive (cif_un s).
  Proof. move=> ????. apply Cit_ne, CitI_ne; solve_proper. Qed.
  #[export] Instance cif_pure_ne : NonExpansive cif_pure.
  Proof. move=> ????. by apply Cit_ne, CitI_ne. Qed.
  #[export] Instance cif_later_contractive : Contractive cif_later.
  Proof. move=> ????. by apply Cit_ne, CitI_ne. Qed.
  #[export] Instance cif_custom_ne {s} : NonExpansive3 (cif_custom s).
  Proof. move=> ??????????. apply Cit_ne, CitI_ne; solve_proper. Qed.

  (** Discreteness *)
  #[export] Instance cif_all_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_all Φx).
  Proof. by apply: CitX_discrete. Qed.
  #[export] Instance cif_ex_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_ex Φx).
  Proof. by apply: CitX_discrete. Qed.
  #[export] Instance cif_bin_discrete {s} `{!Discrete Px, !Discrete Qx} :
    Discrete (cif_bin s Px Qx).
  Proof. apply: CitX_discrete=>//. case; exact _. Qed.
  #[export] Instance cif_un_discrete {s} `{!Discrete Px} :
    Discrete (cif_un s Px).
  Proof. by apply: CitX_discrete. Qed.
  #[export] Instance cif_pure_discrete {φ} : Discrete (cif_pure φ).
  Proof. by apply: CitX_discrete. Qed.
  #[export] Instance cif_custom_discrete {s}
    `{!∀ i, Discrete (Φx i), !∀ c, Discrete (Ψx c), !Discrete d} :
    Discrete (cif_custom s Φx Ψx d).
  Proof. exact _. Qed.
End cif.

Declare Scope cif_scope.
Delimit Scope cif_scope with cif.
Bind Scope cif_scope with cif.
Notation "∀ x .. y , Px" :=
  (cif_all (λ x, .. (cif_all (λ y, Px%cif)) ..)) : cif_scope.
Notation "∃ x .. y , Px" :=
  (cif_ex (λ x, .. (cif_ex (λ y, Px%cif)) ..)) : cif_scope.
Infix "∧" := cif_and : cif_scope. Infix "∨" := cif_or : cif_scope.
Infix "→" := cif_imp : cif_scope.
Infix "∗" := cif_sep : cif_scope. Infix "-∗" := cif_wand : cif_scope.
Notation "■ Px" := (cif_plain Px) : cif_scope.
Notation "□ Px" := (cif_pers Px) : cif_scope.
Notation "|==> Px" := (cif_bupd Px) : cif_scope.
Notation "◇ Px" := (cif_except0 Px) : cif_scope.
Notation "⌜ φ ⌝" := (cif_pure φ) : cif_scope.
Notation "'True'" := (cif_pure True) : cif_scope.
Notation "'False'" := (cif_pure False) : cif_scope.
Notation "▷ P" := (cif_later P) : cif_scope.

(** ** [cif_sem]: Semantics of [cif] *)
Section iris.
  Context {S} {I C : S → Type} {D : S → oFunctor} {Σ : gFunctors}.

  (** [cif_bsem]: Base semantics for [cif] *)
  Definition cif_bsem
    (sm : ∀ s, (I s -d> iProp Σ) → (C s -d> cif I C D Σ) →
      D s $oi Σ → iProp Σ) s
    : (cif_idom I s -d> iProp Σ) → (cif_cdom C s -d> cif I C D Σ) →
        cif_dataOF D s $oi Σ → iProp Σ :=
    match s with
    | cifs_all _ => λ Φ _ _, ∀ a, Φ a | cifs_ex _ => λ Φ _ _, ∃ a, Φ a
    | cifs_bin s => λ Φ _ _, let P := Φ true in let Q := Φ false in
        match s with
        | cifs_and => P ∧ Q | cifs_or => P ∨ Q | cifs_imp => P → Q
        | cifs_sep => P ∗ Q | cifs_wand => P -∗ Q
        end
    | cifs_un s => λ Φ _ _, let P := Φ () in
        match s with
        | cifs_plain => ■ P | cifs_pers => □ P | cifs_bupd => |==> P
        | cifs_except0 => ◇ P
        end
    | cifs_pure => λ _ _ φ, ⌜φ⌝ | cifs_later => λ _ _, laterl
    | cifs_custom s => sm s
    end%I.

  (** [cif_bsem] is non-expansive *)
  #[export] Instance cif_bsem_ne `{!∀ s, NonExpansive3 (sm s)} {s} :
    NonExpansive3 (cif_bsem sm s).
  Proof.
    case s=>/=; try solve_proper. move=> ???????. by apply laterl_ne.
  Qed.

  (** [cif_sem]: Semantics of [cif] *)
  Definition cif_sem sm : cif I C D Σ → iProp Σ := cit_sem (cif_bsem sm).

  (** [cif_sem sm] is non-expansive if [sm] is *)
  Fact cif_sem_ne `{!∀ s, NonExpansive3 (sm s)} : NonExpansive (cif_sem sm).
  Proof. exact _. Qed.
End iris.
Arguments cif_sem {_ _ _ _ _} _ _ /.
