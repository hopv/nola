(** * [cif]: Coinductive-inductive set of formulas *)

From nola.util Require Export fn uip cit.
From nola.bi Require Import ofe.
From nola.iris Require Export iprop.
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
Variant cif_sel SEL :=
| (** Universal quantifier *) cifs_all (A : Type)
| (** Existential quantifier *) cifs_ex (A : Type)
| (** Binary operator *) cifs_bin (s : cif_binsel)
| (** Unary operator *) cifs_un (s : cif_unsel)
| (** Pure proposition *) cifs_pure
| (** Later *) cifs_later
| (** Custom selector *) cifs_custom (s : SEL).
Arguments cifs_all {_}. Arguments cifs_ex {_}.
Arguments cifs_bin {_}.  Arguments cifs_un {_}.
Arguments cifs_pure {_}. Arguments cifs_later {_}. Arguments cifs_custom {_}.

(** [cif_idom]: Domain for inductive parts *)
Definition cif_idom {SEL} (I : SEL → Type) (s : cif_sel SEL) : Type :=
  match s with
  | cifs_all A | cifs_ex A => A | cifs_bin _ => bool | cifs_un _ => unit
  | cifs_pure | cifs_later => Empty_set | cifs_custom s => I s
  end.

(** [cif_cdom]: Domain for coinductive parts *)
Definition cif_cdom {SEL} (C : SEL → Type) (s : cif_sel SEL) : Type :=
  match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ | cifs_pure | cifs_later =>
      Empty_set
  | cifs_custom s => C s
  end.

(** [cif_dataOF]: Data [oFunctor] *)
Definition cif_dataOF {SEL} (D : SEL → oFunctor) (s : cif_sel SEL) : oFunctor :=
  match s with
  | cifs_all _ | cifs_ex _ | cifs_bin _ | cifs_un _ => unitO
  | cifs_pure => PropO | cifs_later => laterOF ∙ | cifs_custom s => D s
  end.

(** [cif_dataOF] is contractive *)
#[export] Instance cif_dataOF_contractive {SEL s}
  `{∀ s : SEL, oFunctorContractive (D s)} :
  oFunctorContractive (cif_dataOF D s).
Proof. case s=>/=; exact _. Qed.

(** ** [cif]: Coinductive-inductive set of formulas *)
Definition cifOF {SEL} I C D : oFunctor :=
  citOF (cif_idom (SEL:=SEL) I) (cif_cdom C) (cif_dataOF D).
Definition cif {SEL} I C D Σ : Type :=
  cit (cif_idom (SEL:=SEL) I) (cif_cdom C) (λ s, cif_dataOF D s $oi Σ).
Definition cifa {SEL} I C D Σ : Type :=
  cita (cif_idom (SEL:=SEL) I) (cif_cdom C) (λ s, cif_dataOF D s $oi Σ).

(** [cifOF] is contractive *)
Fact cifOF_contractive {SEL I C} `{∀ s, oFunctorContractive (D s)} :
  oFunctorContractive (@cifOF SEL I C D).
Proof. exact _. Qed.

(** ** Construct [cif] *)
Section cif.
  Context {SEL} {I C : SEL → Type} {D : SEL → oFunctor} {Σ : gFunctors}.
  Implicit Type Px Qx : cif I C D Σ.

  (** Basic connectives *)

  Definition cif_all {A} (Φx : A -d> cif I C D Σ) : cif I C D Σ :=
    Citg (cifs_all A) Φx nullary ().
  Definition cif_ex {A} (Φx : A -d> cif I C D Σ) : cif I C D Σ :=
    Citg (cifs_ex A) Φx nullary ().

  Definition cif_bin (s : cif_binsel) (Px Qx : cif I C D Σ) : cif I C D Σ :=
    Citg (cifs_bin s) (binary Px Qx) nullary ().
  Definition cif_and := cif_bin cifs_and.
  Definition cif_or := cif_bin cifs_or.
  Definition cif_imp := cif_bin cifs_imp.
  Definition cif_sep := cif_bin cifs_sep.
  Definition cif_wand := cif_bin cifs_wand.

  Definition cif_un (s : cif_unsel) (Px : cif I C D Σ) : cif I C D Σ :=
    Citg (cifs_un s) (unary Px) nullary ().
  Definition cif_plain := cif_un cifs_plain.
  Definition cif_pers := cif_un cifs_pers.
  Definition cif_bupd := cif_un cifs_bupd.
  Definition cif_except0 := cif_un cifs_except0.

  Definition cif_pure (φ : Prop) : cif I C D Σ :=
    Citg cifs_pure nullary nullary φ.
  Definition cif_later (P : iProp Σ) : cif I C D Σ :=
    Citg cifs_later nullary nullary (Next P%I).

  (** Frozen [of_cit] *)
  Lemma of_cif_aux : seal (of_cit : cif I C D Σ → cifa I C D Σ).
  Proof. by eexists. Qed.
  Definition of_cif : cif I C D Σ → cifa I C D Σ := of_cif_aux.(unseal).
  Lemma of_cif_unseal : of_cif = of_cit. Proof. exact: seal_eq. Qed.
  (** [of_cif] is [Preserv] *)
  #[export] Instance of_cif_preserv : Preserv of_cif.
  Proof. rewrite of_cif_unseal. exact _. Qed.
  (** Simplify [to_cit] over [of_cif] *)
  Lemma to_of_cif {Px} : to_cit (of_cif Px) ≡ Px.
  Proof. by rewrite of_cif_unseal to_of_cit'. Qed.

  (** Custom connective *)
  Definition cif_custom s (Φx : I s -d> cif I C D Σ) (Ψx : C s -d> cif I C D Σ)
    (d : D s $oi Σ) : cif I C D Σ :=
    Citg (cifs_custom s) Φx (λ c, of_cif (Ψx c)) d.

  (** [cif] is inhabited *)
  #[export] Instance cif_inhabited : Inhabited (cif I C D Σ) :=
    populate (cif_pure True).

  (** Basic connectives are size-preserving *)
  #[export] Instance cif_all_preserv {A} :
    Preserv' (funPR (λ _, cif _ _ _ _)) _ (@cif_all A).
  Proof. move=> ????. by apply Citg_preserv_productive. Qed.
  #[export] Instance cif_ex_preserv {A} :
    Preserv' (funPR (λ _, cif _ _ _ _)) _ (@cif_ex A).
  Proof. move=> ????. by apply Citg_preserv_productive. Qed.
  #[export] Instance cif_bin_preserv {s n} :
    Proper (proeq n ==> proeq n ==> proeq n) (cif_bin s).
  Proof. move=> ??????. apply Citg_preserv_productive=>//. by case. Qed.
  #[export] Instance cif_un_preserv {s} : Preserv (cif_un s).
  Proof. move=> ????. apply Citg_preserv_productive=>//. by case. Qed.

  (** Custom connectives are size-preserving over the inductive arguments
    and productive over the coinductive arguments *)
  #[export] Instance cif_custom_preserv_productive {s n} :
    Proper (@proeq (funPR (λ _, cif _ _ _ _)) n ==>
      @proeq_later (funPR (λ _, cif _ _ _ _)) n ==> (=) ==> proeq n)
      (cif_custom s).
  Proof.
    move=> ????? eq ??<-. apply Citg_preserv_productive=>//.
    destruct n as [|?]=>//= ?. apply of_cif_preserv, eq.
  Qed.

  (** Non-expansiveness *)
  #[export] Instance cif_all_ne {A} : NonExpansive (@cif_all A).
  Proof. move=> ????. apply Citg_ne; solve_proper. Qed.
  #[export] Instance cif_all_proper {A} : Proper ((≡) ==> (≡)) (@cif_all A).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_ex_ne {A} : NonExpansive (@cif_ex A).
  Proof. move=> ????. apply Citg_ne; solve_proper. Qed.
  #[export] Instance cif_ex_proper {A} : Proper ((≡) ==> (≡)) (@cif_ex A).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_bin_ne {s} : NonExpansive2 (cif_bin s).
  Proof. move=> ???????. apply Citg_ne; solve_proper. Qed.
  #[export] Instance cif_bin_proper {s} :
    Proper ((≡) ==> (≡) ==> (≡)) (cif_bin s).
  Proof. apply ne_proper_2, _. Qed.
  #[export] Instance cif_un_ne {s} : NonExpansive (cif_un s).
  Proof. move=> ????. apply Citg_ne; solve_proper. Qed.
  #[export] Instance cif_un_proper {s} : Proper ((≡) ==> (≡)) (cif_un s).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_pure_ne : NonExpansive cif_pure.
  Proof. move=> ????. by apply Citg_ne. Qed.
  #[export] Instance cif_pure_proper : Proper ((≡) ==> (≡)) cif_pure.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_later_contractive : Contractive cif_later.
  Proof. move=> ????. by apply Citg_ne. Qed.
  #[export] Instance cif_later_proper : Proper ((≡) ==> (≡)) cif_later.
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_custom_ne {s} : NonExpansive3 (cif_custom s).
  Proof.
    move=> ??????????. apply Citg_ne=>// ?. rewrite of_cif_unseal. by f_equiv.
  Qed.
  #[export] Instance cif_custom_proper {s} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (cif_custom s).
  Proof. move=> ??????????. apply cif_custom_ne; by apply equiv_dist. Qed.

  (** Discreteness *)
  #[export] Instance cif_all_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_all Φx).
  Proof. by apply: Citg_discrete. Qed.
  #[export] Instance cif_ex_discrete {A} `{!∀ a : A, Discrete (Φx a)} :
    Discrete (cif_ex Φx).
  Proof. by apply: Citg_discrete. Qed.
  #[export] Instance cif_bin_discrete {s} `{!Discrete Px, !Discrete Qx} :
    Discrete (cif_bin s Px Qx).
  Proof. apply: Citg_discrete=>//. case; exact _. Qed.
  #[export] Instance cif_un_discrete {s} `{!Discrete Px} :
    Discrete (cif_un s Px).
  Proof. by apply: Citg_discrete. Qed.
  #[export] Instance cif_pure_discrete {φ} : Discrete (cif_pure φ).
  Proof. by apply: Citg_discrete. Qed.
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
  Context {SEL} {I C : SEL → Type} {D : SEL → oFunctor} {Σ : gFunctors}.

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
End iris.

(** [cif_sem]: Semantics of [cif] *)
Notation cif_sem sm := (cit_fold (cif_bsem sm)).
Notation cif_sem' SEL I C D Σ sm := (cit_fold (@cif_bsem SEL I C D Σ sm))
  (only parsing).

Section iris.
  Context {SEL} {I C : SEL → Type} {D : SEL → oFunctor} {Σ : gFunctors}.

  (** [cif_sem sm] is non-expansive if [sm] is *)
  #[export] Instance cif_sem_ne `{!∀ s, NonExpansive3 (sm s)} :
    NonExpansive (cif_sem' _ I C D Σ sm).
  Proof. move=> ?. apply cit_fold_ne_gen; solve_proper. Qed.
  #[export] Instance cif_sem_proper `{!∀ s, NonExpansive3 (sm s)} :
    Proper ((≡) ==> (⊣⊢)) (cif_sem' _ I C D Σ sm).
  Proof. apply ne_proper, _. Qed.
End iris.
