(** * [nProp]: Syntactic proposition *)

From nola Require Export util.funext util.rel ctx.
From stdpp Require Export coPset.
From iris.bi Require Import notation.
Import EqNotations.

(** ** Preliminaries for [nProp] *)

(** [nkind]: Kind of of [nProp], [nS] or [nL] *)
Variant nkind : Set := (* small *) nS | (* large *) nL.

(** Equality on [nkind] is decidable *)
#[export] Instance nkind_eq_dec : EqDecision nkind.
Proof. case; case; try (by left); by right. Defined.

(** [npvar]: Predicate variable *)
#[projections(primitive)]
Record npvar := Npvar {
  npvar_argty : Type;
  npvar_sort : nkind;
}.

(** Notations for [npvar] *)
Notation "A →nP κ" := (Npvar A κ) (at level 1, no associativity) : nola_scope.
Notation "A →nPS" := (A →nP nS) (at level 1) : nola_scope.
Notation "A →nPL" := (A →nP nL) (at level 1) : nola_scope.
Notation nP κ := (unit →nP κ).
Notation nPS := (unit →nPS).
Notation nPL := (unit →nPL).

(** [nctx]: Context of [nProp] *)
Notation nctx := (ctx npvar).

(** [nparg]: Argument to [npvar], with [nkind] specified *)
Variant nparg {κ : nkind} : npvar → Type :=
| Nparg {A} : A → nparg (A →nP κ).
Arguments nparg κ V : clear implicits.
Notation npargS := (nparg nS).
Notation npargL := (nparg nL).
Notation "@! a" := (Nparg a) (at level 20, right associativity) : nola_scope.

(** ** [nProp]: Nola syntactic proposition

  Its universe level is strictly higher than those of [V : npvar]
  and the domain [A : Type] of [n_forall]/[n_exist].

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γᵘ, Γᵍ] for smooth type inference

  In nominal proposition arguments (e.g., [n_deriv]'s arguments), unguarded
  variables are flushed into guarded, with the context [(;ᵞ Γᵘ ++ Γᵍ)];
  for connectives with such arguments we make [Γᵘ] explicit for the users
  to aid type inference around [++] *)

Inductive nProp : nkind → nctx → Type :=

(** Pure proposition *)
| n_pure {κ Γ} (φ : Prop) : nProp κ Γ
(** Conjunction *)
| n_and {κ Γ} (P Q : nProp κ Γ) : nProp κ Γ
(** Disjunction *)
| n_or {κ Γ} (P Q : nProp κ Γ) : nProp κ Γ
(** Implication *)
| n_impl {κ Γ} (P Q : nProp κ Γ) : nProp κ Γ
(** Universal quantification *)
| n_forall {κ Γ} {A : Type} (Φ : A → nProp κ Γ) : nProp κ Γ
(** Existential quantification *)
| n_exist {κ Γ} {A : Type} (Φ : A → nProp κ Γ) : nProp κ Γ

(** Separating conjunction *)
| n_sep {κ Γ} (P Q : nProp κ Γ) : nProp κ Γ
(** Magic wand *)
| n_wand {κ Γ} (P Q : nProp κ Γ) : nProp κ Γ
(** Persistence modality *)
| n_persistently {κ Γ} (P : nProp κ Γ) : nProp κ Γ
(** Plainly modality *)
| n_plainly {κ Γ} (P : nProp κ Γ) : nProp κ Γ
(** Basic update modality *)
| n_bupd {κ Γ} (P : nProp κ Γ) : nProp κ Γ
(** Fancy update modality *)
| n_fupd {κ Γ} (E E' : coPset) (P : nProp κ Γ) : nProp κ Γ

(** Later modality *)
| n_later {κ} Γᵘ {Γᵍ} (P : nProp nL (;ᵞ Γᵘ ++ Γᵍ)) : nProp κ (Γᵘ;ᵞ Γᵍ)
(** Judgment derivability *)
| n_deriv {κ} Γᵘ {Γᵍ} (i : nat) (P Q : nProp nL (;ᵞ Γᵘ ++ Γᵍ)) :
    nProp κ (Γᵘ;ᵞ Γᵍ)

(** Universal quantification over [A → nProp] *)
| n_n_forall {κ Γᵘ Γᵍ} V (P : nProp κ (V :: Γᵘ;ᵞ Γᵍ)) : nProp κ (Γᵘ;ᵞ Γᵍ)
(** Existential quantification over [A → nProp] *)
| n_n_exist {κ Γᵘ Γᵍ} V (P : nProp κ (V :: Γᵘ;ᵞ Γᵍ)) : nProp κ (Γᵘ;ᵞ Γᵍ)
(** Recursive small proposition *)
| n_recs {κ Γᵘ Γᵍ} {A : Type} (Φ : A → nProp nS (A →nPS :: Γᵘ;ᵞ Γᵍ)) (a : A) :
    nProp κ (Γᵘ;ᵞ Γᵍ)
(** Recursive large proposition *)
| n_recl {Γᵘ Γᵍ} {A : Type} (Φ : A → nProp nL (A →nPL :: Γᵘ;ᵞ Γᵍ)) (a : A) :
    nProp nL (Γᵘ;ᵞ Γᵍ)

(** Guarded small variable *)
| n_vargs {κ Γᵘ Γᵍ} (s : schoice npargS Γᵍ) : nProp κ (Γᵘ;ᵞ Γᵍ)
(** Guarded large variable, [nPropL] only *)
| n_vargl {Γᵘ Γᵍ} (s : schoice npargL Γᵍ) : nProp nL (Γᵘ;ᵞ Γᵍ)
(** Unguarded small variable, [nPropL] only *)
| n_varus {Γᵘ Γᵍ} (s : schoice npargS Γᵘ) : nProp nL (Γᵘ;ᵞ Γᵍ)
(** Substituted [n_varus] *)
| n_subus {Γᵘ Γᵍ} (P : nProp nS (;ᵞ)) : nProp nL (Γᵘ;ᵞ Γᵍ).

Notation nPropS := (nProp nS).
Notation nPropL := (nProp nL).

(** ** Notations for [nProp] connectives *)

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.

Notation "'⌜' φ '⌝'" := (n_pure φ%type%stdpp%nola) : nProp_scope.
Notation "'True'" := (n_pure True) : nProp_scope.
Notation "'False'" := (n_pure False) : nProp_scope.
Infix "∧" := n_and : nProp_scope.
Notation "(∧)" := n_and (only parsing) : nProp_scope.
Infix "∨" := n_or : nProp_scope.
Notation "(∨)" := n_or (only parsing) : nProp_scope.
Infix "→" := n_impl : nProp_scope.
Notation "¬ P" := (n_impl P (n_pure False)) : nProp_scope.
Notation "∀'" := n_forall (only parsing) : nProp_scope.
Notation "∀ x .. z , P" :=
  (n_forall (λ x, .. (n_forall (λ z, P%n)) ..)) : nProp_scope.
Notation "∃'" := n_exist (only parsing) : nProp_scope.
Notation "∃ x .. z , P" :=
  (n_exist (λ x, .. (n_exist (λ z, P%n)) ..)) : nProp_scope.

Infix "∗" := n_sep : nProp_scope.
Notation "(∗)" := n_sep (only parsing) : nProp_scope.
Infix "-∗" := n_wand : nProp_scope.
Notation "□ P" := (n_persistently P) : nProp_scope.
Notation "■ P" := (n_plainly P) : nProp_scope.
Notation "|==> P" := (n_bupd P) : nProp_scope.
Notation "|={ E , E' }=> P" := (n_fupd E E' P) : nProp_scope.

Notation "▷{ Γᵘ } P" := (n_later Γᵘ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_later _ P) : nProp_scope.
Definition n_except_0 {κ Γ} (P : nProp κ Γ) : nProp κ Γ := ▷ False ∨ P.
Notation "◇ P" := (n_except_0 P) : nProp_scope.
Notation "P ⊢{ i }{ Γᵘ } Q" := (n_deriv Γᵘ i P Q)
  (at level 99, Q at level 200, only parsing) : nProp_scope.
Notation "P ⊢{ i } Q" := (n_deriv _ i P Q)
  (at level 99, Q at level 200, format "P  ⊢{ i }  Q") : nProp_scope.

Notation "∀: V , P" := (n_n_forall V P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: V , P" := (n_n_exist V P)
  (at level 200, right associativity,
    format "'[' '[' ∃:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "rec:ˢ'" := n_recs (only parsing) : nProp_scope.
Notation "rec:ˢ x , P" := (n_recs (λ x, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ˢ  x ,  '/' P ']' ']'") : nProp_scope.
Notation "rec:ˡ'" := n_recl (only parsing) : nProp_scope.
Notation "rec:ˡ x , P" := (n_recl (λ x, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ˡ  x ,  '/' P ']' ']'") : nProp_scope.

Notation "%ᵍˢ s" := (n_vargs s) (at level 20, right associativity)
  : nProp_scope.
Notation "%ᵍˡ s" := (n_vargl s) (at level 20, right associativity)
  : nProp_scope.
Notation "%ᵘˢ s" := (n_varus s) (at level 20, right associativity)
  : nProp_scope.
Notation "!ᵘˢ P" := (n_subus P) (at level 20, right associativity)
  : nProp_scope.

(** ** [nlarge]: Turn [nProp κ Γ] into [nPropL Γ]
  Although the main interest is the case [κ = nS],
  we keep the function polymorphic over [κ] for ease of definition *)
Fixpoint nlarge {κ Γ} (P : nProp κ Γ) : nPropL Γ :=
  match P with
  | ⌜φ⌝ => ⌜φ⌝
  | P ∧ Q => nlarge P ∧ nlarge Q
  | P ∨ Q => nlarge P ∨ nlarge Q
  | P → Q => nlarge P → nlarge Q
  | P ∗ Q => nlarge P ∗ nlarge Q
  | P -∗ Q => nlarge P -∗ nlarge Q
  | ∀' Φ => ∀' (nlarge ∘ Φ)
  | ∃' Φ => ∃' (nlarge ∘ Φ)
  | □ P => □ nlarge P
  | ■ P => ■ nlarge P
  | |==> P => |==> nlarge P
  | |={E,E'}=> P => |={E,E'}=> nlarge P
  | ▷ P => ▷ P
  | P ⊢{i} Q => P ⊢{i} Q
  | ∀: V, P => ∀: V, nlarge P
  | ∃: V, P => ∃: V, nlarge P
  | rec:ˢ' Φ a => rec:ˢ' Φ a
  | rec:ˡ' Φ a => rec:ˡ' Φ a
  | %ᵍˢ s => %ᵍˢ s
  | %ᵍˡ s => %ᵍˡ s
  | %ᵘˢ s => %ᵘˢ s
  | !ᵘˢ P => !ᵘˢ P
  end%n.

(** [nunsmall]: Turn [nPropS Γ] into [nProp κ Γ] *)
Definition nunsmall {κ Γ} (P : nPropS Γ) : nProp κ Γ :=
  match κ with nS => P | nL => nlarge P end.

(** [nlarge] is identity for [nPropL] *)
Lemma nlarge_id' {κ Γ} {P : nProp κ Γ} (eq : κ = nL) :
  nlarge P = rew[λ κ, nProp κ Γ] eq in P.
Proof.
  move: κ Γ P eq. fix FIX 3=> κ Γ.
  case=>/=; intros; subst=>//=; f_equal; try exact (FIX _ _ _ eq_refl);
  try (funext=> ?; exact (FIX _ _ _ eq_refl)); by rewrite (eq_dec_refl eq).
Qed.
Lemma nlarge_id {Γ} {P : nPropL Γ} : nlarge P = P.
Proof. exact (nlarge_id' eq_refl). Qed.

(** [nlarge] over [nunsmall] *)
Lemma nlarge_nunsmall {Γ κ} {P : nPropS Γ} :
  nlarge (κ:=κ) (nunsmall P) = nlarge P.
Proof. case κ=>//=. exact nlarge_id. Qed.
