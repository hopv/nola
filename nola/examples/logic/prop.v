(** * [nProp]: Syntactic proposition *)

From nola.util Require Export funext rel ctx.
From nola.iris Require Export upd.
From stdpp Require Export coPset namespaces.
From iris.bi Require Import notation.
From iris.base_logic Require Export lib.na_invariants.
From nola.examples.heap_lang Require Import primitive_laws.
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

(** ** [nProp]: Nola syntactic proposition *)

(** Basic connectives *)

(** Nullary *)
Variant ncon0 : Type :=
| (** Pure proposition *) nc_pure (φ : Prop) : ncon0
| (** Non-atomic invariant token *) nc_na_own
    (p : na_inv_pool_name) (E : coPset) : ncon0
| (** Points-to token *) nc_mapsto (l : loc) (dq : dfrac) (v : val) : ncon0
| (** Owning invariant points-to token *) nc_inv_mapsto_own
    (l : loc) (v : val) (I : val → Prop) : ncon0
| (** Invariant points-to token *) nc_inv_mapsto
    (l : loc) (I : val → Prop) : ncon0
| (** Meta token *) nc_meta_token (l : loc) (E : coPset) : ncon0
| (** Step number token *) nc_steps_lb (n : nat) : ncon0
| (** Prophecy token *) nc_proph
    (p : proph_id) (pvs : list (val * val)) : ncon0.
(** Nullary, large *)
Variant nconl0 : Type :=
| (** Invariant world satisfaction *) nc_inv_wsat : nconl0.
(** Unary *)
Variant ncon1 : Type :=
| (** Except-0 modality *) nc_except_0 : ncon1
| (** Persistence modality *) nc_persistently : ncon1
| (** Plainly modality *) nc_plainly : ncon1
| (** Basic update modality *) nc_bupd : ncon1
| (** Fancy update modality *) nc_fupd (E E' : coPset) : ncon1.
(** Binary *)
Variant ncon2 : Type :=
| (** Conjunction *) nc_and : ncon2
| (** Disjunction *) nc_or : ncon2
| (** Implication *) nc_impl : ncon2
| (** Separating conjunction *) nc_sep : ncon2
| (** Magic wand *) nc_wand : ncon2
| (** Basic update modality with the world satisfaction *) nc_bupdw : ncon2
| (** Fasic update modality with the world satisfaction *)
    nc_fupdw (E E' : coPset) : ncon2.
(** Unary, guarding *)
Variant ncong1 : Type :=
| (** Later modality *) nc_later : ncong1
| (** Indirection modality *) nc_indir (i : nat) : ncong1
| (** Invariant *) nc_inv (i : nat) (N : namespace)
| (** Non-atomic invariant *) nc_na_inv
    (i : nat) (p : na_inv_pool_name) (N : namespace).

(** Notation for [ncon] *)
Declare Scope ncon_scope.
Delimit Scope ncon_scope with nc.
Bind Scope ncon_scope with ncon0 ncon1 ncon2 ncong1.
Notation "⟨⌜ φ ⌝⟩" := (nc_pure φ%type%stdpp%nola) (format "⟨⌜ φ ⌝⟩")
  : ncon_scope.
Notation "⟨↦ dq | l , v ⟩" := (nc_mapsto l dq v)
  (dq custom dfrac, format "⟨↦ dq | l , v ⟩") : ncon_scope.
Notation "⟨↦_ I | l , v ⟩" := (nc_inv_mapsto_own l v I%stdpp%type)
  (format "⟨↦_ I | l , v ⟩") : ncon_scope.
Notation "⟨↦□_ I | l ⟩" := (nc_inv_mapsto l I%stdpp%type)
  (format "⟨↦□_ I | l ⟩") : ncon_scope.
Notation "⟨◇⟩" := nc_except_0 : ncon_scope.
Notation "⟨□⟩" := nc_persistently : ncon_scope.
Notation "⟨■⟩" := nc_plainly : ncon_scope.
Notation "⟨|==>⟩" := nc_bupd : ncon_scope.
Notation "⟨|={ E , E' }=>⟩" := (nc_fupd E E')
  (format "⟨|={ E , E' }=>⟩") : ncon_scope.
Notation "⟨∧⟩" := nc_and : ncon_scope.
Notation "⟨∨⟩" := nc_or : ncon_scope.
Notation "⟨→⟩" := nc_impl : ncon_scope.
Notation "⟨∗⟩" := nc_sep : ncon_scope.
Notation "⟨-∗⟩" := nc_wand : ncon_scope.
Notation "⟨|=[ ] =>⟩" := nc_bupdw (format "⟨|=[ ] =>⟩") : ncon_scope.
Notation "⟨|=[ ] { E , E' }=>⟩" := (nc_fupdw E E')
  (format "⟨|=[ ] { E , E' }=>⟩") : ncon_scope.
Notation "⟨▷⟩" := nc_later : ncon_scope.
Notation "⟨○( i )⟩" := (nc_indir i) (format "⟨○( i )⟩") : ncon_scope.

(** [nProp]: Nola syntactic proposition
  Its universe level is strictly higher than those of [V : npvar]
  and the domain [A : Type] of [n_forall]/[n_exist].

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γᵘ, Γᵍ] for smooth type inference *)

Inductive nProp : nkind → nctx → Type :=

(** Basic connective *)
| n_0 {κ Γ} (c : ncon0) : nProp κ Γ
| n_l0 {Γ} (c : nconl0) : nProp nL Γ
| n_1 {κ Γ} (c : ncon1) (P : nProp κ Γ) : nProp κ Γ
| n_2 {κ Γ} (c : ncon2) (P Q : nProp κ Γ) : nProp κ Γ
| n_g1 {κ Γᵘ Γᵍ} (c : ncong1) (P : nProp nL (;ᵞ Γᵘ ++ Γᵍ)) : nProp κ (Γᵘ;ᵞ Γᵍ)

(** Universal quantification *)
| n_forall {κ Γ} {A : Type} (Φ : A → nProp κ Γ) : nProp κ Γ
(** Existential quantification *)
| n_exist {κ Γ} {A : Type} (Φ : A → nProp κ Γ) : nProp κ Γ
(** Weakest precondition *)
| n_wpw {κ Γ} (W : nProp κ Γ) (s : stuckness) (E : coPset) (e : expr)
    (Φ : val → nProp κ Γ) : nProp κ Γ
(** Total weakest precondition *)
| n_twpw {κ Γ} (W : nProp κ Γ) (s : stuckness) (E : coPset) (e : expr)
    (Φ : val → nProp κ Γ) : nProp κ Γ

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

Notation "'⌜' φ '⌝'" := (n_0 ⟨⌜φ⌝⟩) : nProp_scope.
Notation "'True'" := (n_0 ⟨⌜True⌝⟩) : nProp_scope.
Notation "'False'" := (n_0 ⟨⌜False⌝⟩) : nProp_scope.
Notation n_na_own p E := (n_0 (nc_na_own p E)).
Notation "l ↦ dq v" := (n_0 ⟨↦{dq}|l,v⟩) : nProp_scope.
Notation "l ↦_ I v" := (n_0 ⟨↦_I|l,v⟩) : nProp_scope.
Notation "l ↦_ I □" := (n_0 ⟨↦□_I|l⟩) : nProp_scope.
Notation n_meta_token l E := (n_0 (nc_meta_token l E)).
Notation n_steps_lb n := (n_0 (nc_steps_lb n)).
Notation n_proph p pvs := (n_0 (nc_proph p pvs)).
Notation n_inv_wsat := (n_l0 nc_inv_wsat).
Notation "◇ P" := (n_1 ⟨◇⟩ P) : nProp_scope.
Notation "□ P" := (n_1 ⟨□⟩ P) : nProp_scope.
Notation "■ P" := (n_1 ⟨■⟩ P) : nProp_scope.
Notation "|==> P" := (n_1 ⟨|==>⟩ P) : nProp_scope.
Notation "|={ E , E' }=> P" := (n_1 ⟨|={E,E'}=>⟩ P) : nProp_scope.
Notation "|={ E }=> P" := (n_1 ⟨|={E,E}=>⟩ P) : nProp_scope.
Infix "∧" := (n_2 ⟨∧⟩) : nProp_scope.
Infix "∨" := (n_2 ⟨∨⟩) : nProp_scope.
Infix "→" := (n_2 ⟨→⟩) : nProp_scope.
Notation "¬ P" := (P → False)%n : nProp_scope.
Infix "∗" := (n_2 ⟨∗⟩) : nProp_scope.
Infix "-∗" := (n_2 ⟨-∗⟩) : nProp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%n : nProp_scope.
Notation "P ={ E , E' }=∗ Q" := (P -∗ |={E,E'}=> Q)%n : nProp_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%n : nProp_scope.
Notation "|=[ W ] => P" := (n_2 ⟨|=[]=>⟩ W P) : nProp_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q)%n : nProp_scope.
Notation "|=[ W ] { E , E' }=> P" := (n_2 ⟨|=[]{E,E'}=>⟩ W P) : nProp_scope.
Notation "|=[ W ] { E }=> P" := (n_2 ⟨|=[]{E,E}=>⟩ W P) : nProp_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q)%n : nProp_scope.
Notation "P =[ W ] { E }=∗ Q" := (P =[W]{E,E}=∗ Q)%n : nProp_scope.
Notation "∀'" := n_forall (only parsing) : nProp_scope.
Notation "∀ x .. z , P" :=
  (n_forall (λ x, .. (n_forall (λ z, P%n)) ..)) : nProp_scope.
Notation "∃'" := n_exist (only parsing) : nProp_scope.
Notation "∃ x .. z , P" :=
  (n_exist (λ x, .. (n_exist (λ z, P%n)) ..)) : nProp_scope.

Notation "▷{ Γᵘ } P" := (n_g1 (Γᵘ:=Γᵘ) ⟨▷⟩ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_g1 ⟨▷⟩ P) : nProp_scope.
Notation "○{ Γᵘ } ( i ) P" := (n_g1 (Γᵘ:=Γᵘ) ⟨○(i)⟩ P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "○ ( i ) P" := (n_g1 ⟨○(i)⟩ P)
  (at level 20, right associativity, format "○ ( i )  P") : nProp_scope.
Notation n_inv' Γᵘ i N P := (n_g1 (Γᵘ:=Γᵘ) (nc_inv i N) P) (only parsing).
Notation n_inv i N P := (n_inv' _ i N P).
Notation n_na_inv' Γᵘ i p N P :=
  (n_g1 (Γᵘ:=Γᵘ) (nc_na_inv i p N) P) (only parsing).
Notation n_na_inv i p N P := (n_na_inv' _ i p N P).
Notation "WP[ W ] e @ s ; E {{ Φ } }" := (n_wpw W s E e Φ) (only parsing)
  : nProp_scope.
Notation "WP[ W ] e @ s ; E {{ v , P } }" := (n_wpw W s E e (λ v, P))
  : nProp_scope.
Notation "WP[ W ] e @ s ; E [{ Φ } ]" := (n_twpw W s E e Φ) (only parsing)
  : nProp_scope.
Notation "WP[ W ] e @ s ; E [{ v , P } ]" := (n_twpw W s E e (λ v, P))
  : nProp_scope.

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

(** ** [↑ˡ P]: Turn [P : nProp κ Γ] into [nPropL Γ]
  Although the main interest is the case [κ = nS],
  we keep the function polymorphic over [κ] for ease of definition *)
Reserved Notation "(↑ˡ)".
Reserved Notation "↑ˡ P" (at level 20, right associativity).
Fixpoint nlarge {κ Γ} (P : nProp κ Γ) : nPropL Γ :=
  match P with
  | n_0 c => n_0 c | n_l0 c => n_l0 c | n_1 c P => n_1 c (↑ˡ P)
  | n_2 c P Q => n_2 c (↑ˡ P) (↑ˡ Q) | n_g1 c P => n_g1 c P
  | ∀' Φ => ∀ a, ↑ˡ Φ a | ∃' Φ => ∃ a, ↑ˡ Φ a
  | n_wpw W s E e Φ => n_wpw (↑ˡ W) s E e (λ v, ↑ˡ Φ v)
  | n_twpw W s E e Φ => n_twpw (↑ˡ W) s E e (λ v, ↑ˡ Φ v)
  | ∀: V, P => ∀: V, ↑ˡ P | ∃: V, P => ∃: V, ↑ˡ P
  | rec:ˢ' Φ a => rec:ˢ' Φ a | rec:ˡ' Φ a => rec:ˡ' Φ a
  | %ᵍˢ s => %ᵍˢ s | %ᵍˡ s => %ᵍˡ s | %ᵘˢ s => %ᵘˢ s | !ᵘˢ P => !ᵘˢ P
  end%n
where
  "(↑ˡ)" := nlarge : nola_scope and
  "↑ˡ P" := (nlarge P) : nola_scope.

(** [nsmall]: Turn [nProp κ Γ] into [nPropS Γ] *)

(** [nunsmall]: Turn [nPropS Γ] into [nProp κ Γ] *)
Definition nunsmall {κ Γ} (P : nPropS Γ) : nProp κ Γ :=
  match κ with nS => P | nL => ↑ˡ P end.

(** [↑ˡ] is identity for [nPropL] *)
Lemma nlarge_id' {κ Γ} {P : nProp κ Γ} (eq : κ = nL) :
  ↑ˡ P = rew[λ κ, nProp κ Γ] eq in P.
Proof.
  move: κ Γ P eq. fix FIX 3=> κ Γ.
  case=>/=; intros; subst=>//=; try rewrite (eq_dec_refl eq)/=; f_equal;
    try exact (FIX _ _ _ eq_refl); funext=> ?; exact (FIX _ _ _ eq_refl).
Qed.
Lemma nlarge_id {Γ} {P : nPropL Γ} : ↑ˡ P = P.
Proof. exact (nlarge_id' eq_refl). Qed.

(** [↑ˡ] over [nunsmall] *)
Lemma nlarge_nunsmall {Γ κ} {P : nPropS Γ} :
  ↑ˡ (nunsmall (κ:=κ) P) = ↑ˡ P.
Proof. case κ=>//=. exact nlarge_id. Qed.
