(** * [nProp]: Syntactic proposition *)

From nola.examples.logic Require Export synty.
From nola.util Require Export funext func rel ctx schoice.
From nola.iris Require Export upd lft proph.
From stdpp Require Export coPset namespaces.
From iris.bi Require Export notation.
From iris.base_logic Require Export lib.na_invariants.
From nola.examples.heap_lang Require Export definitions.
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
| Nparg {A} (a : A) : nparg (A →nP κ).
Arguments nparg κ V : clear implicits.
Notation npargS := (nparg nS).
Notation npargL := (nparg nL).
Notation "@! a" := (Nparg a) (at level 20, right associativity) : nola_scope.
Notation "0@ a" := (!0 @! a) (at level 20, right associativity) : nola_scope.
Notation "1@ a" := (!1 @! a) (at level 20, right associativity) : nola_scope.
Notation "2@ a" := (!2 @! a) (at level 20, right associativity) : nola_scope.
Notation "3@ a" := (!3 @! a) (at level 20, right associativity) : nola_scope.
Notation "4@ a" := (!4 @! a) (at level 20, right associativity) : nola_scope.
Notation "5@ a" := (!5 @! a) (at level 20, right associativity) : nola_scope.
Notation "6@ a" := (!6 @! a) (at level 20, right associativity) : nola_scope.
Notation "7@ a" := (!7 @! a) (at level 20, right associativity) : nola_scope.
Notation "8@ a" := (!8 @! a) (at level 20, right associativity) : nola_scope.
Notation "9@ a" := (!9 @! a) (at level 20, right associativity) : nola_scope.

(** ** [nProp]: Nola syntactic proposition *)

(** Basic connectives *)

(** Nullary *)
Variant ncon0 : Type :=
| (** Pure proposition *) nc_pure (φ : Prop)
| (** Non-atomic invariant token *) nc_na_own
    (p : na_inv_pool_name) (E : coPset)
| (** Cancelable invariant token *) nc_cinv_own (γ : gname) (q : Qp)
| (** Points-to token *) nc_mapsto (l : loc) (dq : dfrac) (v : val)
| (** Owning invariant points-to token *) nc_inv_mapsto_own
    (l : loc) (v : val) (I : val → Prop)
| (** Invariant points-to token *) nc_inv_mapsto (l : loc) (I : val → Prop)
| (** Meta token *) nc_meta_token (l : loc) (E : coPset)
| (** Step number token *) nc_steps_lb (n : nat)
| (** Prophecy token *) nc_proph (p : proph_id) (pvs : list (val * val))
| (** Lifetime token *) nc_lft_tok (α : lft) (q : Qp)
| (** Dead lifetime token *) nc_lft_dead (α : lft)
| (** Eternal lifetime token *) nc_lft_eter (α : lft)
| (** Persistent lifetime inclusion *) nc_lft_sincl (α β : lft)
| (** Prophecy token *) nc_proph_tok (ξ : aprvarn) (q : Qp)
| (** Prophecy tokens *) nc_proph_toks (ξl : list aprvarn) (q : Qp)
| (** Prophecy observation *) nc_proph_obs (φπ : prophn Prop)
| (** Prophecy world satisfaction *) nc_proph_wsat
| (** Value observer *) nc_val_obs {X : nsynty} (γ : gname) (x : X)
| (** Prophecy controller *) nc_proph_ctrl {X : nsynty}
    (γ : gname) (x : X) (ξ : prvar X).
(** Nullary, large *)
Variant nconl0 : Type :=
| (** Simple invariant world satisfaction *) nc_sinv_wsat
| (** Invariant world satisfaction *) nc_inv_wsat
| (** Non-atomic invariant world satisfaction *) nc_na_inv_wsat
| (** Borrowing world satisfaction *) nc_borrow_wsat.
(** Unary *)
Variant ncon1 : Type :=
| (** Except-0 modality *) nc_except_0
| (** Persistence modality *) nc_persistently
| (** Plainly modality *) nc_plainly
| (** Basic update modality *) nc_bupd
| (** Fancy update modality *) nc_fupd (E E' : coPset).
Variant ncon2 : Type :=
| (** Conjunction *) nc_and
| (** Disjunction *) nc_or
| (** Implication *) nc_impl
| (** Separating conjunction *) nc_sep
| (** Magic wand *) nc_wand
| (** Basic update modality with the world satisfaction *) nc_bupdw
| (** Fasic update modality with the world satisfaction *)
    nc_fupdw (E E' : coPset).
(** Usual *)
Variant nconu : Type :=
| (** Partial *) nc_wpw (s : stuckness) (E : coPset) (e : expr)
| (** Total *) nc_twpw (s : stuckness) (E : coPset) (e : expr)
| (** Universal quantification *) nc_forall (A : Type)
| (** Existential quantification *) nc_exist (A : Type).
(** Domain of [nconu] *)
Definition nconu_dom (c : nconu) : Type := match c with
  | nc_wpw _ _ _ | nc_twpw _ _ _ => option val
  | nc_forall A | nc_exist A => A
  end.
(** Guarding *)
Variant ncong : Type :=
| (** Later modality *) nc_later
| (** Indirection modality *) nc_indir
| (** Simple invariant *) nc_sinv
| (** Invariant *) nc_inv (N : namespace)
| (** Non-atomic invariant *) nc_na_inv
    (p : na_inv_pool_name) (N : namespace)
| (** Closed borrower *) nc_borc (α : lft)
| (** Borrower *) nc_bor (α : lft)
| (** Open borrower *) nc_obor (α : lft) (q : Qp)
| (** Lender *) nc_lend (α : lft)
| (** Fractured borrower token *) nc_fbor (α : lft).
(** Domain of [ncong] *)
Definition ncong_dom (c : ncong) : Type := match c with
  | nc_fbor _ => Qp | _ => nat
  end.

(** [nProp]: Nola syntactic proposition
  Its universe level is strictly higher than those of [V : npvar]
  and the domain [A : Type] of [n_forall]/[n_exist].

  Connectives that operate on the context [Γ : nctx] take decomposed contexts
  [Γᵘ, Γᵍ] for smooth type inference. *)

Inductive nProp : nkind → nctx → Type :=

(** Basic connective *)
| n_0 {κ Γ} (c : ncon0) : nProp κ Γ
| n_l0 {Γ} (c : nconl0) : nProp nL Γ
| n_1 {κ Γ} (c : ncon1) (P : nProp κ Γ) : nProp κ Γ
| n_2 {κ Γ} (c : ncon2) (P Q : nProp κ Γ) : nProp κ Γ
| n_u {κ Γ} (c : nconu) (P : nconu_dom c → nProp κ Γ) : nProp κ Γ
| n_g {κ Γᵘ Γᵍ} (c : ncong) (P : ncong_dom c → nProp nL (;ᵞ Γᵘ ++ Γᵍ))
    : nProp κ (Γᵘ;ᵞ Γᵍ)

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

(** Constant proposition, ignoring the first unguarded/guarded variable *)
| n_constu {κ V Γᵘ Γᵍ} (P : nProp κ (Γᵘ;ᵞ Γᵍ)) : nProp κ (V :: Γᵘ;ᵞ Γᵍ)
| n_constg {κ V Γᵍ} (P : nProp κ (;ᵞ Γᵍ)) : nProp κ (;ᵞ V :: Γᵍ)
(** Guarded small variable *)
| n_vargs {κ Γᵘ Γᵍ} (s : schoice npargS Γᵍ) : nProp κ (Γᵘ;ᵞ Γᵍ)
(** Guarded large variable, [nPropL] only *)
| n_vargl {Γᵘ Γᵍ} (s : schoice npargL Γᵍ) : nProp nL (Γᵘ;ᵞ Γᵍ)
(** Unguarded small variable, [nPropL] only *)
| n_varus {Γᵘ Γᵍ} (s : schoice npargS Γᵘ) : nProp nL (Γᵘ;ᵞ Γᵍ)
(** Substituted [n_varus] *)
| n_subus {Γ} (P : nProp nS (;ᵞ)) : nProp nL Γ.

Notation nPropS := (nProp nS).
Notation nPropL := (nProp nL).

(** ** Notations for [nProp] connectives *)

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.
Local Open Scope nProp_scope.

Notation "'⌜' φ '⌝'" := (n_0 (nc_pure φ)) : nProp_scope.
Notation "'True'" := ⌜True⌝ : nProp_scope.
Notation "'False'" := ⌜False⌝ : nProp_scope.
Notation n_na_own p E := (n_0 (nc_na_own p E)).
Notation n_cinv_own γ q := (n_0 (nc_cinv_own γ q)).
Notation "l ↦ dq v" := (n_0 (nc_mapsto l dq v)) : nProp_scope.
Notation "l ↦_ I v" := (n_0 (nc_inv_mapsto_own l I v)) : nProp_scope.
Notation "l ↦_ I □" := (n_0 (nc_inv_mapsto l I)): nProp_scope.
Notation n_meta_token l E := (n_0 (nc_meta_token l E)).
Notation n_steps_lb n := (n_0 (nc_steps_lb n)).
Notation n_proph p pvs := (n_0 (nc_proph p pvs)).
Notation "q .[ α ]" := (n_0 (nc_lft_tok α q)) : nProp_scope.
Notation "[† α ]" := (n_0 (nc_lft_dead α)) : nProp_scope.
Notation "[∞ α ]" := (n_0 (nc_lft_eter α)) : nProp_scope.
Notation "α ⊑□ β" := (n_0 (nc_lft_sincl α β)) : nProp_scope.
Notation n_proph_wsat := (n_0 nc_proph_wsat).
Notation "q :[ ξ ]" := (n_0 (nc_proph_tok ξ q)) : nProp_scope.
Notation "q :∗[ ξ ]" := (n_0 (nc_proph_toks ξ q)) : nProp_scope.
Notation ".⟨ φπ ⟩" := (n_0 (nc_proph_obs φπ)) (only parsing) : nProp_scope.
Notation "⟨ π , φ ⟩" := (n_0 (nc_proph_obs (λ π, φ))) : nProp_scope.
Notation n_val_obs γ x := (n_0 (nc_val_obs γ x)).
Notation n_proph_ctrl γ x ξ := (n_0 (nc_proph_ctrl γ x ξ)).
Notation n_sinv_wsat := (n_l0 nc_sinv_wsat).
Notation n_inv_wsat := (n_l0 nc_inv_wsat).
Notation n_na_inv_wsat := (n_l0 nc_na_inv_wsat).
Notation n_borrow_wsat := (n_l0 nc_borrow_wsat).
Notation "◇ P" := (n_1 nc_except_0 P) : nProp_scope.
Notation "□ P" := (n_1 nc_persistently P) : nProp_scope.
Notation "■ P" := (n_1 nc_plainly P) : nProp_scope.
Notation "|==> P" := (n_1 nc_bupd P) : nProp_scope.
Notation "|={ E , E' }=> P" := (n_1 (nc_fupd E E') P) : nProp_scope.
Notation "|={ E }=> P" := (n_1 (nc_fupd E E) P) : nProp_scope.
Infix "∧" := (n_2 nc_and) : nProp_scope.
Infix "∨" := (n_2 nc_or) : nProp_scope.
Infix "→" := (n_2 nc_impl) : nProp_scope.
Notation "¬ P" := (P → False) : nProp_scope.
Infix "∗" := (n_2 nc_sep) : nProp_scope.
Infix "-∗" := (n_2 nc_wand) : nProp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : nProp_scope.
Notation "P ={ E , E' }=∗ Q" := (P -∗ |={E,E'}=> Q) : nProp_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : nProp_scope.
Notation "|=[ W ] => P" := (n_2 nc_bupdw W P) : nProp_scope.
Notation "P =[ W ]=∗ Q" := (P -∗ |=[W]=> Q) : nProp_scope.
Notation "|=[ W ] { E , E' }=> P" := (n_2 (nc_fupdw E E') W P) : nProp_scope.
Notation "|=[ W ] { E }=> P" := (n_2 (nc_fupdw E E) W P) : nProp_scope.
Notation "P =[ W ] { E , E' }=∗ Q" := (P -∗ |=[W]{E,E'}=> Q) : nProp_scope.
Notation "P =[ W ] { E }=∗ Q" := (P =[W]{E,E}=∗ Q) : nProp_scope.
Notation n_wpw W s E e Φ := (n_u (nc_wpw s E e) (of_option W Φ)).
Notation n_twpw W s E e Φ := (n_u (nc_twpw s E e) (of_option W Φ)).
Notation "WP[ W ] e @ s ; E {{ Φ } }" := (n_wpw W s E e Φ) (only parsing)
  : nProp_scope.
Notation "WP[ W ] e @ s ; E {{ v , P } }" := (n_wpw W s E e (λ v, P))
  : nProp_scope.
Notation "WP[ W ] e @ s ; E [{ Φ } ]" := (n_twpw W s E e Φ) (only parsing)
  : nProp_scope.
Notation "WP[ W ] e @ s ; E [{ v , P } ]" := (n_twpw W s E e (λ v, P))
  : nProp_scope.
Notation n_forall A := (n_u (nc_forall A)).
Notation "∀'" := (n_forall _) (only parsing) : nProp_scope.
Notation "∀ a .. z , P" :=
  (n_forall _ (λ a, .. (n_forall _ (λ z, P%n)) ..)) : nProp_scope.
Notation n_exist A := (n_u (nc_exist A)).
Notation "∃'" := (n_exist _) (only parsing) : nProp_scope.
Notation "∃ a .. z , P" :=
  (n_exist _ (λ a, .. (n_exist _ (λ z, P%n)) ..)) : nProp_scope.

Notation n_g1' Γᵘ c P := (n_g (Γᵘ:=Γᵘ) c (λ _, P%n)) (only parsing).
Notation n_g1 c P := (n_g c (λ _, P%n)).
Notation "▷{ Γᵘ } P" := (n_g1' Γᵘ nc_later P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "▷ P" := (n_g1 nc_later P) : nProp_scope.
Notation "○{ Γᵘ } P" := (n_g1' Γᵘ nc_indir P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "○ P" := (n_g1 nc_indir P)
  (at level 20, right associativity, format "○  P") : nProp_scope.
Notation n_inv' Γᵘ N P := (n_g1' Γᵘ (nc_inv N) P) (only parsing).
Notation n_inv N P := (n_inv' _ N P).
Notation n_na_inv' Γᵘ p N P :=
  (n_g1' Γᵘ (nc_na_inv p N) P) (only parsing).
Notation n_na_inv p N P := (n_na_inv' _ p N P).
Notation n_borc' Γᵘ α P := (n_g1' Γᵘ (nc_borc α) P) (only parsing).
Notation n_borc α P := (n_borc' _ α P).
Notation n_bor' Γᵘ α P := (n_g1' Γᵘ (nc_bor α) P) (only parsing).
Notation n_bor α P := (n_bor' _ α P).
Notation n_obor' Γᵘ α q P := (n_g1' Γᵘ (nc_obor α q) P) (only parsing).
Notation n_obor α q P := (n_obor' _ α q P).
Notation n_lend' Γᵘ α P := (n_g1' Γᵘ (nc_lend α) P) (only parsing).
Notation n_lend α P := (n_lend' _ α P).
Notation n_fbor' Γᵘ α Φ := (n_g (Γᵘ:=Γᵘ) (nc_fbor α) Φ) (only parsing).
Notation n_fbor α Φ := (n_fbor' _ α Φ).
Notation n_fbor_mapsto α l v := (n_fbor α (λ q, l ↦{#q} v)).
Notation "l ↦[ α ] v" := (n_fbor_mapsto α l v)
  (at level 20, format "l  ↦[ α ]  v") : nProp_scope.

Notation "∀: V , P" := (n_n_forall V P)
  (at level 200, right associativity,
    format "'[' '[' ∀:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "∃: V , P" := (n_n_exist V P)
  (at level 200, right associativity,
    format "'[' '[' ∃:  V ']' ,  '/' P ']'") : nProp_scope.
Notation "rec:ˢ'" := n_recs (only parsing) : nProp_scope.
Notation "rec:ˢ a , P" := (n_recs (λ a, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ˢ  a ,  '/' P ']' ']'") : nProp_scope.
Notation "rec:ˡ'" := n_recl (only parsing) : nProp_scope.
Notation "rec:ˡ a , P" := (n_recl (λ a, P))
  (at level 200, right associativity,
    format "'[' '[' rec:ˡ  a ,  '/' P ']' ']'") : nProp_scope.

Notation "¢ᵘ{ Γᵘ } P" := (n_constu (Γᵘ:=Γᵘ) P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "¢ᵘ P" := (n_constu P) (at level 20, right associativity)
  : nProp_scope.
Notation "¢ᵍ{ Γᵍ } P" := (n_constg (Γᵍ:=Γᵍ) P)
  (at level 20, right associativity, only parsing) : nProp_scope.
Notation "¢ᵍ P" := (n_constg P) (at level 20, right associativity)
  : nProp_scope.
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
  we keep the function polymorphic over [κ] for ease of definition. *)
Reserved Notation "↑ˡ P" (at level 20, right associativity).
Fixpoint nlarge {κ Γ} (P : nProp κ Γ) : nPropL Γ :=
  match P with
  | n_0 c => n_0 c | n_l0 c => n_l0 c
  | n_1 c P => n_1 c (↑ˡ P) | n_2 c P Q => n_2 c (↑ˡ P) (↑ˡ Q)
  | n_u c Φ => n_u c (λ a, ↑ˡ Φ a) | n_g c Φ => n_g c Φ
  | ∀: V, P => ∀: V, ↑ˡ P | ∃: V, P => ∃: V, ↑ˡ P
  | rec:ˢ' Φ a => rec:ˢ' Φ a | rec:ˡ' Φ a => rec:ˡ' Φ a
  | ¢ᵘ P => ¢ᵘ ↑ˡ P | ¢ᵍ P => ¢ᵍ ↑ˡ P
  | %ᵍˢ s => %ᵍˢ s | %ᵍˡ s => %ᵍˡ s | %ᵘˢ s => %ᵘˢ s | !ᵘˢ P => !ᵘˢ P
  end
where "↑ˡ P" := (nlarge P) : nola_scope.

(** [nunsmall]: Turn [nPropS Γ] into [nProp κ Γ] *)
Definition nunsmall {κ Γ} (P : nPropS Γ) : nProp κ Γ :=
  match κ with nS => P | nL => ↑ˡ P end.

(** [↑ˡ] is identity for [nPropL] *)
Local Lemma nlarge_id' {κ Γ} {P : nProp κ Γ} (eq : κ = nL) :
  ↑ˡ P = rew[λ κ, nProp κ Γ] eq in P.
Proof.
  move: κ Γ P eq. fix FIX 3=> κ Γ.
  case=>/=; intros; subst=>//=; try rewrite (eq_dec_refl eq)/=; f_equal;
    try funext=> ?; exact (FIX _ _ _ eq_refl).
Qed.
Lemma nlarge_id {Γ} {P : nPropL Γ} : ↑ˡ P = P.
Proof. exact (nlarge_id' eq_refl). Qed.

(** [↑ˡ] over [nunsmall] *)
Lemma nlarge_nunsmall {Γ κ} {P : nPropS Γ} :
  ↑ˡ (nunsmall (κ:=κ) P) = ↑ˡ P.
Proof. case κ=>//=. exact nlarge_id. Qed.
