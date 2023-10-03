(** * [deriv]: Derivability *)

From nola.util Require Export pred wft.
From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import proofmode.

(** ** Preliminaries *)

(** [darg]: Argument data of [deriv_ty D] *)

#[projections(primitive)]
Record darg {A : Type} (F : A → Type) := Darg {
  (** Index *)
  darg_idx : A;
  (** Data *)
  darg_data : F darg_idx;
}.
Arguments Darg {_ _} _ _.
Arguments darg_idx {_ _} _.
Arguments darg_data {_ _} _.
Add Printing Constructor darg.
Definition dargO {A} F := leibnizO (darg (A:=A) F).

(** [dwrap]: Wrapper for derivability *)

#[projections(primitive)]
Record dwrap (A : Type) := Dwrap { dunwrap : A }.
Arguments Dwrap {_} _.
Arguments dunwrap {_} _.
Add Printing Constructor dwrap.

(** Notation for [dwrap] *)
Module DerivNotation.
  Notation "⸨ iP ⸩ ( d )" := (dunwrap d iP)
    (format "'[' ⸨  iP  ⸩ '/  ' ( d ) ']'") : nola_scope.
  Notation "⸨ P ⸩ ( d , i )" := (dunwrap d (Darg i P))
    (format "'[' ⸨  P  ⸩ '/  ' ( d ,  i ) ']'") : nola_scope.
End DerivNotation.
Import DerivNotation.

(** Make [dwrap A] [ofe] for [A : ofe] *)
#[export] Instance dwrap_equiv `{!Equiv A} : Equiv (dwrap A)
  := λ '(Dwrap a) '(Dwrap b), a ≡ b.
#[export] Instance dwrap_dist `{!Dist A} : Dist (dwrap A)
  := λ n '(Dwrap a) '(Dwrap b), a ≡{n}≡ b.
Lemma dwrap_ofe_mixin (A : ofe) : OfeMixin (dwrap A).
Proof.
  split; unfold equiv, dist, dwrap_equiv, dwrap_dist.
  - move=> [?][?]. apply equiv_dist.
  - move=> ?. split; move=> *; by [|symmetry|etrans].
  - move=> ??[?][?]. apply dist_lt.
Qed.
Canonical dwrap_ofe (A : ofe) := Ofe (dwrap A) (dwrap_ofe_mixin A).
#[export] Instance Dwrap_ne `{A : ofe} : NonExpansive (Dwrap (A:=A)).
Proof. solve_proper. Qed.

(** [derivs]: Derivation structure *)
#[projections(primitive)]
Record derivs : Type := Derivs {
  (** Index type, with a well-founded relation *)
  derivs_idx : wft;
  (** Data type *)
  derivs_data : derivs_idx → Type;
  (** BI logic for interpretation *)
  derivs_bi : bi;
}.
Add Printing Constructor derivs.
Implicit Type D : derivs.

(** Type for derivability *)
Notation deriv_aty D := (dargO D.(derivs_data)).
Definition deriv_ty' D : Type := deriv_aty D -d> D.(derivs_bi).
Notation deriv_ty D := (dwrap (deriv_ty' D)).

(** [derivsi]: [derivs] with interpretation *)
Structure derivsi : Type := Derivsi {
  derivsi_derivs :> derivs;
  (** Interpretation parameterized over the derivability *)
  #[canonical=no] derivsi_intp :
    deriv_ty derivsi_derivs → deriv_ty' derivsi_derivs;
}.
Arguments derivsi_intp {D} : rename.
Implicit Type DI : derivsi.

(** Notation for [derivs_intp] *)
Notation derivsi_intp' d := (Dwrap (derivsi_intp d)).
Module IntpNotation.
  Notation "⟦ iP ⟧ ( d )" := (derivsi_intp d iP)
    (format "'[' ⟦  iP  ⟧ '/  ' ( d ) ']'") : nola_scope.
  Notation "⟦ P ⟧ ( d , i )" := (derivsi_intp d (Darg i P))
    (format "'[' ⟦  P  ⟧ '/  ' ( d ,  i ) ']'") : nola_scope.
End IntpNotation.
Import IntpNotation.

(** Magic wand between derivabilitys *)
Definition wandˢ {D} (d d' : deriv_ty D) : D.(derivs_bi) :=
  ∀ iP, ⸨ iP ⸩(d) -∗ ⸨ iP ⸩(d').
Infix "-∗ˢ" := wandˢ (at level 99, right associativity) : nola_scope.
#[export] Instance wandˢ_ne {D} : NonExpansive2 (wandˢ (D:=D)).
Proof.
  unfold wandˢ=> ??? seq ?? d'eq. do 3 f_equiv; [apply seq|apply d'eq].
Qed.

(** Propositions for soundness of a derivability *)
Definition dsound' {DI} (d d' : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ P, ⸨ P ⸩(d, i) -∗ ⟦ P ⟧(d', i).
Definition dsound {DI} (d : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ P, ⸨ P ⸩(d, i) -∗ ⟦ P ⟧(d, i).
Definition low_dsound {DI} (d : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ j, ⌜j ≺ i⌝ → dsound d j.

(** ** [derivy] : Characterization of the derivability *)

Inductive derivy DI (ih : deriv_ty DI → Prop) (d : deriv_ty DI) : Prop := {
  (** For [derivy_intp] *)
  derivy_byintp' :
    (* Parameterization by [derivy'] is for strict positivity *)
    ∃ derivy' : _ → Prop, (∀ d', derivy' d' → derivy DI ih d') ∧
    ∀ iP, let i := iP.(darg_idx) in
    (∀ d', ⌜derivy' d'⌝ → ⌜ih d'⌝ → □ dsound' d d' i -∗
      □ (d -∗ˢ d') -∗ □ low_dsound d' i -∗ ⟦ iP ⟧(d'))
    -∗ ⸨ iP ⸩(d)
}.
Existing Class derivy.

(** Get the derivability [⸨ P ⸩(d, i)] by the interpretaion *)
Lemma derivy_byintp `{!derivy DI ih d} {i P} :
  (∀ d',
    (* Take any derivability [d'] *)
    ⌜derivy DI ih d'⌝ →
    (* Get access to the inductive hypothesis *)
    ⌜ih d'⌝ →
    (* Turn the derivability at level [i] into the interpretation *)
    □ dsound' d d' i -∗
    (* Turn the coinductive derivability into
      the given derivability *)
    □ (d -∗ˢ d') -∗
    (* Turn the given derivability at a level lower than [i]
      into the interpretation *)
    □ low_dsound d' i -∗
    ⟦ P ⟧(d', i))
  -∗ ⸨ P ⸩(d, i).
Proof.
  have X := (@derivy_byintp' _ ih d). move: X=> [dy[dyto byintp]]. iIntros "→".
  iApply byintp. iIntros (d' dyd'). apply dyto in dyd'. by iApply "→".
Qed.

(** [derivy] is monotone over the inductive hypothesis *)
Lemma derivy_mono `{!derivy DI ih d} (ih' : _ → Prop) :
  (∀ d', ih d' → ih' d') → derivy DI ih' d.
Proof.
  move=> ihto. move: d derivy0. fix FIX 2=> d [[dy[dyto byintp]]]. split.
  exists (derivy _ ih'). split; [done|]=>/= ?. iIntros "big". iApply byintp.
  iIntros (???). iApply "big"; iPureIntro; by [apply FIX, dyto|apply ihto].
Qed.

(** [derivy] can accumulate the inductive hypothesis *)
Lemma derivy_acc {DI ih} res :
  (∀ d, derivy DI (res ∧₁ ih) d → res d) → ∀ d, derivy DI ih d → res d.
Proof.
  move=> to d dyd. apply to. move: d dyd. fix FIX 2=> d [[dy[dyto byintp]]].
  split. exists (derivy _ (res ∧₁ ih)). split; [done|]=>/= ?. iIntros "big".
  iApply byintp. iIntros (? dyd' ?). move: dyd'=>/dyto/FIX ?.
  iApply "big"; iPureIntro; [done|]. split; by [apply to|].
Qed.

(** Introduce a derivability *)
Lemma derivy_intro `{!derivy DI ih d} {i P} :
  (∀ d', ⌜derivy DI ih d'⌝ → ⌜ih d'⌝ → ⟦ P ⟧(d', i)) -∗ ⸨ P ⸩(d, i).
Proof.
  iIntros "∀P". iApply derivy_byintp. iIntros (???) "_ _ _". by iApply "∀P".
Qed.

(** Update derivabilitys *)
Lemma derivy_map `{!derivy DI ih d} {i P Q} :
  (∀ d', ⌜derivy DI ih d'⌝ → ⌜ih d'⌝ → ⟦ P ⟧(d', i) -∗ ⟦ Q ⟧(d', i)) -∗
  ⸨ P ⸩(d, i) -∗ ⸨ Q ⸩(d, i).
Proof.
  iIntros "∀PQ P". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply "∀PQ"; by [| |iApply "→"].
Qed.
Lemma derivy_map2 `{!derivy DI ih d} {i P Q R} :
  (∀ d', ⌜derivy DI ih d'⌝ → ⌜ih d'⌝ → ⟦ P ⟧(d', i) -∗ ⟦ Q ⟧(d', i) -∗
    ⟦ R ⟧(d', i)) -∗
  ⸨ P ⸩(d, i) -∗ ⸨ Q ⸩(d, i) -∗ ⸨ R ⸩(d, i).
Proof.
  iIntros "∀PQ P Q". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply ("∀PQ" with "[//] [//] [P]"); by iApply "→".
Qed.
Lemma derivy_map3 `{!derivy DI ih d} {i P Q R S} :
  (∀ d', ⌜derivy DI ih d'⌝ → ⌜ih d'⌝ → ⟦ P ⟧(d', i) -∗ ⟦ Q ⟧(d', i) -∗
    ⟦ R ⟧(d', i) -∗ ⟦ S ⟧(d', i)) -∗
  ⸨ P ⸩(d, i) -∗ ⸨ Q ⸩(d, i) -∗ ⸨ R ⸩(d, i) -∗ ⸨ S ⸩(d, i).
Proof.
  iIntros "∀PQ P Q R". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply ("∀PQ" with "[//] [//] [P] [Q]"); by iApply "→".
Qed.
Lemma derivy_map_lev `{!derivy DI ih d} {i j P Q} :
  i ≺ j → (∀ d', ⌜derivy DI ih d'⌝ → ⌜ih d'⌝ → ⟦ P ⟧(d', i) -∗ ⟦ Q ⟧(d', j)) -∗
  ⸨ P ⸩(d, i) -∗ ⸨ Q ⸩(d, j).
Proof.
  iIntros (ij) "∀PQ P". iApply derivy_byintp. iIntros (???) "_ #→d' #d'→".
  iApply "∀PQ"; [done..|]. iApply "d'→"; [done|]. by iApply "→d'".
Qed.

(** ** [deriv]: Derivability *)

(** [deriv_gen]: What becomes [deriv] by taking [bi_least_fixpoint] *)
Definition deriv_gen {DI} (self : deriv_ty' DI)
  : deriv_ty' DI := λ iP, let i := iP.(darg_idx) in
  (∀ d', ⌜derivy DI True₁ d'⌝ → □ dsound' (Dwrap self) d' i -∗
    □ (Dwrap self -∗ˢ d') -∗ □ low_dsound d' i -∗
    ⟦ iP ⟧(d'))%I.
#[export] Instance deriv_gen_mono {DI} : BiMonoPred (deriv_gen (DI:=DI)).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" (?) "big".
  iIntros (??) "#AΨ #BΨ".
  iApply "big"; [done|..]; iIntros "!> % ?"; [iApply "AΨ"|iApply "BΨ"];
    by iApply "ΦΨ".
Qed.

(** [deriv]: Derivability *)
Definition deriv {DI} : deriv_ty DI := Dwrap (bi_least_fixpoint deriv_gen).

(** [deriv] satisfies [derivy] *)
#[export] Instance deriv_derivy {DI} : derivy DI True₁ deriv.
Proof. split.
  eexists _. split; [done|]=>/=. iIntros (?) "big".
  rewrite least_fixpoint_unfold. iIntros (??) "#A #B".
  iApply "big"; [done..| |]; iIntros "!> % ?/="; by [iApply "A"|iApply "B"].
Qed.

(** [deriv] is sound w.r.t. the interpretation under [deriv] *)
Lemma deriv_sound {DI i} : ⊢ dsound (DI:=DI) deriv i.
Proof.
  elim: {i}(wft_lt_wf i)=> i _ IH. iIntros (P) "/= X".
  have: (Darg i P).(darg_idx) = i by done.
  move: {P}(Darg i P : deriv_aty _)=> iP eq. iRevert (eq). iRevert (iP) "X".
  iApply least_fixpoint_ind. iIntros "!>" ([??]) "/= X ->".
  iApply ("X" $! _ deriv_derivy); iIntros "!> % /=".
  { iIntros "[X _]". by iApply "X". } { iIntros "[_ $]". }
  { iIntros (?). by iApply IH. }
Qed.
