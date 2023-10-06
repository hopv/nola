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
  Notation "⸨ iP ⸩ ( δ )" := (dunwrap δ iP)
    (format "'[' ⸨  iP  ⸩ '/  ' ( δ ) ']'") : nola_scope.
  Notation "⸨ P ⸩ ( δ , i )" := (dunwrap δ (Darg i P))
    (format "'[' ⸨  P  ⸩ '/  ' ( δ ,  i ) ']'") : nola_scope.
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
Notation derivsi_intp' δ := (Dwrap (derivsi_intp δ)).
Module IntpNotation.
  Notation "⟦ iP ⟧ ( δ )" := (derivsi_intp δ iP)
    (format "'[' ⟦  iP  ⟧ '/  ' ( δ ) ']'") : nola_scope.
  Notation "⟦ P ⟧ ( δ , i )" := (derivsi_intp δ (Darg i P))
    (format "'[' ⟦  P  ⟧ '/  ' ( δ ,  i ) ']'") : nola_scope.
End IntpNotation.
Import IntpNotation.

(** Magic wand between derivabilitys *)
Definition wandˢ {D} (δ δ' : deriv_ty D) : D.(derivs_bi) :=
  ∀ iP, ⸨ iP ⸩(δ) -∗ ⸨ iP ⸩(δ').
Infix "-∗ˢ" := wandˢ (at level 99, right associativity) : nola_scope.
#[export] Instance wandˢ_ne {D} : NonExpansive2 (wandˢ (D:=D)).
Proof.
  unfold wandˢ=> ??? seq ?? δ'eq. do 3 f_equiv; [apply seq|apply δ'eq].
Qed.

(** Propositions for soundness of a derivability *)
Definition dsound' {DI} (δ δ' : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ P, ⸨ P ⸩(δ, i) -∗ ⟦ P ⟧(δ', i).
Definition dsound {DI} (δ : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ P, ⸨ P ⸩(δ, i) -∗ ⟦ P ⟧(δ, i).
Definition low_dsound {DI} (δ : deriv_ty DI) i : DI.(derivs_bi) :=
  ∀ j, ⌜j ≺ i⌝ → dsound δ j.

(** ** [derivy] : Characterization of the derivability *)

Inductive derivy DI (ih : deriv_ty DI → Prop) (δ : deriv_ty DI) : Prop := {
  (** For [derivy_intp] *)
  derivy_byintp' :
    (* Parameterization by [derivy'] is for strict positivity *)
    ∃ derivy' : _ → Prop, (∀ δ', derivy' δ' → derivy DI ih δ') ∧
    ∀ iP, let i := iP.(darg_idx) in
    (∀ δ', ⌜derivy' δ'⌝ → ⌜ih δ'⌝ → □ dsound' δ δ' i -∗
      □ (δ -∗ˢ δ') -∗ □ low_dsound δ' i -∗ ⟦ iP ⟧(δ'))
    -∗ ⸨ iP ⸩(δ)
}.
Existing Class derivy.

(** Get the derivability [⸨ P ⸩(δ, i)] by the interpretaion *)
Lemma derivy_byintp `{!derivy DI ih δ} {i P} :
  (∀ δ',
    (* Take any derivability [δ'] *)
    ⌜derivy DI ih δ'⌝ →
    (* Get access to the inductive hypothesis *)
    ⌜ih δ'⌝ →
    (* Turn the derivability at level [i] into the interpretation *)
    □ dsound' δ δ' i -∗
    (* Turn the coinductive derivability into
      the given derivability *)
    □ (δ -∗ˢ δ') -∗
    (* Turn the given derivability at a level lower than [i]
      into the interpretation *)
    □ low_dsound δ' i -∗
    ⟦ P ⟧(δ', i))
  -∗ ⸨ P ⸩(δ, i).
Proof.
  have X := (@derivy_byintp' _ ih δ). move: X=> [dy[dyto byintp]]. iIntros "→".
  iApply byintp. iIntros (δ' dyd'). apply dyto in dyd'. by iApply "→".
Qed.

(** [derivy] is monotone over the inductive hypothesis *)
Lemma derivy_mono `{!derivy DI ih δ} (ih' : _ → Prop) :
  (∀ δ', ih δ' → ih' δ') → derivy DI ih' δ.
Proof.
  move=> ihto. move: δ derivy0. fix FIX 2=> δ [[dy[dyto byintp]]]. split.
  exists (derivy _ ih'). split; [done|]=>/= ?. iIntros "big". iApply byintp.
  iIntros (???). iApply "big"; iPureIntro; by [apply FIX, dyto|apply ihto].
Qed.

(** [derivy] can accumulate the inductive hypothesis *)
Lemma derivy_acc {DI ih} res :
  (∀ δ, derivy DI (res ∧₁ ih) δ → res δ) → ∀ δ, derivy DI ih δ → res δ.
Proof.
  move=> to δ dyd. apply to. move: δ dyd. fix FIX 2=> δ [[dy[dyto byintp]]].
  split. exists (derivy _ (res ∧₁ ih)). split; [done|]=>/= ?. iIntros "big".
  iApply byintp. iIntros (? dyd' ?). move: dyd'=>/dyto/FIX ?.
  iApply "big"; iPureIntro; [done|]. split; by [apply to|].
Qed.

(** Introduce a derivability *)
Lemma derivy_intro `{!derivy DI ih δ} {i P} :
  (∀ δ', ⌜derivy DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ P ⟧(δ', i)) -∗ ⸨ P ⸩(δ, i).
Proof.
  iIntros "∀P". iApply derivy_byintp. iIntros (???) "_ _ _". by iApply "∀P".
Qed.

(** Update derivabilitys *)
Lemma derivy_map `{!derivy DI ih δ} {i P Q} :
  (∀ δ', ⌜derivy DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ P ⟧(δ', i) -∗ ⟦ Q ⟧(δ', i)) -∗
  ⸨ P ⸩(δ, i) -∗ ⸨ Q ⸩(δ, i).
Proof.
  iIntros "∀PQ P". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply "∀PQ"; by [| |iApply "→"].
Qed.
Lemma derivy_map2 `{!derivy DI ih δ} {i P Q R} :
  (∀ δ', ⌜derivy DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ P ⟧(δ', i) -∗ ⟦ Q ⟧(δ', i) -∗
    ⟦ R ⟧(δ', i)) -∗
  ⸨ P ⸩(δ, i) -∗ ⸨ Q ⸩(δ, i) -∗ ⸨ R ⸩(δ, i).
Proof.
  iIntros "∀PQ P Q". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply ("∀PQ" with "[//] [//] [P]"); by iApply "→".
Qed.
Lemma derivy_map3 `{!derivy DI ih δ} {i P Q R S} :
  (∀ δ', ⌜derivy DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ P ⟧(δ', i) -∗ ⟦ Q ⟧(δ', i) -∗
    ⟦ R ⟧(δ', i) -∗ ⟦ S ⟧(δ', i)) -∗
  ⸨ P ⸩(δ, i) -∗ ⸨ Q ⸩(δ, i) -∗ ⸨ R ⸩(δ, i) -∗ ⸨ S ⸩(δ, i).
Proof.
  iIntros "∀PQ P Q R". iApply derivy_byintp. iIntros (???) "#→ _ _".
  iApply ("∀PQ" with "[//] [//] [P] [Q]"); by iApply "→".
Qed.
Lemma derivy_map_lev `{!derivy DI ih δ} {i j P Q} :
  i ≺ j → (∀ δ', ⌜derivy DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ P ⟧(δ', i) -∗ ⟦ Q ⟧(δ', j)) -∗
  ⸨ P ⸩(δ, i) -∗ ⸨ Q ⸩(δ, j).
Proof.
  iIntros (ij) "∀PQ P". iApply derivy_byintp. iIntros (???) "_ #→δ' #δ'→".
  iApply "∀PQ"; [done..|]. iApply "δ'→"; [done|]. by iApply "→δ'".
Qed.

(** ** [deriv]: Derivability *)

(** [deriv_gen]: What becomes [deriv] by taking [bi_least_fixpoint] *)
Definition deriv_gen {DI} (self : deriv_ty' DI)
  : deriv_ty' DI := λ iP, let i := iP.(darg_idx) in
  (∀ δ', ⌜derivy DI True₁ δ'⌝ → □ dsound' (Dwrap self) δ' i -∗
    □ (Dwrap self -∗ˢ δ') -∗ □ low_dsound δ' i -∗
    ⟦ iP ⟧(δ'))%I.
#[export] Instance deriv_gen_mono {DI} : BiMonoPred (deriv_gen (DI:=DI)).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" (?) "big".
  iIntros (??) "#AΨ #BΨ".
  iApply "big"; [done|..]; iIntros "!> % ?"; [iApply "AΨ"|iApply "BΨ"];
    by iApply "ΦΨ".
Qed.

(** [deriv]: Derivability *)
Definition deriv_def {DI} : deriv_ty DI := Dwrap (bi_least_fixpoint deriv_gen).
Lemma deriv_aux : seal (@deriv_def). Proof. by eexists. Qed.
Definition deriv {DI} := deriv_aux.(unseal) DI.
Lemma deriv_unseal : @deriv = @deriv_def. Proof. exact: seal_eq. Qed.

(** [deriv] satisfies [derivy] *)
#[export] Instance deriv_derivy {DI} : derivy DI True₁ deriv.
Proof.
  rewrite deriv_unseal. split. eexists _. split; [done|]=>/=. iIntros (?) "big".
  rewrite least_fixpoint_unfold. iIntros (??) "#A #B".
  iApply "big"; [done..| |]; iIntros "!> % ?/="; by [iApply "A"|iApply "B"].
Qed.

(** [deriv] is sound w.r.t. the interpretation under [deriv] *)
Lemma deriv_sound {DI i} : ⊢ dsound (DI:=DI) deriv i.
Proof.
  rewrite deriv_unseal. elim: {i}(wft_lt_wf i)=> i _ IH. iIntros (P) "/= X".
  have: (Darg i P).(darg_idx) = i by done.
  move: {P}(Darg i P : deriv_aty _)=> iP eq. iRevert (eq). iRevert (iP) "X".
  iApply least_fixpoint_ind. iIntros "!>" ([??]) "/= X ->".
  rewrite -deriv_unseal. iApply ("X" $! _ deriv_derivy); iIntros "!> % /=";
    rewrite deriv_unseal. { iIntros "[X _]". by iApply "X". }
  { iIntros "[_ $]". } { iIntros (?). by iApply IH. }
Qed.
