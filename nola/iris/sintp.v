(** * [sintp]: Strong interpretation *)

From nola.util Require Export pred wft.
From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import proofmode.

(** ** Preliminaries *)

(** [sarg]: Argument data of [sintp_ty IT] *)

#[projections(primitive)]
Record sarg {A : Type} (F : A → Type) := Sarg {
  (** Index *)
  sarg_idx : A;
  (** Data *)
  sarg_data : F sarg_idx;
}.
Arguments Sarg {_ _} _ _.
Arguments sarg_idx {_ _} _.
Arguments sarg_data {_ _} _.
Add Printing Constructor sarg.
Definition sargO {A} F := leibnizO (sarg (A:=A) F).

(** [swrap]: Wrapper for strong interpretation *)

#[projections(primitive)]
Record swrap (A : Type) := Swrap { sunwrap : A }.
Arguments Swrap {_} _.
Arguments sunwrap {_} _.
Add Printing Constructor swrap.

(** Notation for [swrap] *)
Module SintpNotation.
  Notation "⸨ iP ⸩ ( s )" := (sunwrap s iP)
    (format "'[' ⸨  iP  ⸩ '/  ' ( s ) ']'") : nola_scope.
  Notation "⸨ P ⸩ ( s , i )" := (sunwrap s (Sarg i P))
    (format "'[' ⸨  P  ⸩ '/  ' ( s ,  i ) ']'") : nola_scope.
End SintpNotation.
Import SintpNotation.

(** Make [swrap A] [ofe] for [A : ofe] *)
#[export] Instance swrap_equiv `{!Equiv A} : Equiv (swrap A)
  := λ '(Swrap a) '(Swrap b), a ≡ b.
#[export] Instance swrap_dist `{!Dist A} : Dist (swrap A)
  := λ n '(Swrap a) '(Swrap b), a ≡{n}≡ b.
Lemma swrap_ofe_mixin (A : ofe) : OfeMixin (swrap A).
Proof.
  split; unfold equiv, dist, swrap_equiv, swrap_dist.
  - move=> [?][?]. apply equiv_dist.
  - move=> ?. split; move=> *; by [|symmetry|etrans].
  - move=> ??[?][?]. apply dist_lt.
Qed.
Canonical swrap_ofe (A : ofe) := Ofe (swrap A) (swrap_ofe_mixin A).
#[export] Instance Swrap_ne `{A : ofe} : NonExpansive (Swrap (A:=A)).
Proof. solve_proper. Qed.

(** [intps]: Interpretation structure *)
#[projections(primitive)]
Record intps : Type := Intps {
  (** Index type, with a well-founded relation *)
  intps_idx : wft;
  (** Data type *)
  intps_data : intps_idx → Type;
  (** BI logic for interpretation *)
  intps_bi : bi;
}.
Add Printing Constructor intps.
Implicit Type IT : intps.

(** Type for strong interpretation *)
Notation sintp_aty IT := (sargO IT.(intps_data)).
Definition sintp_ty' IT : Type := sintp_aty IT -d> IT.(intps_bi).
Notation sintp_ty IT := (swrap (sintp_ty' IT)).

(** [intpsi]: [intps] with interpretation *)
Structure intpsi : Type := Intpsi {
  intpsi_intps :> intps;
  (** Interpretation parameterized over the strong interpretation *)
  #[canonical=no] intpsi_intp : sintp_ty intpsi_intps → sintp_ty' intpsi_intps;
}.
Arguments intpsi_intp {IT} : rename.
Implicit Type ITI : intpsi.

(** Notation for [intps_intp] *)
Notation intpsi_intp' s := (Swrap (intpsi_intp s)).
Module IntpNotation.
  Notation "⟦ iP ⟧ ( s )" := (intpsi_intp s iP)
    (format "'[' ⟦  iP  ⟧ '/  ' ( s ) ']'") : nola_scope.
  Notation "⟦ P ⟧ ( s , i )" := (intpsi_intp s (Sarg i P))
    (format "'[' ⟦  P  ⟧ '/  ' ( s ,  i ) ']'") : nola_scope.
End IntpNotation.
Import IntpNotation.

(** Magic wand between strong interpretations *)
Definition wandˢ {IT} (s s' : sintp_ty IT) : IT.(intps_bi) :=
  ∀ iP, ⸨ iP ⸩(s) -∗ ⸨ iP ⸩(s').
Infix "-∗ˢ" := wandˢ (at level 99, right associativity) : nola_scope.
#[export] Instance wandˢ_ne {IT} : NonExpansive2 (wandˢ (IT:=IT)).
Proof.
  unfold wandˢ=> ??? seq ?? s'eq. do 3 f_equiv; [apply seq|apply s'eq].
Qed.

(** Propositions for soundness of a strong interpretation *)
Definition ssound' {ITI} (s s' : sintp_ty ITI) i : ITI.(intps_bi) :=
  ∀ P, ⸨ P ⸩(s, i) -∗ ⟦ P ⟧(s', i).
Definition ssound {ITI} (s : sintp_ty ITI) i : ITI.(intps_bi) :=
  ∀ P, ⸨ P ⸩(s, i) -∗ ⟦ P ⟧(s, i).
Definition low_ssound {ITI} (s : sintp_ty ITI) i : ITI.(intps_bi) :=
  ∀ j, ⌜j ≺ i⌝ → ssound s j.

(** ** [sintpy] : Characterization of the strong interpretation *)

Inductive sintpy ITI (ih : sintp_ty ITI → Prop) (s : sintp_ty ITI) : Prop := {
  (** For [sintpy_intp] *)
  sintpy_byintp' :
    (* Parameterization by [sintpy'] is for strict positivity *)
    ∃ sintpy' : _ → Prop, (∀ s', sintpy' s' → sintpy ITI ih s') ∧
    ∀ iP, let i := iP.(sarg_idx) in
    (∀ s', ⌜sintpy' s'⌝ → ⌜ih s'⌝ → □ ssound' s s' i -∗
      □ (s -∗ˢ s') -∗ □ low_ssound s' i -∗ ⟦ iP ⟧(s'))
    -∗ ⸨ iP ⸩(s)
}.
Existing Class sintpy.

(** Get the strong interpretation [⸨ P ⸩(s, i)] by the interpretaion *)
Lemma sintpy_byintp `{!sintpy ITI ih s} {i P} :
  (∀ s',
    (* Take any strong interpretation [s'] *)
    ⌜sintpy ITI ih s'⌝ →
    (* Inductive hypothesis *)
    ⌜ih s'⌝ →
    (* Turn the strong interpration at level [i] into the interpretation *)
    □ ssound' s s' i -∗
    (* Turn the coinductive strong interpretation into
      the given strong interpretation *)
    □ (s -∗ˢ s') -∗
    (* Turn the given strong interpretation at a level lower than [i]
      into the interpretation *)
    □ low_ssound s' i -∗
    ⟦ P ⟧(s', i))
  -∗ ⸨ P ⸩(s, i).
Proof.
  have X := (@sintpy_byintp' _ ih s). move: X=> [sy[syto byintp]].
  iIntros "intp". iApply byintp. iIntros (s' sys'). apply syto in sys'.
  by iApply "intp".
Qed.

(** [sintpy] is monotone over the inductive hypothesis *)
Lemma sintpy_mono `{!sintpy ITI ih s} {ih' : _ → Prop} :
  (∀ s', ih s' → ih' s') → sintpy ITI ih' s.
Proof.
  move=> ihto. move: s sintpy0. fix FIX 2=> s [[sy[syto byintp]]]. split.
  exists (sintpy _ ih'). split; [done|]=>/= ?. iIntros "big". iApply byintp.
  iIntros (???). iApply "big"; iPureIntro; by [apply FIX, syto|apply ihto].
Qed.

(** [sintpy] can accumulate the inductive hypothesis *)
Lemma sintpy_acc {ITI ih} res :
  (∀ s, sintpy ITI (res ∧₁ ih) s → res s) →
  (∀ s, sintpy ITI ih s → res s).
Proof.
  move=> to s sys. apply to. move: s sys. fix FIX 2=> s [[sy[syto byintp]]].
  split. exists (sintpy _ (res ∧₁ ih)). split; [done|]=>/= ?. iIntros "big".
  iApply byintp. iIntros (? sys' ?). move: sys'=>/syto/FIX ?.
  iApply "big"; iPureIntro; [done|]. split; [|done]. by apply to.
Qed.

(** Introduce a strong interpretation *)
Lemma sintpy_intro `{!sintpy ITI ih s} {i P} :
  (∀ s', ⌜sintpy ITI ih s'⌝ → ⌜ih s'⌝ → ⟦ P ⟧(s', i)) -∗ ⸨ P ⸩(s, i).
Proof.
  iIntros "∀P". iApply sintpy_byintp. iIntros (???) "_ _ _". by iApply "∀P".
Qed.

(** Update strong interpretations *)
Lemma sintpy_map `{!sintpy ITI ih s} {i P Q} :
  (∀ s', ⌜sintpy ITI ih s'⌝ → ⌜ih s'⌝ → ⟦ P ⟧(s', i) -∗ ⟦ Q ⟧(s', i)) -∗
  ⸨ P ⸩(s, i) -∗ ⸨ Q ⸩(s, i).
Proof.
  iIntros "∀PQ P". iApply sintpy_byintp. iIntros (???) "#to _ _".
  iApply "∀PQ"; by [| |iApply "to"].
Qed.
Lemma sintpy_map2 `{!sintpy ITI ih s} {i P Q R} :
  (∀ s', ⌜sintpy ITI ih s'⌝ → ⌜ih s'⌝ → ⟦ P ⟧(s', i) -∗ ⟦ Q ⟧(s', i) -∗
    ⟦ R ⟧(s', i)) -∗
  ⸨ P ⸩(s, i) -∗ ⸨ Q ⸩(s, i) -∗ ⸨ R ⸩(s, i).
Proof.
  iIntros "∀PQ P Q". iApply sintpy_byintp. iIntros (???) "#to _ _".
  iApply ("∀PQ" with "[//] [//] [P]"); by iApply "to".
Qed.
Lemma sintpy_map3 `{!sintpy ITI ih s} {i P Q R S} :
  (∀ s', ⌜sintpy ITI ih s'⌝ → ⌜ih s'⌝ → ⟦ P ⟧(s', i) -∗ ⟦ Q ⟧(s', i) -∗
    ⟦ R ⟧(s', i) -∗ ⟦ S ⟧(s', i)) -∗
  ⸨ P ⸩(s, i) -∗ ⸨ Q ⸩(s, i) -∗ ⸨ R ⸩(s, i) -∗ ⸨ S ⸩(s, i).
Proof.
  iIntros "∀PQ P Q R". iApply sintpy_byintp. iIntros (???) "#to _ _".
  iApply ("∀PQ" with "[//] [//] [P] [Q]"); by iApply "to".
Qed.
Lemma sintpy_map_lev `{!sintpy ITI ih s} {i j P Q} :
  i ≺ j → (∀ s', ⌜sintpy ITI ih s'⌝ → ⌜ih s'⌝ → ⟦ P ⟧(s', i) -∗ ⟦ Q ⟧(s', j)) -∗
  ⸨ P ⸩(s, i) -∗ ⸨ Q ⸩(s, j).
Proof.
  iIntros (ij) "∀PQ P". iApply sintpy_byintp. iIntros (???) "_ #tos' #s'to".
  iApply "∀PQ"; [done..|]. iApply "s'to"; [done|]. by iApply "tos'".
Qed.

(** ** [sintp]: Strong interpretation *)

(** [sintp_gen]: What becomes [sintp] by taking [bi_least_fixpoint] *)
Definition sintp_gen {ITI} (self : sintp_ty' ITI)
  : sintp_ty' ITI := λ iP, let i := iP.(sarg_idx) in
  (∀ s', ⌜sintpy ITI True₁ s'⌝ → □ ssound' (Swrap self) s' i -∗
    □ (Swrap self -∗ˢ s') -∗ □ low_ssound s' i -∗
    ⟦ iP ⟧(s'))%I.
#[export] Instance sintp_gen_mono {ITI} : BiMonoPred (sintp_gen (ITI:=ITI)).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" (?) "big".
  iIntros (??) "#AΨ #BΨ".
  iApply "big"; [done|..]; iIntros "!> % ?"; [iApply "AΨ"|iApply "BΨ"];
    by iApply "ΦΨ".
Qed.

(** [sintp]: Strong interpretation *)
Definition sintp {ITI} : sintp_ty ITI := Swrap (bi_least_fixpoint sintp_gen).

(** [sintp] satisfies [sintpy] *)
#[export] Instance sintp_sintpy {ITI} : sintpy ITI True₁ sintp.
Proof. split.
  eexists _. split; [done|]=>/=. iIntros (?) "big".
  rewrite least_fixpoint_unfold. iIntros (??) "#A #B".
  iApply "big"; [done..| |]; iIntros "!> % ?/="; by [iApply "A"|iApply "B"].
Qed.

(** [sintp] is sound w.r.t. the interpretation under [sintp] *)
Lemma sintp_sound {ITI i} : ⊢ ssound (ITI:=ITI) sintp i.
Proof.
  elim: {i}(wft_lt_wf i)=> i _ IH. iIntros (P) "/= X".
  have: (Sarg i P).(sarg_idx) = i by done.
  move: {P}(Sarg i P : sintp_aty _)=> iP eq. iRevert (eq). iRevert (iP) "X".
  iApply least_fixpoint_ind. iIntros "!>" ([??]) "/= X ->".
  iApply ("X" $! _ sintp_sintpy); iIntros "!> % /=".
  { iIntros "[X _]". by iApply "X". } { iIntros "[_ $]". }
  { iIntros (?). by iApply IH. }
Qed.
