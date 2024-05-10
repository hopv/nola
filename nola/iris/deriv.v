(** * Derivability *)

From nola.util Require Export intp.
From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import proofmode.
Import PintpNotation.

(** ** Preliminaries *)

(** [dwrap]: Wrapper for a derivability *)

#[projections(primitive)]
Record dwrap (A : Type) := Dwrap { dunwrap : A }.
Arguments Dwrap {_} _.
Arguments dunwrap {_} _.
Add Printing Constructor dwrap.

(** Notation for derivability *)
Module DerivNotation.
  Notation "⸨ J ⸩( δ )" := (dunwrap δ J) (format "⸨  '[' J  ']' ⸩( δ )")
    : nola_scope.
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

(** Type for a derivability predicate *)
Notation deriv JUD PROP := (dwrap (JUD -d> PROP)).

(** [judg]: Judgment with the parameterized interpretation *)
#[projections(primitive)]
Structure judg (PROP : bi) : Type := Judg {
  judg_car :> Type;
  (** Interpretation parameterized over derivability candidates *)
  #[canonical=no] judg_Pintp :: Pintp (deriv judg_car PROP) judg_car PROP;
}.
Arguments judg_car {PROP JUDG} : rename.
Arguments judg_Pintp {PROP JUDG} : rename.

Section deriv.
  Context {PROP : bi} {JUDG : judg PROP}.
  Implicit Type (δ : deriv JUDG PROP) (ih : deriv JUDG PROP → Prop).

  (** Soundness of a derivability [δ] with respect to the semantics at [δ'] *)
  Definition dsound δ δ' : PROP := ∀ J, ⸨ J ⸩(δ) -∗ ⟦ J ⟧(δ').
  Definition dtrans δ δ' : PROP := ∀ J, ⸨ J ⸩(δ) -∗ ⸨ J ⸩(δ').

  (** ** [Deriv ih δ] : [δ] is a good derivability predicate

    [ih] is the inductive hypothesis, used for parameterized induction *)

  Inductive Deriv ih δ : Prop := {
    (** For [Deriv_intp] *)
    Deriv_byintp' :
      (* Parameterization by [Deriv'] is for strict positivity *)
      ∃ Deriv' : _ → Prop, (∀ δ', Deriv' δ' → Deriv ih δ') ∧ ∀ J,
        (∀ δ', ⌜Deriv' δ'⌝ → ⌜ih δ'⌝ →
          □ dsound δ δ' -∗ □ dtrans δ δ' -∗ ⟦ J ⟧(δ')) -∗ ⸨ J ⸩(δ)
  }.
  Existing Class Deriv.

  (** Get the derivability [⸨ J ⸩(δ)] by the interpretaion *)
  Lemma Deriv_byintp `{!Deriv ih δ} {J} :
    ((* Take any good derivability predicate [δ'] *) ∀ δ', ⌜Deriv ih δ'⌝ →
      (* Can use the inductive hypothesis *) ⌜ih δ'⌝ →
      (* Can turn [δ] into the semantics at [δ'] *)
        □ dsound δ δ' -∗
      (* Can turn [δ] into [δ'] *) □ dtrans δ δ' -∗
      (* The semantics at [δ'] *) ⟦ J ⟧(δ'))
    -∗ (* The derivability at [δ] *) ⸨ J ⸩(δ).
  Proof.
    have X := Deriv_byintp' ih δ. move: X=> [dy[dyto byintp]]. iIntros "→".
    iApply byintp. iIntros (δ' dyd'). apply dyto in dyd'. by iApply "→".
  Qed.

  (** [Deriv] is monotone over the inductive hypothesis *)
  Lemma Deriv_mono `{D : !Deriv ih δ} (ih' : _ → Prop) :
    (∀ δ', ih δ' → ih' δ') → Deriv ih' δ.
  Proof.
    move=> ihto. move: δ D. fix FIX 2=> δ [[dy[dyto byintp]]]. split.
    exists (Deriv ih'). split; [done|]=>/= ?. iIntros "big". iApply byintp.
    iIntros (???). iApply "big"; iPureIntro; by [apply FIX, dyto|apply ihto].
  Qed.

  (** [Deriv] can accumulate the inductive hypothesis *)
  Lemma Deriv_acc res {ih δ} :
    (∀ δ', Deriv (λ δ', res δ' ∧ ih δ') δ' → res δ') → Deriv ih δ → res δ.
  Proof.
    move=> to dyd. apply to. move: δ dyd. fix FIX 2=> δ [[dy[dyto byintp]]].
    split. exists (Deriv (λ δ, res δ ∧ ih δ)). split; [done|]=>/= ?.
    iIntros "big". iApply byintp. iIntros (? dyd' ?). move: dyd'=>/dyto/FIX ?.
    iApply "big"; iPureIntro; [done|]. split; by [apply to|].
  Qed.

  (** Introduce a derivability via semantics *)
  Lemma Deriv_intro `{!Deriv ih δ} {J} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ')) ⊢ ⸨ J ⸩(δ).
  Proof.
    iIntros "∀". iApply Deriv_byintp. iIntros (???) "_ _". by iApply "∀".
  Qed.

  (** Map derivabilities via semantics *)
  Lemma Deriv_map `{!Deriv ih δ} {J J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ')) -∗
    ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ).
  Proof.
    iIntros "∀ J". iApply Deriv_byintp. iIntros (???) "#→ _".
    iApply "∀"; by [| |iApply "→"].
  Qed.
  Lemma Deriv_map2 `{!Deriv ih δ} {J J' J''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗
      ⟦ J'' ⟧(δ')) -∗
    ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ) -∗ ⸨ J'' ⸩(δ).
  Proof.
    iIntros "∀ J J'". iApply Deriv_byintp. iIntros (???) "#→ _".
    iApply ("∀" with "[//] [//] [J]"); by iApply "→".
  Qed.
  Lemma Deriv_map3 `{!Deriv ih δ} {J J' J'' J'''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗
      ⟦ J'' ⟧(δ') -∗ ⟦ J''' ⟧(δ')) -∗
    ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ) -∗ ⸨ J'' ⸩(δ) -∗ ⸨ J''' ⸩(δ).
  Proof.
    iIntros "∀ J J' J''". iApply Deriv_byintp. iIntros (???) "#→ _".
    iApply ("∀" with "[//] [//] [J] [J']"); by iApply "→".
  Qed.
  Lemma Deriv_mapl `{!Deriv ih δ} {Js J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      ([∗ list] J ∈ Js, ⟦ J ⟧(δ')) -∗ ⟦ J' ⟧(δ')) -∗
    ([∗ list] J ∈ Js, ⸨ J ⸩(δ)) -∗ ⸨ J' ⸩(δ).
  Proof.
    iIntros "∀ Js". iApply Deriv_byintp. iIntros (???) "#→ _".
    iApply "∀"; [done..|]. iInduction Js as [|J Js] "IH"=>/=; [done|].
    iDestruct "Js" as "[J Js]". iSplitL "J"; by [iApply "→"|iApply "IH"].
  Qed.

  (** ** [der]: The best derivability predicate *)

  (** [der_gen]: What becomes [der] by taking [bi_least_fixpoint] *)
  Definition der_gen (self : JUDG → PROP) : JUDG → PROP := λ J,
    (∀ δ, ⌜Deriv (λ _, True) δ⌝ → □ dsound (Dwrap self) δ -∗
      □ dtrans (Dwrap self) δ -∗ ⟦ J ⟧(δ))%I.
  #[export] Instance der_gen_mono : BiMonoPred (A:=leibnizO _) der_gen.
  Proof.
    split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" (?) "big".
    iIntros (??) "#Ψδ #Ψδ'".
    iApply "big"; [done|..]; iIntros "!> % ?"; [iApply "Ψδ"|iApply "Ψδ'"];
      by iApply "ΦΨ".
  Qed.

  (** [der]: The best derivability predicate *)
  Definition der_def : deriv JUDG PROP :=
    Dwrap (bi_least_fixpoint (A:=leibnizO _) der_gen).
  Lemma der_aux : seal (@der_def). Proof. by eexists. Qed.
  Definition der := der_aux.(unseal).
  Lemma der_unseal : der = der_def. Proof. exact: seal_eq. Qed.

  (** [der] satisfies [Deriv] *)
  #[export] Instance der_Deriv : Deriv (λ _, True) der.
  Proof.
    rewrite der_unseal. split. eexists _. split; [done|]=>/=. iIntros (?) "big".
    rewrite least_fixpoint_unfold. iIntros (??) "#→δ #→δ'".
    iApply "big"; [done..| |]; iIntros "!> % ?/="; by [iApply "→δ"|iApply "→δ'"].
  Qed.

  (** [der] is sound w.r.t. the interpretation under [der] *)
  Lemma der_sound : ⊢ dsound der der.
  Proof.
    rewrite der_unseal. iApply (least_fixpoint_ind (A:=leibnizO _)).
    iIntros "!> % gen". rewrite -der_unseal.
    iApply ("gen" $! _ der_Deriv); iIntros "!> % /="; rewrite der_unseal.
    { iIntros "[$ _]". } { iIntros "[_ $]". }
  Qed.
End deriv.

(** ** Derivability-parameterized interpretation *)
Class Dintp (JUD : Type) (A : ofe) (PROP : bi) := DINTP {
  dintp :: Pintp (deriv JUD PROP) A PROP;
  dintp_ne {δ} :: NonExpansive (dintp δ);
}.
Hint Mode Dintp - ! - : typeclass_instances.
