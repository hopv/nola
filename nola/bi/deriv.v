(** * Magic derivability *)

From nola.util Require Export psg.
From nola.bi Require Export order.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

(** ** [Dsem]: Semantics parameterized over derivability candidates *)
#[projections(primitive)]
Record Dsem (JUDG : ofe) (A : ofe) (PROP : bi) : Type := DSEM {
  dsem :> (JUDG -n> PROP) → A → PROP;
  dsem_ne {δ} :: NonExpansive (dsem δ);
}.
Existing Class Dsem.
Add Printing Constructor Dsem.
Hint Mode Dsem - ! - : typeclass_instances.
Arguments DSEM {_ _ _} _ _.
Arguments dsem {_ _ _ _} _ _ /. Arguments dsem_ne {_ _ _ _}.

Module DsemNotation'.
  Notation "⟦ ⟧( δ )" := (dsem δ) (format "⟦ ⟧( δ )").
  Notation "⟦ a ⟧( δ )" := (dsem δ a) (format "⟦  '[' a  ']' ⟧( δ )").
End DsemNotation'.
Import DsemNotation'.

#[export] Instance dsem_proper `{!Dsem JUDG A PROP} {δ} :
  Proper ((≡) ==> (⊣⊢)) (@dsem JUDG A PROP _ δ).
Proof. apply ne_proper, _. Qed.

(** Judgment semantics *)
Notation Jsem JUDG PROP := (Dsem JUDG JUDG PROP).

(** [dinto δ δ']: [δ] can be turned into the semantics at [δ'] *)
Notation dinto δ δ' := (∀ J, δ J ⊢ ⟦ J ⟧(δ')) (only parsing).

Section deriv.
  Context `{!Jsem JUDG PROP}.
  Implicit Type (J : JUDG) (δ : JUDG -n> PROP) (ih : (JUDG -n> PROP) → Prop).

  (** ** [Deriv ih δ] : [δ] is a good derivability predicate

    [ih] is the inductive hypothesis, used for parameterized induction *)
  Definition Deriv := Psgoidp (OT:=JUDG -n> PROP) (λ δ, OfeMor (dsem δ)).
  Existing Class Deriv.

  (** [Deriv] is monotone over the inductive hypothesis *)
  Lemma Deriv_mono `{!Deriv ih δ} (ih' : _ → Prop) :
    (∀ δ', ih δ' → ih' δ') → Deriv ih' δ.
  Proof. move=> to. move: Deriv0. exact: Psgoidp_mono. Qed.

  (** Parameterized induction principle for [Deriv] *)
  Lemma Deriv_ind `{!Deriv ih' δ} ih : Deriv (λ δ', ih δ' ∧ ih' δ') ⊑ ih → ih δ.
  Proof. exact: Psgoidp_ind. Qed.

  (** Factorize the derivability [δ J] by semantics *)
  Lemma Deriv_factor' `{!Deriv ih δ} {J} :
    ((* Take any good derivability predicate [δ'] *) ∀ δ', ⌜Deriv ih δ'⌝ →
      (* Can use the inductive hypothesis *) ⌜ih δ'⌝ →
      (* Can turn [δ] into the semantics at [δ'] *) ⌜dinto δ δ'⌝ →
      (* The semantics at [δ'] *) ⟦ J ⟧(δ')) ⊢
      (* The derivability at [δ] *) δ J.
  Proof.
    iIntros "to". iApply (Psgoidp_factor' Deriv0). iIntros (?[?[??]]).
    by iApply "to".
  Qed.
  Lemma Deriv_factor `{!Deriv ih δ} {J} :
    δ J ⊣⊢ ∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ J ⟧(δ').
  Proof.
    iSplit; iIntros "?"; [|iStopProof; exact:  Deriv_factor'].
    by iIntros (??? ->).
  Qed.
  Lemma Deriv_factor_all `{!Deriv ih δ} {J} :
    δ J ⊣⊢ ∀ δ' (_ : Deriv ih δ') (_ : ih δ') (_ : dinto δ δ'), ⟦ J ⟧(δ').
  Proof.
    rewrite Deriv_factor. repeat (do 2 f_equiv; rewrite bi.pure_impl_forall).
  Qed.

  (** Map derivabilities via semantics *)
  Lemma Deriv_map `{!Deriv ih δ} {J J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ')) ⊢
      δ J -∗ δ J'.
  Proof.
    iIntros "∀ J". iApply Deriv_factor. iIntros (??? to). rewrite to.
    by iApply "∀".
  Qed.
  Lemma Deriv_map2 `{!Deriv ih δ} {J J' J''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ')) ⊢
      δ J -∗ δ J' -∗ δ J''.
  Proof.
    iIntros "∀ J J'". iApply Deriv_factor. iIntros (??? to). rewrite !to.
    iApply ("∀" with "[//] [//] [//] J J'").
  Qed.
  Lemma Deriv_map3 `{!Deriv ih δ} {J J' J'' J'''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ') -∗ ⟦ J''' ⟧(δ')) ⊢
      δ J -∗ δ J' -∗ δ J'' -∗ δ J'''.
  Proof.
    iIntros "∀ J J' J''". iApply Deriv_factor. iIntros (??? to). rewrite !to.
    iApply ("∀" with "[//] [//] [//] J J' J''").
  Qed.
  Lemma Deriv_mapl `{!Deriv ih δ} {Js J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ([∗ list] J ∈ Js, ⟦ J ⟧(δ')) -∗ ⟦ J' ⟧(δ')) ⊢
      ([∗ list] J ∈ Js, δ J) -∗ δ J'.
  Proof.
    iIntros "∀ Js". iApply Deriv_factor. iIntros (??? to).
    iApply "∀"; [done..|]. iStopProof. elim: Js; [done|]=>/= ?? ->.
    by rewrite to.
  Qed.
  Lemma Deriv_all `{!Deriv ih δ} {A Jf J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      (∀ a : A, ⟦ Jf a ⟧(δ')) -∗ ⟦ J' ⟧(δ')) ⊢
      (∀ a, δ (Jf a)) -∗ δ J'.
  Proof.
    iIntros "∀ Jf". iApply Deriv_factor. iIntros (????). iApply "∀"; [done..|].
    iStopProof. by do 2 f_equiv.
  Qed.

  (** Derivability preserves persistence *)
  #[export] Instance Deriv_persistent `{!Deriv ih δ, BiPersistentlyForall PROP}
    `{Sem : ∀ δ', Deriv ih δ' → ih δ' → dinto δ δ' → Persistent ⟦ J ⟧(δ')} :
    Persistent (δ J).
  Proof.
    rewrite Deriv_factor_all. repeat apply bi.forall_persistent=> ?. exact: Sem.
  Qed.

  (** Derivability preserves timelessness *)
  #[export] Instance Deriv_timeless `{!Deriv ih δ}
    `{Sem : ∀ δ', Deriv ih δ' → ih δ' → dinto δ δ' → Timeless ⟦ J ⟧(δ')} :
    Timeless (δ J).
  Proof.
    rewrite Deriv_factor_all. repeat apply bi.forall_timeless=> ?. exact: Sem.
  Qed.

  (** ** [der]: The best derivability predicate *)
  Definition der : JUDG -n> PROP :=
    psg (OT:=JUDG -n> PROP) (λ δ, OfeMor (dsem δ)).

  (** [der] satisfies [Deriv] *)
  #[export] Instance der_Deriv : Deriv (λ _, True) der.
  Proof. apply Psgoidp_Psgoid, psg_Psgoid. Qed.

  (** [der] is sound w.r.t. the semantics at [der] *)
  Lemma der_sound {J} : der J ⊢ ⟦ J ⟧(der).
  Proof. move: J. exact (psg_post (OT:=JUDG -n> PROP)). Qed.
End deriv.

Module DsemNotation.
  Export DsemNotation'.
  Notation "⟦ ⟧" := (⟦⟧(der)) (format "⟦ ⟧").
  Notation "⟦ a ⟧" := (⟦ a ⟧(der)) (format "⟦  '[' a  ']' ⟧").
End DsemNotation.

(** ** [inJ]: Judgment inclusion *)
Record inJ (JUDG' JUDG : ofe) : Type := IN_J {
  in_j :> JUDG' → JUDG;
  in_j_ne :: NonExpansive in_j;
}.
Existing Class inJ.
Add Printing Constructor inJ.
Arguments IN_J {_ _} _ _.
Arguments in_j {_ _ inj} : rename. Arguments in_j_ne {_ _ inj} : rename.
Hint Mode inJ ! - : typeclass_instances.

(** Judgment inclusion into [sigT] *)
Definition sigT_inJ {A} {JUDGf : A → ofe} {a} : inJ (JUDGf a) (sigTO JUDGf) :=
  IN_J (existT a) _.

(** ** [inJS]: Judgment semantics inclusion *)
Class inJS (JUDG' JUDG : ofe) PROP
  `{!inJ JUDG' JUDG, !Dsem JUDG JUDG' PROP, !Jsem JUDG PROP} : Prop :=
  in_js : ∀ {δ J}, ⟦ @in_j JUDG' JUDG _ J ⟧(δ) = ⟦ J ⟧(δ).
Hint Mode inJS ! - - - - - : typeclass_instances.

(** Semantics over [sigT] *)
Program Definition sigT_dsem {A} (F : A → ofe) {PROP JUDG}
  `{!∀ a, Dsem JUDG (F a) PROP} : Dsem JUDG (sigT F) PROP :=
  DSEM (λ δ s, ⟦ projT2 s ⟧(δ)) _.
Next Obligation. move=> > [??][??][/=?]. subst=>/=. solve_proper. Qed.

(** Judgment semantics inclusion into [sigT] *)
Lemma sigT_inJS {A} {JUDGf : A → ofe} {PROP}
  (dsemf : ∀ a, Dsem (sigT JUDGf) (JUDGf a) PROP) {a} :
  inJS (JUDGf a) (sigTO JUDGf) PROP (inJ0:=sigT_inJ) (Jsem0:=sigT_dsem JUDGf).
Proof. done. Qed.
