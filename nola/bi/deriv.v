(** * Derivability *)

From nola.util Require Export intp psg.
From nola.bi Require Export order.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
Import PintpNotation.

(** ** [Dintp]: Interpretation parameterized over derivability candidates *)
Class Dintp (JUDG : ofe) (A : ofe) (PROP : bi) := DINTP {
  dintp :: Pintp (JUDG → PROP) A PROP;
  dintp_ne `{!NonExpansive δ} :: NonExpansive (dintp δ);
}.
Add Printing Constructor Dintp.
Hint Mode Dintp - ! - : typeclass_instances.
Arguments DINTP {_ _ _} _ {_}.

(** ** [judgi]: Judgment with the parameterized interpretation *)
#[projections(primitive)]
Structure judgi (PROP : bi) : Type := Judgi {
  judgi_car :> ofe;
  (** Interpretation parameterized over derivability candidates *)
  #[canonical=no] judgi_Dintp :: Dintp judgi_car judgi_car PROP;
}.
Add Printing Constructor judgi.
Arguments Judgi {_} _ {_}.
Arguments judgi_car {PROP JUDGI} : rename.
Arguments judgi_Dintp {PROP JUDGI} : rename.

Section deriv.
  Context {PROP} {JUDGI : judgi PROP}.
  Implicit Type (J : JUDGI) (δ : JUDGI → PROP) (ih : (JUDGI → PROP) → Prop).

  (** ** [Deriv ih δ] : [δ] is a good derivability predicate

    [ih] is the inductive hypothesis, used for parameterized induction *)
  Definition Deriv ih δ := Psgoidp (OT:=JUDGI → PROP) pintp ih δ.
  Existing Class Deriv.

  (** [Deriv] is monotone over the inductive hypothesis *)
  Lemma Deriv_mono `{!Deriv ih δ} (ih' : _ → Prop) :
    (∀ δ', ih δ' → ih' δ') → Deriv ih' δ.
  Proof. move=> to. move: Deriv0. by apply Psgoidp_mono. Qed.

  (** Parameterized induction principle for [Deriv] *)
  Lemma Deriv_ind `{!Deriv ih' δ} ih : Deriv (λ δ', ih δ' ∧ ih' δ') ⊑ ih → ih δ.
  Proof. by apply Psgoidp_ind. Qed.

  (** Get the derivability [δ J] by the interpretaion *)
  Lemma Deriv_to `{!Deriv ih δ} {J} :
    ((* Take any good derivability predicate [δ'] *) ∀ δ', ⌜Deriv ih δ'⌝ →
      (* Can use the inductive hypothesis *) ⌜ih δ'⌝ →
      (* Can turn [δ] into the semantics at [δ'] *) ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      (* The semantics at [δ'] *) ⟦ J ⟧(δ')) ⊢
      (* The derivability at [δ] *) δ J.
  Proof.
    iIntros "to". iApply (Psgoidp_le Deriv0). iIntros (?[?[??]]).
    by iApply "to".
  Qed.
  Lemma Deriv_eqv `{!Deriv ih δ} {J} :
    δ J ⊣⊢ ∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ → ⟦ J ⟧(δ').
  Proof.
    iSplit; iIntros "?"; iStopProof; [|by exact Deriv_to]. iIntros "?" (????).
    by iStopProof.
  Qed.
  Lemma Deriv_eqv' `{!Deriv ih δ} {J} :
    δ J ⊣⊢
      ∀ δ' (_ : Deriv ih δ') (_ : ih δ'), ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ → ⟦ J ⟧(δ').
  Proof.
    rewrite Deriv_eqv. do 2 f_equiv. rewrite bi.pure_impl_forall.
    do 2 f_equiv. exact: bi.pure_impl_forall.
  Qed.

  (** [Deriv ih δ] implies that [δ] is non-expansive *)
  #[export] Instance Deriv_to_ne `{!Deriv ih δ} : NonExpansive δ.
  Proof.
    apply Deriv_ind=> ??????. rewrite !Deriv_eqv'. do 5 f_equiv. move=> [??].
    solve_proper.
  Qed.

  (** Map derivabilities via semantics *)
  Lemma Deriv_map `{!Deriv ih δ} {J J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ')) ⊢
      δ J -∗ δ J'.
  Proof.
    iIntros "∀ J". iApply Deriv_to. iIntros (??? to). rewrite to. by iApply "∀".
  Qed.
  Lemma Deriv_map2 `{!Deriv ih δ} {J J' J''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ')) ⊢
      δ J -∗ δ J' -∗ δ J''.
  Proof.
    iIntros "∀ J J'". iApply Deriv_to. iIntros (??? to). rewrite !to.
    iApply ("∀" with "[//] [//] [//] J J'").
  Qed.
  Lemma Deriv_map3 `{!Deriv ih δ} {J J' J'' J'''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ') -∗ ⟦ J''' ⟧(δ')) ⊢
      δ J -∗ δ J' -∗ δ J'' -∗ δ J'''.
  Proof.
    iIntros "∀ J J' J''". iApply Deriv_to. iIntros (??? to). rewrite !to.
    iApply ("∀" with "[//] [//] [//] J J' J''").
  Qed.
  Lemma Deriv_mapl `{!Deriv ih δ} {Js J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      ([∗ list] J ∈ Js, ⟦ J ⟧(δ')) -∗ ⟦ J' ⟧(δ')) ⊢
      ([∗ list] J ∈ Js, δ J) -∗ δ J'.
  Proof.
    iIntros "∀ Js". iApply Deriv_to. iIntros (??? to). iApply "∀"; [done..|].
    iStopProof. elim: Js; [done|]=>/= ?? ->. by rewrite to.
  Qed.

  (** ** [der]: The best derivability predicate *)
  Definition der : JUDGI → PROP := psg (OT:=JUDGI → PROP) pintp.

  (** [Intp] with [der] for [Dintp] *)
  #[export] Instance Dintp_Intp `{!Dintp (JUDGI : judgi PROP) A PROP} :
    Intp A PROP := ⟦⟧(der).

  (** [der] satisfies [Deriv] *)
  #[export] Instance der_Deriv : Deriv (λ _, True) der.
  Proof. apply Psgoidp_Psgoid, psg_Psgoid. Qed.

  (** [der] is sound w.r.t. the semantics at [der] *)
  Lemma der_sound {J} : der J ⊢ ⟦ J ⟧(der).
  Proof. move: J. exact (psg_post (OT:=JUDGI → PROP)). Qed.
End deriv.
