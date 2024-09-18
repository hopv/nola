(** * Derivability *)

From nola.util Require Export sem psg.
From nola.bi Require Export order.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
Import PsemNotation.

(** ** [Dsem]: Semantics parameterized over derivability candidates *)
Class Dsem (JUDG : ofe) (A : ofe) (PROP : bi) := DSEM {
  dsem :: Psem (JUDG → PROP) A PROP;
  dsem_ne `{!NonExpansive δ} :: NonExpansive (dsem δ);
}.
Add Printing Constructor Dsem.
Hint Mode Dsem - ! - : typeclass_instances.
Arguments DSEM {_ _ _} _ {_}.

#[export] Instance dsem_proper `{!Dsem JUDG A PROP, !NonExpansive δ} :
  Proper ((≡) ==> (⊣⊢)) (@dsem JUDG A PROP _ δ).
Proof. apply ne_proper, _. Qed.

(** ** [judgi]: Judgment with the parameterized semantics *)
#[projections(primitive)]
Structure judgi (PROP : bi) : Type := Judgi {
  judgi_car :> ofe;
  (** Semantics parameterized over derivability candidates *)
  #[canonical=no] judgi_Dsem :: Dsem judgi_car judgi_car PROP;
}.
Add Printing Constructor judgi.
Arguments Judgi {_} _ {_}.
Arguments judgi_car {PROP JUDGI} : rename.
Arguments judgi_Dsem {PROP JUDGI} : rename.

(** [dinto δ δ']: [δ] can be turned into the semantics at [δ'] *)
Notation dinto δ δ' := (∀ J, δ J ⊢ ⟦ J ⟧(δ')) (only parsing).

Section deriv.
  Context {PROP} {JUDGI : judgi PROP}.
  Implicit Type (J : JUDGI) (δ : JUDGI → PROP) (ih : (JUDGI → PROP) → Prop).

  (** ** [Deriv ih δ] : [δ] is a good derivability predicate

    [ih] is the inductive hypothesis, used for parameterized induction *)
  Definition Deriv ih δ := Psgoidp (OT:=JUDGI → PROP) psem ih δ.
  Existing Class Deriv.

  (** [Deriv] is monotone over the inductive hypothesis *)
  Lemma Deriv_mono `{!Deriv ih δ} (ih' : _ → Prop) :
    (∀ δ', ih δ' → ih' δ') → Deriv ih' δ.
  Proof. move=> to. move: Deriv0. by apply Psgoidp_mono. Qed.

  (** Parameterized induction principle for [Deriv] *)
  Lemma Deriv_ind `{!Deriv ih' δ} ih : Deriv (λ δ', ih δ' ∧ ih' δ') ⊑ ih → ih δ.
  Proof. by apply Psgoidp_ind. Qed.

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
    iSplit; iIntros "?"; [|iStopProof; by exact Deriv_factor'].
    by iIntros (??? ->).
  Qed.
  Lemma Deriv_factor_all `{!Deriv ih δ} {J} :
    δ J ⊣⊢ ∀ δ' (_ : Deriv ih δ') (_ : ih δ') (_ : dinto δ δ'), ⟦ J ⟧(δ').
  Proof.
    rewrite Deriv_factor. repeat (do 2 f_equiv; rewrite bi.pure_impl_forall).
  Qed.

  (** [Deriv ih δ] implies that [δ] is non-expansive *)
  #[export] Instance Deriv_to_ne `{!Deriv ih δ} : NonExpansive δ.
  Proof.
    apply Deriv_ind=> ??????. rewrite !Deriv_factor_all. do 5 f_equiv.
    move=> [??]. solve_proper.
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
  Definition der : JUDGI → PROP := psg (OT:=JUDGI → PROP) psem.

  (** [Sem] with [der] for [Dsem] *)
  #[export] Instance Dsem_Sem `{!Dsem (JUDGI : judgi PROP) A PROP} : Sem A PROP
    := ⟦⟧(der).

  (** [der] satisfies [Deriv] *)
  #[export] Instance der_Deriv : Deriv (λ _, True) der.
  Proof. apply Psgoidp_Psgoid, psg_Psgoid. Qed.

  (** [der] is sound w.r.t. the semantics at [der] *)
  Lemma der_sound {J} : der J ⊢ ⟦ J ⟧(der).
  Proof. move: J. exact (psg_post (OT:=JUDGI → PROP)). Qed.
End deriv.
