(** * Derivability *)

From nola.util Require Export intp psg.
From nola.iris Require Export order.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
Import PintpNotation.

(** ** Derivability *)

(** [judg]: Judgment with the parameterized interpretation *)
#[projections(primitive)]
Structure judg (PROP : bi) : Type := Judg {
  judg_car :> Type;
  (** Interpretation parameterized over derivability candidates *)
  #[canonical=no] judg_Pintp :: Pintp (judg_car → PROP) judg_car PROP;
}.
Arguments judg_car {PROP JUDG} : rename.
Arguments judg_Pintp {PROP JUDG} : rename.

Section deriv.
  Context {PROP} {JUDG : judg PROP}.
  Implicit Type (J : JUDG) (δ : JUDG → PROP) (ih : (JUDG → PROP) → Prop).

  (** ** [Deriv ih δ] : [δ] is a good derivability predicate

    [ih] is the inductive hypothesis, used for parameterized induction *)
  Definition Deriv ih δ := Psgoidp (OT:=JUDG → PROP) pintp ih δ.
  Existing Class Deriv.

  (** [Deriv] is monotone over the inductive hypothesis *)
  Lemma Deriv_mono `{!Deriv ih δ} (ih' : _ → Prop) :
    (∀ δ', ih δ' → ih' δ') → Deriv ih' δ.
  Proof. move=> to. move: Deriv0. by apply Psgoidp_mono. Qed.

  (** Parameterized induction principle for [Deriv] *)
  Lemma Deriv_ind `{!Deriv ih' δ} ih :
    Deriv (λ δ', ih δ' ∧ ih' δ') ⊑ ih → ih δ.
  Proof. by apply Psgoidp_ind. Qed.

  (** Get the derivability [δ J] by the interpretaion *)
  Lemma Deriv_to `{!Deriv ih δ} {J} :
    ((* Take any good derivability predicate [δ'] *) ∀ δ', ⌜Deriv ih δ'⌝ →
      (* Can use the inductive hypothesis *) ⌜ih δ'⌝ →
      (* Can turn [δ] into the semantics at [δ'] *) ⌜∀ J, δ J ⊢ ⟦ J ⟧(δ')⌝ →
      (* The semantics at [δ'] *) ⟦ J ⟧(δ'))
    ⊢ (* The derivability at [δ] *) δ J.
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

  (** Map derivabilities via semantics *)
  Lemma Deriv_map `{!Deriv ih δ} {J J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ')) ⊢
    δ J -∗ δ J'.
  Proof.
    iIntros "∀ J". iApply Deriv_to. iIntros (??? to).
    iApply "∀"; by [| |iApply to].
  Qed.
  Lemma Deriv_map2 `{!Deriv ih δ} {J J' J''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ')) ⊢
    δ J -∗ δ J' -∗ δ J''.
  Proof.
    iIntros "∀ J J'". iApply Deriv_to. iIntros (??? to).
    iApply ("∀" with "[//] [//] [J]"); by iApply to.
  Qed.
  Lemma Deriv_map3 `{!Deriv ih δ} {J J' J'' J'''} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗ ⟦ J'' ⟧(δ') -∗
      ⟦ J''' ⟧(δ')) ⊢
    δ J -∗ δ J' -∗ δ J'' -∗ δ J'''.
  Proof.
    iIntros "∀ J J' J''". iApply Deriv_to. iIntros (??? to).
    iApply ("∀" with "[//] [//] [J] [J']"); by iApply to.
  Qed.
  Lemma Deriv_mapl `{!Deriv ih δ} {Js J'} :
    (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ →
      ([∗ list] J ∈ Js, ⟦ J ⟧(δ')) -∗ ⟦ J' ⟧(δ')) ⊢
    ([∗ list] J ∈ Js, δ J) -∗ δ J'.
  Proof.
    iIntros "∀ Js". iApply Deriv_to. iIntros (??? to). iApply "∀"; [done..|].
    iStopProof. elim: Js; [done|]=>/= ?? IH. iIntros "[J ?]".
    iSplitL "J"; by [iApply to|iApply IH].
  Qed.

  (** ** [der]: The best derivability predicate *)
  Definition der : JUDG → PROP := psg (OT:=JUDG → PROP) pintp.

  (** [der] satisfies [Deriv] *)
  #[export] Instance der_Deriv : Deriv (λ _, True) der.
  Proof. apply Psgoidp_Psgoid, psg_Psgoid. Qed.

  (** [der] is sound w.r.t. the semantics at [der] *)
  Lemma der_sound {J} : der J ⊢ ⟦ J ⟧(der).
  Proof. move: J. exact (psg_post (OT:=JUDG → PROP)). Qed.
End deriv.

(** ** Derivability-parameterized interpretation *)
Class Dintp (JUD : Type) (A : ofe) (PROP : bi) := DINTP {
  dintp :: Pintp (JUD → PROP) A PROP;
  dintp_ne {δ} :: NonExpansive (dintp δ);
}.
Hint Mode Dintp - ! - : typeclass_instances.
