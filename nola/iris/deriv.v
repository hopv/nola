(** * [deriv]: Derivability *)

From nola.util Require Export pred.
From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import proofmode.

(** ** Preliminaries *)

(** [dwrap]: Wrapper for a derivability candidate *)

#[projections(primitive)]
Record dwrap (A : Type) := Dwrap { dunwrap : A }.
Arguments Dwrap {_} _.
Arguments dunwrap {_} _.
Add Printing Constructor dwrap.

(** Notation for [dwrap] *)
Module DerivNotation'.
  Notation "⸨ J ⸩ ( δ )" := (dunwrap δ J)
    (format "'[' ⸨  J  ⸩ '/  ' ( δ ) ']'") : nola_scope.
End DerivNotation'.
Import DerivNotation'.

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
Structure derivs : Type := Derivs {
  (** Data type *)
  derivs_car :> Type;
  (** BI logic for interpretation *)
  #[canonical=no] derivs_bi : bi;
}.
Add Printing Constructor derivs.
Implicit Type D : derivs.

(** Type for derivability *)
Definition deriv_ty' (D : derivs) : Type := D -d> D.(derivs_bi).
Notation deriv_ty D := (dwrap (deriv_ty' D)).

(** [derivsi]: [derivs] with interpretation *)
Structure derivsi : Type := Derivsi {
  derivsi_derivs :> derivs;
  (** Interpretation parameterized over derivability candidates *)
  #[canonical=no] derivsi_intp :
    deriv_ty derivsi_derivs → deriv_ty' derivsi_derivs;
}.
Arguments derivsi_intp {D} : rename.
Implicit Type DI : derivsi.

(** Notation for [derivs_intp] *)
Notation derivsi_intp' δ := (Dwrap (derivsi_intp δ)).
Module IntpNotation.
  Notation "⟦ J ⟧ ( δ )" := (derivsi_intp δ J)
    (format "'[' ⟦  J  ⟧ '/  ' ( δ ) ']'") : nola_scope.
End IntpNotation.
Import IntpNotation.

(** Conversion between candidates [δ], [δ'] *)
Definition dtrans {D} (δ δ' : deriv_ty D) : D.(derivs_bi) :=
  ∀ J, ⸨ J ⸩(δ) -∗ ⸨ J ⸩(δ').
#[export] Instance dtrans_ne {D} : NonExpansive2 (dtrans (D:=D)).
Proof.
  unfold dtrans=> ??? seq ?? δ'eq. do 3 f_equiv; [apply seq|apply δ'eq].
Qed.

(** Soundness of a candidate [δ] with respect the semantics by [δ'] *)
Definition dsound {DI} (δ δ' : deriv_ty DI) : DI.(derivs_bi) :=
  ∀ J, ⸨ J ⸩(δ) -∗ ⟦ J ⟧(δ').

(** ** [Deriv] : Derivability candidate *)

Inductive Deriv DI (ih : deriv_ty DI → Prop) (δ : deriv_ty DI) : Prop := {
  (** For [Deriv_intp] *)
  Deriv_byintp' :
    (* Parameterization by [Deriv'] is for strict positivity *)
    ∃ Deriv' : _ → Prop, (∀ δ', Deriv' δ' → Deriv DI ih δ') ∧ ∀ J,
      (∀ δ', ⌜Deriv' δ'⌝ → ⌜ih δ'⌝ →
        □ dsound δ δ' -∗ □ dtrans δ δ' -∗ ⟦ J ⟧(δ')) -∗ ⸨ J ⸩(δ)
}.
Existing Class Deriv.

(** Get the candidate [⸨ J ⸩(δ)] by the interpretaion *)
Lemma Deriv_byintp `{!Deriv DI ih δ} {J} :
  (∀ δ', (* Take any candidate [δ'] *) ⌜Deriv DI ih δ'⌝ →
    (* Get access to the inductive hypothesis *) ⌜ih δ'⌝ →
    (* Turn the base candidate into the sematics by the given candidate *)
      □ dsound δ δ' -∗
    (* Turn the base candidate into the given candidate *) □ dtrans δ δ' -∗
    (* The semantics by the given candidate *) ⟦ J ⟧(δ'))
  -∗ (* The base candidate *) ⸨ J ⸩(δ).
Proof.
  have X := (@Deriv_byintp' _ ih δ). move: X=> [dy[dyto byintp]]. iIntros "→".
  iApply byintp. iIntros (δ' dyd'). apply dyto in dyd'. by iApply "→".
Qed.

(** [Deriv] is monotone over the inductive hypothesis *)
Lemma Deriv_mono `{!Deriv DI ih δ} (ih' : _ → Prop) :
  (∀ δ', ih δ' → ih' δ') → Deriv DI ih' δ.
Proof.
  move=> ihto. move: δ Deriv0. fix FIX 2=> δ [[dy[dyto byintp]]]. split.
  exists (Deriv _ ih'). split; [done|]=>/= ?. iIntros "big". iApply byintp.
  iIntros (???). iApply "big"; iPureIntro; by [apply FIX, dyto|apply ihto].
Qed.

(** [Deriv] can accumulate the inductive hypothesis *)
Lemma Deriv_acc {DI ih} res :
  (∀ δ, Deriv DI (res ∧₁ ih) δ → res δ) → ∀ δ, Deriv DI ih δ → res δ.
Proof.
  move=> to δ dyd. apply to. move: δ dyd. fix FIX 2=> δ [[dy[dyto byintp]]].
  split. exists (Deriv _ (res ∧₁ ih)). split; [done|]=>/= ?. iIntros "big".
  iApply byintp. iIntros (? dyd' ?). move: dyd'=>/dyto/FIX ?.
  iApply "big"; iPureIntro; [done|]. split; by [apply to|].
Qed.

(** Introduce a candidate *)
Lemma Deriv_intro `{!Deriv DI ih δ} {J} :
  (∀ δ', ⌜Deriv DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ')) -∗ ⸨ J ⸩(δ).
Proof.
  iIntros "∀". iApply Deriv_byintp. iIntros (???) "_ _". by iApply "∀".
Qed.

(** Update candidates *)
Lemma Deriv_map `{!Deriv DI ih δ} {J J'} :
  (∀ δ', ⌜Deriv DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ')) -∗
  ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ).
Proof.
  iIntros "∀ J". iApply Deriv_byintp. iIntros (???) "#→ _".
  iApply "∀"; by [| |iApply "→"].
Qed.
Lemma Deriv_map2 `{!Deriv DI ih δ} {J J' J''} :
  (∀ δ', ⌜Deriv DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗
    ⟦ J'' ⟧(δ')) -∗
  ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ) -∗ ⸨ J'' ⸩(δ).
Proof.
  iIntros "∀ J J'". iApply Deriv_byintp. iIntros (???) "#→ _".
  iApply ("∀" with "[//] [//] [J]"); by iApply "→".
Qed.
Lemma Deriv_map3 `{!Deriv DI ih δ} {J J' J'' J'''} :
  (∀ δ', ⌜Deriv DI ih δ'⌝ → ⌜ih δ'⌝ → ⟦ J ⟧(δ') -∗ ⟦ J' ⟧(δ') -∗
    ⟦ J'' ⟧(δ') -∗ ⟦ J''' ⟧(δ')) -∗
  ⸨ J ⸩(δ) -∗ ⸨ J' ⸩(δ) -∗ ⸨ J'' ⸩(δ) -∗ ⸨ J''' ⸩(δ).
Proof.
  iIntros "∀ J J' J''". iApply Deriv_byintp. iIntros (???) "#→ _".
  iApply ("∀" with "[//] [//] [J] [J']"); by iApply "→".
Qed.

(** ** [deriv]: Derivability *)

(** [deriv_gen]: What becomes [deriv] by taking [bi_least_fixpoint] *)
Definition deriv_gen {DI} (self : deriv_ty' DI) : deriv_ty' DI := λ J,
  (∀ δ, ⌜Deriv DI True₁ δ⌝ → □ dsound (Dwrap self) δ -∗
    □ dtrans (Dwrap self) δ -∗ ⟦ J ⟧(δ))%I.
#[export] Instance deriv_gen_mono {DI} :
  BiMonoPred (A:=leibnizO _) (deriv_gen (DI:=DI)).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" (?) "big".
  iIntros (??) "#Ψδ #Ψδ'".
  iApply "big"; [done|..]; iIntros "!> % ?"; [iApply "Ψδ"|iApply "Ψδ'"];
    by iApply "ΦΨ".
Qed.

(** [deriv]: Derivability *)
Definition deriv_def {DI} : deriv_ty DI :=
    Dwrap (bi_least_fixpoint (A:=leibnizO _) deriv_gen).
Lemma deriv_aux : seal (@deriv_def). Proof. by eexists. Qed.
Definition deriv {DI} := deriv_aux.(unseal) DI.
Lemma deriv_unseal : @deriv = @deriv_def. Proof. exact: seal_eq. Qed.

(** Notation for [dwrap] *)
Module DerivNotation.
  Export DerivNotation'.
  Notation "⸨ J ⸩" := ⸨ J ⸩(deriv) (format "⸨  J  ⸩") : nola_scope.
End DerivNotation.

(** [deriv] satisfies [Deriv] *)
#[export] Instance deriv_Deriv {DI} : Deriv DI True₁ deriv.
Proof.
  rewrite deriv_unseal. split. eexists _. split; [done|]=>/=. iIntros (?) "big".
  rewrite least_fixpoint_unfold. iIntros (??) "#→δ #→δ'".
  iApply "big"; [done..| |]; iIntros "!> % ?/="; by [iApply "→δ"|iApply "→δ'"].
Qed.

(** [deriv] is sound w.r.t. the interpretation under [deriv] *)
Lemma deriv_sound {DI} : ⊢ dsound (DI:=DI) deriv deriv.
Proof.
  rewrite deriv_unseal. iApply (least_fixpoint_ind (A:=leibnizO _)).
  iIntros "!> % gen". rewrite -deriv_unseal.
  iApply ("gen" $! _ deriv_Deriv); iIntros "!> % /="; rewrite deriv_unseal.
  { iIntros "[$ _]". } { iIntros "[_ $]". }
Qed.
