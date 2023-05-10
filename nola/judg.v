(** * Judgment and derivability *)

From nola Require Export prelude.
From nola.util Require Import pred wft.

(** ** [judg]: Judgment information *)
#[projections(primitive)]
Structure judg := Judg {
  (** Index type, with a well-founded relation *)
  #[canonical=no] judg_idx : wft;
  (** Data type *)
  judg_data :> judg_idx → Type;
  (** Semantics *)
  #[canonical=no] judg_sem :
    (∀ i, judg_data i → Prop) → ∀ i, judg_data i → Prop;
}.
Add Printing Constructor judg.
Arguments judg_sem {JU} φ i J : rename.

(** Derivability predicate *)
Notation deriv_ty JU := (∀ i, JU.(judg_data) i → Prop).
(** Derivability predicate parameterized over a derivability predicate *)
Notation pderiv_ty JU := (deriv_ty JU → deriv_ty JU).

(** Operations on derivability predicates *)

Definition Falseᵈ {JU} : deriv_ty JU := λ _ _, False.
Notation "⊥ᵈ" := Falseᵈ : nola_scope.

Definition orᵈ {JU} (φ ψ : deriv_ty JU) : deriv_ty JU := λ i J, φ i J ∨ ψ i J.
Infix "∨ᵈ" := orᵈ (at level 50, left associativity) : nola_scope.

Definition apporᵈ {JU} (δ : pderiv_ty JU) (φ : deriv_ty JU) : deriv_ty JU :=
  δ φ ∨ᵈ φ.
Infix "$∨ᵈ" := apporᵈ (at level 50, left associativity) : nola_scope.

Definition implᵈ {JU} (φ ψ : deriv_ty JU) : Prop := ∀ i J, φ i J → ψ i J.
Infix "→ᵈ" := implᵈ (at level 99, right associativity) : nola_scope.

Definition implᵈ_low {JU} (i : JU.(judg_idx)) (φ ψ : deriv_ty JU) : Prop :=
  ∀ j, j ≺ i → ∀ K, φ j K → ψ j K.
Infix "→ᵈ[≺ i ]" := (implᵈ_low i) (at level 99, right associativity)
  : nola_scope.

(** ** [derivy] : Characterization of a derivability predicate *)

(** Generator of [deriv] *)
Record derivy_gen (JU : judg) (self : pderiv_ty JU → Prop) (δ : pderiv_ty JU)
  : Prop := {
  (** [δ] is monotone over the coinductive hypothesis *)
  derivy_gen_mono {φ ψ : deriv_ty JU} : (φ →ᵈ ψ) → δ φ →ᵈ δ ψ;
  (** [δ] can accumulate coinductive hypotheses *)
  derivy_gen_acc {φ} (res : deriv_ty JU) : (res →ᵈ δ (φ ∨ᵈ res)) → res →ᵈ δ φ;
  (** [δ φ i J] can be proved by semantics *)
  derivy_gen_bysem {φ i J} :
    (∀ δ', self δ' → (δ φ i →₁ judg_sem (δ' ⊥ᵈ) i) → (δ $∨ᵈ φ →ᵈ δ' ⊥ᵈ) →
      (δ' ⊥ᵈ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ)) → judg_sem (δ' ⊥ᵈ) i J) →
    δ φ i J
}.
#[export] Instance derivy_gen_mono₁₁ {JU} : Mono₁₁ (derivy_gen JU).
Proof.
  move=> D E DE δ [?? bysem]. split; [done|done|]=> φ i J H.
  apply bysem=> δ' /DE. apply H.
Qed.

(** [derivy] : Characterization of a derivability predicate *)
Definition derivy (JU : judg) : pderiv_ty JU → Prop := mu (derivy_gen JU).
Existing Class derivy.

(** [inderivy JU δ' δ φ i] : Characterization of a derivability predicate
  in [δ φ i]'s [derivy_bysem] *)
Class inderivy (JU : judg) (δ' δ : pderiv_ty JU) (φ : deriv_ty JU)
  (i : JU.(judg_idx)) : Prop := {
  (** [δ'] satisfies [derivy] *)
  inderivy_derivy :: derivy JU δ';
  (** Interpret [δ φ i] as [judg_sem (δ' ⊥ᵈ) i] *)
  inderivy_sem : δ φ i →₁ judg_sem (δ' ⊥ᵈ) i;
  (** Turn [δ $∨ᵈ φ] into [δ' ⊥ᵈ] *)
  inderivy_turn : δ $∨ᵈ φ →ᵈ δ' ⊥ᵈ;
  (** Interpret [δ' ⊥ᵈ j] as [judg_sem (δ' ⊥ᵈ) j] for [j ≺ i] *)
  inderivy_semlow : δ' ⊥ᵈ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ);
}.

(** Lemmas for [derivy] *)
Lemma derivy_mono `{D : derivy JU δ} {φ ψ} : (φ →ᵈ ψ) → δ φ →ᵈ δ ψ.
Proof. move: D=> /mu_unfold [mono _ _]. apply mono. Qed.
Lemma derivy_acc `{D : derivy JU δ} {φ} res :
  (res →ᵈ δ (φ ∨ᵈ res)) → res →ᵈ δ φ.
Proof. move: D=> /mu_unfold [_ acc _]. apply acc. Qed.
Lemma derivy_bysem `{D : derivy JU δ} {φ i J} :
  (∀ δ', inderivy JU δ' δ φ i → judg_sem (δ' ⊥ᵈ) i J) → δ φ i J.
Proof. move: D=> /mu_unfold [_ _ bysem]=> H. apply bysem=> *. by apply H. Qed.

(** Lemmas for [inderivy] *)
Lemma inderivy_turn_l `{inderivy JU δ' δ φ i} : δ φ →ᵈ δ' ⊥ᵈ.
Proof. move=> *. apply inderivy_turn. by left. Qed.
Lemma inderivy_turn_r `{inderivy JU δ' δ φ i} : φ →ᵈ δ' ⊥ᵈ.
Proof. move=> *. apply inderivy_turn. by right. Qed.
Lemma inderivy_turn_semlow `{inderivy JU δ' δ φ i} :
  δ $∨ᵈ φ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ).
Proof. move=> *. apply inderivy_semlow; by [|apply inderivy_turn]. Qed.
Lemma inderivy_turn_semlow_l `{inderivy JU δ' δ φ i} :
  δ φ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ).
Proof. move=> *. apply inderivy_turn_semlow; by [|left]. Qed.
Lemma inderivy_turn_semlow_r `{inderivy JU δ' δ φ i} :
  φ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ).
Proof. move=> *. apply inderivy_turn_semlow; by [|right]. Qed.

(** ** [deriv]: Derivability *)

(** Generator of [deriv] *)
Inductive deriv_gen (JU : judg) (self : deriv_ty JU) i (J : JU i) : Prop := {
  (* Parameterization by [deriv_i] serves for strict positivity *)
  deriv_gen_bysem : ∃ deriv_i, (deriv_i →₁ deriv_gen JU self i) ∧
    (∀ δ', derivy JU δ' → (deriv_i →₁ judg_sem (δ' ⊥ᵈ) i) → (self →ᵈ δ' ⊥ᵈ) →
      (δ' ⊥ᵈ →ᵈ[≺ i] judg_sem (δ' ⊥ᵈ)) → judg_sem (δ' ⊥ᵈ) i J)
}.

(** Argument data of [deriv_ty JU] *)
#[projections(primitive)]
Record deriv_aty (JU : judg) := DerivAty {
  deriv_aty_idx : JU.(judg_idx);
  deriv_aty_data : JU deriv_aty_idx;
}.
Arguments DerivAty {_} _ _.

(** Conversion between [deriv_aty JU → Prop] and [deriv_ty JU] *)
Definition deriv_curry {JU} (φ : deriv_aty JU → Prop) : deriv_ty JU :=
  λ i J, φ (DerivAty i J).
Definition deriv_uncurry {JU} (φ : deriv_ty JU) : deriv_aty JU → Prop :=
  λ '(DerivAty i J), φ i J.

(** Modified [deriv_gen] *)
Definition deriv_gen' JU (φ : deriv_aty JU → Prop) : deriv_aty JU → Prop :=
  deriv_uncurry (deriv_gen JU (deriv_curry φ)).
#[export] Instance deriv_gen'_mono JU : Mono₁₁ (deriv_gen' JU).
Proof.
  move=> φ ψ φψ [i J] +. move: i J. fix FIX 3=> i J [[der[derto big]]].
  split. exists der. split. { move=> K /derto. apply FIX. }
  move=> δ' ?? turn ?. apply big; [done|done| |done]=> j K /φψ. apply turn.
Qed.

(** [deriv]: Derivability *)
Definition deriv (JU : judg) (φ : deriv_ty JU) : deriv_ty JU :=
  deriv_curry (pnu (deriv_gen' JU) (deriv_uncurry φ)).

(** [deriv] satisfies [derivy] *)
#[export] Instance deriv_derivy {JU} : derivy JU (deriv JU).
Proof.
  apply mu_fold. split.
  - move=> φ ψ φψ i J. apply pnu_mono=> [[j K]] /φψ. done.
  - move=> φ res resto i J ?. apply (pnu_acc (deriv_uncurry res)); [|done].
    move=> [j K] /resto. done.
  - move=> φ i J H. apply pnu_fold. split. exists (deriv JU φ i).
    split. { by move=> J' /pnu_unfold. } { move=> δ'. apply H. }
Qed.

(** Soundness of [deriv] *)
Lemma deriv_sound {JU} : deriv JU ⊥ᵈ →ᵈ judg_sem (deriv JU ⊥ᵈ).
Proof.
  move=> i +. elim: {i}(wft_lt_wf i)=> i _ IH + /nu_unfold. fix FIX 2.
  move=> J [[drvi[drvito big]]]. apply big. { apply _. }
  { move=> J' /drvito. apply FIX. } { by move=> *. } { done. }
Qed.
