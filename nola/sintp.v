(** * [sintp]: Strong interpretation *)

From nola Require Export util.pred util.wft.
From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import tactics.
Local Delimit Scope bi_scope with bi.

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
#[export] Instance Swrap_nonex `{A : ofe} : NonExpansive (Swrap (A:=A)).
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
Notation psintp_ty IT := (sintp_ty IT → sintp_ty IT).

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
  Notation "⟦ s ⟧ˢ" := (intpsi_intp' s) (format "⟦ s ⟧ˢ ") : nola_scope.
End IntpNotation.
Import IntpNotation.

(** Operations on strong interpretations *)

Definition Falseˢ {IT} : sintp_ty IT := Swrap (λ _, False)%bi.
Notation "⊥ˢ" := Falseˢ : nola_scope.

Definition orˢ {IT} (s s' : sintp_ty IT) : sintp_ty IT :=
  Swrap (λ iP, ⸨ iP ⸩(s) ∨ ⸨ iP ⸩(s'))%bi.
Infix "∨ˢ" := orˢ (at level 50, left associativity) : nola_scope.

Definition apporˢ {IT} (σ : psintp_ty IT) (s : sintp_ty IT) : sintp_ty IT :=
  σ s ∨ˢ s.
Infix "$∨ˢ" := apporˢ (at level 50, left associativity) : nola_scope.

Definition wandˢ {IT} (s s' : sintp_ty IT) : IT.(intps_bi) :=
  ∀ iP, ⸨ iP ⸩(s) -∗ ⸨ iP ⸩(s').
Infix "-∗ˢ" := wandˢ (at level 99, right associativity) : nola_scope.
#[export] Instance wandˢ_nonex {IT} : NonExpansive2 (wandˢ (IT:=IT)).
Proof.
  unfold wandˢ=> ??? seq ?? s'eq. do 3 f_equiv; [apply seq|apply s'eq].
Qed.

Definition wandˢ_low {IT} (i : IT.(intps_idx)) (s s' : sintp_ty IT)
  : IT.(intps_bi) := ∀ j, ⌜j ≺ i⌝ → ∀ P, ⸨ P ⸩(s,j) -∗ ⸨ P ⸩(s',j).
Notation "s -∗ˢ[≺ i ] s'" := (wandˢ_low i s s')
  (at level 99, right associativity, format "'[' s  -∗ˢ[≺ i ]  '/' s' ']'")
  : nola_scope.
#[export] Instance wandˢ_low_nonex {IT} i :
  NonExpansive2 (wandˢ_low (IT:=IT) i).
Proof.
  unfold wandˢ_low=> ??? seq ?? s'eq. do 6 f_equiv; [apply seq|apply s'eq].
Qed.

(** ** [sintpy] : Characterization of the strong interpretation *)

Inductive sintpy ITI (σ : psintp_ty ITI) : Prop := {
  (** [σ] is non-expansive *)
  sintpy_nonex :: NonExpansive σ;
  (** [σ] is monotone over the coinductive hypothesis *)
  sintpy_mono {s s' : sintp_ty ITI} : □ (s -∗ˢ s') -∗ σ s -∗ˢ σ s';
  (** [σ] can accumulate coinductive hypotheses *)
  sintpy_acc {s} (r : sintp_ty ITI) : □ (r -∗ˢ σ (s ∨ˢ r)) -∗ r -∗ˢ σ s;
  (** For [sintpy_intp] *)
  sintpy_byintp' {s} :
    (* Parameterization by [sintpy'] is for strict positivity *)
    ∃ sintpy' : _ → Prop, (∀ σ', sintpy' σ' → sintpy ITI σ') ∧
    ⊢ ∀ iP, let i := iP.(sarg_idx) in
      (∀ σ', ⌜sintpy' σ'⌝ → □ (∀ P, ⸨ P ⸩(σ s, i) -∗ ⟦ P ⟧(σ' ⊥ˢ, i)) -∗
        □ (σ $∨ˢ s -∗ˢ σ' ⊥ˢ) -∗ □ (σ' ⊥ˢ -∗ˢ[≺ i] ⟦σ' ⊥ˢ⟧ˢ) -∗
        ⟦ iP ⟧(σ' ⊥ˢ))
      -∗ ⸨ iP ⸩(σ s)
}.
Existing Class sintpy.

(** [σ] is proper *)
#[export] Instance sintpy_proper `{!sintpy ITI σ} : Proper ((≡) ==> (≡)) σ.
Proof. apply ne_proper, _. Qed.

(** Get the strong interpretation [⸨ P ⸩(σ s, i)] by the interpretaion *)
Lemma sintpy_byintp `{!sintpy ITI σ} {s i P} :
  ⊢ (∀ σ', ⌜sintpy ITI σ'⌝ → (* Take any strong interpretation [σ'] *)
      (* Turn the strong interpration at level [i] into the interpretation *)
      □ (∀ P, ⸨ P ⸩(σ s, i) -∗ ⟦ P ⟧(σ' ⊥ˢ, i)) -∗
      (* Turn the coinductive strong interpretation into
        the given strong interpretation *)
      □ (σ $∨ˢ s -∗ˢ σ' ⊥ˢ) -∗
      (* Turn the given strong interpretation at a level lower than [i]
        into the interpretation *)
      □ (σ' ⊥ˢ -∗ˢ[≺ i] ⟦σ' ⊥ˢ⟧ˢ) -∗ ⟦ P ⟧(σ' ⊥ˢ, i))
    -∗ ⸨ P ⸩(σ s, i).
Proof.
  have X := (@sintpy_byintp' _ σ _ s). move: X=> [sy'[sy'to byintp]].
  iIntros "intp". iApply byintp. iIntros (σ' syσ'). apply sy'to in syσ'.
  by iApply "intp".
Qed.

(** Introduce [⸨ P ⸩(σ s, i)] *)
Lemma sintpy_intro `{!sintpy ITI σ} {s i P} :
  ⊢ (∀ σ', ⌜sintpy ITI σ'⌝ → ⟦ P ⟧(σ' ⊥ˢ, i)) -∗ ⸨ P ⸩(σ s, i).
Proof.
  iIntros "∀P". iApply sintpy_byintp. iIntros (??) "_ _ _". by iApply "∀P".
Qed.

(** Convert the data of [⸨ P ⸩(σ s, i)] *)
Lemma sintpy_convert `{!sintpy ITI σ} {s i P Q} :
  ⊢ (∀ σ', ⌜sintpy ITI σ'⌝ → ⟦ P ⟧(σ' ⊥ˢ, i) -∗ ⟦ Q ⟧(σ' ⊥ˢ, i)) -∗
    ⸨ P ⸩(σ s, i) -∗ ⸨ Q ⸩(σ s, i).
Proof.
  iIntros "∀PQ P". iApply sintpy_byintp. iIntros (??) "#to _ _".
  iApply "∀PQ"; [done|]. by iApply "to".
Qed.

(** ** [sintp]: Strong interpretation *)

(** [sintp_gen_gen]: What becomes [sintp_gen] by taking [bi_least_fixpoint] *)
Definition sintp_gen_gen ITI (self' self : sintp_ty' ITI)
  : sintp_ty' ITI := λ iP, let i := iP.(sarg_idx) in
  (∀ σ', ⌜sintpy ITI σ'⌝ →  □ (∀ P, ⸨ P ⸩(Swrap self, i) -∗ ⟦ P ⟧(σ' ⊥ˢ, i)) -∗
    □ (Swrap self' -∗ˢ σ' ⊥ˢ) -∗ □ (σ' ⊥ˢ -∗ˢ[≺ i] ⟦σ' ⊥ˢ⟧ˢ) -∗
    ⟦ iP ⟧(σ' ⊥ˢ))%bi.
#[export] Instance sintp_gen_gen_mono {ITI self'} :
  BiMonoPred (sintp_gen_gen ITI self').
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ" ((f, s)) "big".
  iIntros (??) "#Ψfto". iApply "big"; [done|]. iIntros "!#" (iP) "Φsf'".
  iApply "Ψfto". by iApply "ΦΨ".
Qed.

(** [sintp_gen]: What becomes [sintp] by taking [bi_greatest_fixpoint] *)
Definition sintp_gen ITI (self : sintp_ty' ITI) : sintp_ty' ITI :=
  bi_least_fixpoint (sintp_gen_gen ITI self).
#[export] Instance sintp_gen_mono {ITI} : BiMonoPred (sintp_gen ITI).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ". iApply least_fixpoint_ind.
  iIntros "!#" (?) "big". rewrite /sintp_gen least_fixpoint_unfold.
  iIntros (σ' ?) "#genΨto #Ψto". iApply "big"; [done| |]; iModIntro; clear.
  - iIntros (iP) "/= [big _]". iApply "genΨto"=>/=. iApply "big".
  - iIntros (iP) "/= Φ". iApply "Ψto". by iApply "ΦΨ".
Qed.

(** [sintp]: Strong interpretation *)
Definition sintp_gen' ITI (s self : sintp_ty' ITI) : sintp_ty' ITI :=
  sintp_gen ITI (λ iP, self iP ∨ s iP)%bi.
#[export] Instance sintp_gen'_mono {ITI s} : BiMonoPred (sintp_gen' ITI s).
Proof.
  split; [|solve_proper]=> Φ Ψ ??. iIntros "#ΦΨ". iApply bi_mono_pred.
  iIntros "!#" (?) "[?|?]"; [|by iRight]. iLeft. by iApply "ΦΨ".
Qed.
Definition sintp' ITI (s : sintp_ty' ITI) : sintp_ty' ITI :=
  bi_greatest_fixpoint (sintp_gen' ITI s).
Definition sintp ITI (s : sintp_ty ITI) : sintp_ty ITI :=
  Swrap (sintp' ITI (sunwrap s)).

(** [sintp] satisfies [sintpy] *)
#[export] Instance sintp_sintpy {ITI} : sintpy ITI (sintp ITI).
Proof. split.
  - move=> ? s s' ss'. unfold sintp, sintp'. f_equiv=> ?.
    apply greatest_fixpoint_ne; [|done]=> ??.
    unfold sintp_gen', sintp_gen. apply least_fixpoint_ne; [|done]=> ??.
    unfold sintp_gen_gen. (do 8 f_equiv)=> ?. f_equiv. apply ss'.
  - move=> [s] [s']. iIntros "#ss'". iApply greatest_fixpoint_strong_mono.
    clear. iIntros "!#" (?). iApply (bi_mono_pred (F:=sintp_gen _)).
    iIntros "!#" (iP) "[?|?]"; [by iLeft|]. iRight. by iApply "ss'".
  - move=> [s] [r]. iIntros "#rto" (iP) "r".
    iDestruct ("rto" with "r") as "Xsr"=>/=. iRevert (iP) "Xsr".
    iApply greatest_fixpoint_coind. iIntros "!#" (iP).
    rewrite /sintp' greatest_fixpoint_unfold. iRevert (iP).
    iApply (bi_mono_pred (F:=sintp_gen _)).
    iIntros "!#" (iP) "[?|[?|?]]"; [|by iRight|]; do 2 iLeft;
      by [iApply "rto"|done].
  - move=>/= ?. exists (sintpy _). split; [done|]. iIntros (?) "big".
    rewrite /sintp' greatest_fixpoint_unfold /sintp_gen'/sintp_gen
      least_fixpoint_unfold /=/curry. iIntros (σ syσ) "#A #B".
    iApply ("big" $! σ syσ); iIntros "!#" (?) "?"; [iApply "A"|iApply "B"]=>/=;
      by rewrite /sintp' greatest_fixpoint_unfold.
Qed.

(** [sintp] is an underapproximation of the interpretation under [sintp] *)
Lemma sintp_intp {ITI} : ⊢ sintp ITI ⊥ˢ -∗ˢ ⟦sintp ITI ⊥ˢ⟧ˢ.
Proof.
  iIntros ([i P]) "?". iStopProof. move: P. elim: {i}(wft_lt_wf i)=>/= i _ IH P.
  iIntros "X". rewrite /sintp' greatest_fixpoint_unfold.
  have: (Sarg i P).(sarg_idx) = i by done.
  move: {P}(Sarg i P : sintp_aty _)=> iP eq. iRevert (eq). iRevert (iP) "X".
  iApply least_fixpoint_ind. iIntros "!#" ([? P]) "/= X ->".
  iApply ("X" $! _ sintp_sintpy); iIntros "!#" (?) "/=".
  - iIntros "[X _]". by iApply "X".
  - by iIntros "[?|[]]".
  - iIntros. iStopProof. by apply IH.
Qed.