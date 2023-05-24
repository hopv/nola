(** * [wft]: Type with a well-founded relation *)

From nola Require Export util.rel.
Import EqNotations.

(** ** [wft]: Type with a well-founded relation *)

#[projections(primitive)]
Structure wft := Wft {
  (** Underlying type *)
  wft_car :> Type;
  (** Registered relation

    Transitivity is not required despite the name/notation *)
  #[canonical=no] wft_lt : wft_car → wft_car → Prop;
  (** [wft_lt] is well-founded *)
  #[canonical=no] wft_lt_wf : wf wft_lt;
}.
Add Printing Constructor wft.

Arguments wft_car : simpl never.
Arguments wft_lt {A} _ _ : simpl never, rename.
Arguments wft_lt_wf {A} : simpl never, rename.
Infix "≺" := wft_lt (at level 70, no associativity) : nola_scope.
Notation "(≺)" := wft_lt (only parsing) : nola_scope.

(** Inverse of [≺] *)
Definition wft_gt {A : wft} (a b : A) := b ≺ a.
Infix "≻" := wft_gt (at level 70, no associativity) : nola_scope.
Notation "(≻)" := wft_gt (only parsing) : nola_scope.

(** [≺] is irreflexive *)
#[export] Instance wft_lt_irrefl {A : wft} : Irreflexive A.(wft_lt).
Proof. apply wf_irrefl, wft_lt_wf. Qed.

(** [≺] is asymmetric *)
#[export] Instance wft_lt_asymm {A : wft} : Asymmetric A.(wft_lt).
Proof. apply wf_asymm, wft_lt_wf. Qed.

(** ** Make [unit] [wft] *)

Canonical unit_wft := Wft unit (λ _ _, False) false_wf.

(** ** Make [nat] [wft] *)

Canonical nat_wft := Wft nat (<) (well_founded_ltof _ _).

(** ** Make [fin n] [wft] *)

Canonical fin_wft n := Wft (fin n) (<) (well_founded_ltof _ _).

(** ** [wfsum]: Indexed sum of [wft]s *)

Section wfsum.
  Context {A : wft} {F : A → wft}.

  (** [wfsum]: Indexed sum of [wft]s *)
  #[projections(primitive)]
  Record wfsum : Type := Wfsum {
    wfsum_idx : A;
    wfsum_val : F wfsum_idx;
  }.
  Add Printing Constructor wfsum.

  (** Relation for [wfsum] *)
  Definition wfsum_lt : wfsum → wfsum → Prop := λ '(Wfsum a b) '(Wfsum a' b'),
    a ≺ a'  ∨  ∃ eq : a = a', rew[F] eq in b ≺ b'.

  (** [wfsum_lt] is well-founded *)

  Local Lemma wfsum_lt_wf_pre a
    (IH : ∀ a', a' ≺ a → ∀ b, Acc wfsum_lt (Wfsum a' b)) b :
    Acc wfsum_lt (Wfsum a b).
  Proof.
    elim: {b}(wft_lt_wf b)=> b _ IH'. apply Acc_intro=> [[a' b']] [|].
    - move=> a'a. apply (IH _ a'a).
    - move=> [?+]. subst=>/=. by apply IH'.
  Qed.

  Lemma wfsum_lt_wf : wf wfsum_lt.
  Proof.
    move=> [a +]. elim: {a}(wft_lt_wf a)=> a _ IH b.
    apply Acc_intro=> [[a' b']] [?|]; [by apply IH|]=> [[? _]]. subst.
    by apply wfsum_lt_wf_pre.
  Qed.

  (** [wfsum] forms [wft] *)
  Canonical wfsum_wft := Wft wfsum wfsum_lt wfsum_lt_wf.
End wfsum.

Arguments wfsum {A} F.
