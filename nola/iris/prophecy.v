(** * Prophecy *)

From nola Require Export prelude.
From nola.util Require Import rel.
From nola.iris Require Import discrete_fun.
From iris.algebra Require Import auth functions gmap csum frac agree.
From iris.bi Require Import fractional.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
Import EqNotations.

(** ** Syntactic type *)

#[projections(primitive)]
Structure synty := Synty {
  (* Syntax *) synty_car :> Type;
  (* Type interpretation *) synty_ty : synty_car → Type;
  (* Equality decision over the syntax *) synty_eqdec :: EqDecision synty_car;
  (* Inhabitance proposition *) synty_inhab : synty_car → Prop;
  (* [synty_inhab] ensures [Inhabited] *) synty_inhabited ::
    ∀ X, synty_inhab X → Inhabited (synty_ty X);
  (* An inhabitance implies [synty_inhab] *) synty_to_inhab :
    ∀ X, synty_ty X → synty_inhab X;
  (* [synty_inhab] is proof-irrelevant *) synty_inhab_irrel ::
    ∀ X, ProofIrrel (synty_inhab X);
}.
Coercion synty_ty : synty_car >-> Sortclass.
Arguments synty_ty {_} _. Arguments synty_eqdec {_} _.
Arguments synty_inhab {_} _. Arguments synty_inhabited {_ _} _.
Arguments synty_to_inhab {_ _} _. Arguments synty_inhab_irrel {_ _} _.

(** Prophecy variable *)

Implicit Type TY : synty.

(** ** Prophecy variable and assignment *)

(** Prophecy variable *)
#[projections(primitive)]
Record prvar {TY : synty} (A : TY) := Prvar {
  (* Proof of inhabitance *) prvar_inhab : synty_inhab A;
  (* Id *) prvar_id : positive;
}.
Add Printing Constructor prvar.
Arguments prvar_inhab {_ _} _. Arguments prvar_id {_ _} _.
Arguments Prvar {_ _} _ _.

(** Equality decision over [prvar] *)
#[export] Instance prvar_eq_dec {TY} (A : TY) : EqDecision (prvar A).
Proof.
  move=> [h i] [h' j]. rewrite (proof_irrel h h'). case: (decide (i = j))=> ?.
  { subst. by left. } { right. by case. }
Defined.

(** Inhabitedness of [prvar] *)

(** Prophecy variable of any type *)
#[projections(primitive)]
Record aprvar (TY : synty) := Aprvar {
  (* Type *) aprvar_ty : TY;
  (* Variable *) aprvar_var :> prvar aprvar_ty;
}.
Add Printing Constructor aprvar.
Arguments aprvar_ty {_}. Arguments aprvar_var {_}.
Arguments Aprvar {_} _ _.
Coercion Aprvar : prvar >-> aprvar.

(** Equality decision over [aprvar] *)
#[export] Instance aprvar_eq_dec {TY} : EqDecision (aprvar TY).
Proof.
  move=> [X [h i]] [Y [h' j]]. case: (decide (X = Y)); last first.
  { move=> ?. right. by case. }
  move=> ?. subst. rewrite (proof_irrel h h').
  case: (decide (i = j))=> ?. { subst. by left. } { right. by case. }
Defined.

(** Prophecy assignment *)
Definition proph_asn (TY : synty) := ∀ ξ : aprvar TY, ξ.(aprvar_ty).
(** Value under a prophecy assignment *)
Notation proph TY A := (proph_asn TY → A).

(** [proph_asn] is inhabited *)
#[export] Instance proph_asn_inhabited {TY} : Inhabited (proph_asn TY).
Proof. apply populate. move=> [?[??]]. by apply synty_inhabited. Qed.

(** ** Prophecy Dependency *)

(** Equivalence of prophecy assignments over a set of prophecy variables *)
Local Definition proph_asn_eqv {TY}
  (φ : aprvar TY → Prop) (π π' : proph_asn TY) :=
  ∀ ξ : aprvar TY, φ ξ → π ξ = π' ξ.
Local Notation "π .≡{ φ }≡ π'" := (proph_asn_eqv φ π π')
  (at level 70, format "π  .≡{ φ }≡  π'").

(** Prophecy dependency *)
Definition proph_dep {TY A} (aπ : proph TY A) (ξl: list (aprvar TY)) :=
  ∀ π π', π .≡{ (.∈ ξl) }≡ π' → aπ π = aπ π'.
Notation "aπ ./ ξl" := (proph_dep aπ ξl) (at level 70, format "aπ  ./  ξl")
  : nola_scope.

(** Lemmas *)

Section lemmas.
  Context {TY}.
  Implicit Type (ξ η ζ : aprvar TY) (ξl ηl ζl : list (aprvar TY)).

  (** Monotonicity over the list set *)
  #[export] Instance proph_dep_mono {A} (aπ : proph TY A) :
    Proper ((⊆) ==> impl) (proph_dep aπ).
  Proof. move=>/= ?? sub dep ?? eqv. apply dep => ??. by apply eqv, sub. Qed.
  #[export] Instance proph_dep_mono' {A} (aπ : proph TY A) :
    Proper (flip (⊆) ==> flip impl) (proph_dep aπ).
  Proof. solve_proper. Qed.
  #[export] Instance proph_dep_proper {A} (aπ : proph TY A) :
    Proper ((≡ₚ) ==> iff) (proph_dep aπ).
  Proof. move=> ?? eq. split; apply proph_dep_mono; by rewrite eq. Qed.

  (** On [(.$ ξ)] *)
  Lemma proph_dep_one ξ : (λ π, π ξ) ./ [ξ].
  Proof. move=> ?? eqv. apply eqv. constructor. Qed.

  (** Construct with a function *)
  Lemma proph_dep_constr {A B} (f : A → B) aπ ξl :
    aπ ./ ξl → (λ π, f (aπ π)) ./ ξl.
  Proof. move=> dep ?? /dep ?. by apply (f_equal f). Qed.
  Lemma proph_dep_constr2 {A B C} (f: A → B → C) aπ bπ ξl ηl :
    aπ ./ ξl → bπ ./ ηl → (λ π, f (aπ π) (bπ π)) ./ ξl ++ ηl.
  Proof.
    move=> dep dep' ?? eqv.
    eapply proph_dep_mono, (.$ eqv) in dep, dep'; [|set_solver..]. by f_equal.
  Qed.
  Lemma proph_dep_constr3 {A B C D} (f: A → B → C → D) aπ bπ cπ ξl ηl ζl :
    aπ ./ ξl → bπ ./ ηl → cπ ./ ζl →
    (λ π, f (aπ π) (bπ π) (cπ π)) ./ ξl ++ ηl ++ ζl.
  Proof.
    move=> dep dep' dep'' ?? eqv.
    eapply proph_dep_mono, (.$ eqv) in dep, dep', dep''; [|set_solver..].
    by f_equal.
  Qed.

  (** Destruct from an injective function *)
  Lemma proph_dep_destr {A B} f `{!@Inj A B (=) (=) f} aπ ξl :
    (λ π, f (aπ π)) ./ ξl → aπ ./ ξl.
  Proof. by move=> dep ?? /dep/(inj f) ?. Qed.
  Lemma proph_dep_destr2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} aπ bπ ξl :
    (λ π, f (aπ π) (bπ π)) ./ ξl → aπ ./ ξl ∧ bπ ./ ξl.
  Proof.
    move=> dep. split; move=> ?? /dep eq; apply (inj2 f) in eq; tauto.
  Qed.

  (** On a singleton type *)
  Lemma proph_dep_singleton {A} (aπ : proph TY A) :
    (∀ a a' : A, a = a') → aπ ./ [].
  Proof. by move=> ????. Qed.
End lemmas.

(** ** Prophecy log *)

(** Prophecy log item *)
#[projections(primitive)]
Record proph_log_item TY := ProphLogItem {
  (* Prophecy variable *) pli_var : aprvar TY;
  (* Prophetic value *) pli_val : proph TY pli_var.(aprvar_ty);
}.
Arguments pli_var {_}. Arguments pli_val {_}.
Arguments ProphLogItem {_} _ _.
Local Notation ".{ ξ := aπ }" := (ProphLogItem ξ aπ)
  (format ".{ ξ  :=  aπ }").

(** Prophecy log *)
Local Definition proph_log TY := list (proph_log_item TY).

(** Prophecy variables of a prophecy log *)
Local Definition pl_vars {TY} (L : proph_log TY) : list (aprvar TY) :=
  pli_var <$> L.

(** Prophecy dependency over the complement of a list set *)
Local Definition proph_dep_out {TY A}
  (aπ : proph TY A) (ξl : list (aprvar TY)) :=
  ∀ π π', π .≡{ (.∉ ξl) }≡ π' → aπ π = aπ π'.
Local Notation "aπ ./~ ξl" := (proph_dep_out aπ ξl)
  (at level 70, format "aπ  ./~  ξl").

(** Validity of a prophecy log *)
Local Fixpoint proph_log_valid {TY} (L : proph_log TY) :=
  match L with
  | [] => True
  | .{ξ := aπ} :: L' =>
      ξ ∉ pl_vars L' ∧ aπ ./~ pl_vars L ∧ proph_log_valid L'
  end.
Local Notation ".✓ L" := (proph_log_valid L) (at level 20, format ".✓  L").

(** A prophecy assignment satisfying a prophecy log *)
Local Definition proph_sat {TY} (π : proph_asn TY) (L : proph_log TY) :=
  Forall (λ pli, π pli.(pli_var) = pli.(pli_val) π) L.
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").

(** A prophecy assignment updated at a prophecy variable *)
Local Definition proph_upd {TY}
  (ξ : aprvar TY) (aπ : proph TY ξ.(aprvar_ty)) π : proph_asn TY := λ η,
  match decide (ξ = η) with
  | left eq => rew[aprvar_ty] eq in aπ π
  | right _ => π η
  end.
Local Notation ":<[ ξ := aπ ]>" := (proph_upd ξ aπ)
  (at level 5, format ":<[ ξ  :=  aπ ]>").

(** Access on [proph_upd] *)
Local Lemma proph_upd_self {TY} {π : proph_asn TY} {ξ aπ} :
  :<[ξ := aπ]> π ξ = aπ π.
Proof.
  rewrite /proph_upd. case: (decide (ξ = ξ)); [|done]=> eq.
  by rewrite (eq_dec_refl eq).
Qed.
Local Lemma proph_upd_ne {TY} {π : proph_asn TY} {ξ aπ η} :
  ξ ≠ η → :<[ξ := aπ]> π η = π η.
Proof. rewrite /proph_upd. by case (decide (ξ = η)). Qed.

(** Prophecy assignment updated by a prophecy log *)
Local Fixpoint proph_upds {TY} L (π : proph_asn TY) :=
  match L with
  | [] => π
  | .{ξ := aπ} :: L' => proph_upds L' (:<[ξ := aπ]> π)
  end.
Local Notation ":<[ L ]>" := (proph_upds L)
  (at level 5, format ":<[ L ]>").

(** Equivalence out of [L] for [proph_upds] *)
Local Lemma proph_upds_eqv_out {TY} (L : proph_log TY) :
  ∀ π, :<[L]> π .≡{ (.∉ pl_vars L) }≡ π.
Proof.
  elim L=>/= [|[??]? IH]; [done|]=> > /not_elem_of_cons [??].
  rewrite IH; [|done]. by apply proph_upd_ne.
Qed.

(** [L] can by satisfied by [:<[L]>] for valid [L] *)
Local Lemma proph_valid_upds_sat {TY} {L : proph_log TY} :
  .✓ L → ∀π, :<[L]> π ◁ L.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[ξ aπ] L' IH]; [done|].
  move=> [?[? /IH ?]]?. apply Forall_cons=>/=. split; [|done].
  rewrite proph_upds_eqv_out; [|done]. rewrite proph_upd_self.
  set L := .{ξ := aπ} :: L'. have dep': aπ ./~ pl_vars L by done. symmetry.
  apply dep', (proph_upds_eqv_out L).
Qed.
(** [L] can by satisfied for valid [L] *)
Local Lemma proph_valid_sat {TY} {L : proph_log TY} : .✓ L → ∃ π, π ◁ L.
Proof. exists (:<[L]> inhabitant). by apply proph_valid_upds_sat. Qed.

(** ** Prophecy resource algebra *)

(** Algebra for a prophecy variable *)
Local Definition proph_itemR {TY} (X : TY) :=
  csumR fracR (agreeR (leibnizO (proph TY X))).
(** Algebra for prophecy variables of a type *)
Local Definition proph_gmapR {TY} (X : TY) := gmapR positive (proph_itemR X).
(** Algebra for all prophecy variables *)
Local Definition proph_smryR TY := discrete_funR (proph_gmapR (TY:=TY)).
(** Algebra for the prophecy machinery *)
Local Definition prophR_def TY := authR (proph_smryR TY).
Lemma prophR_aux : seal prophR_def. Proof. by eexists. Qed.
Definition prophR := prophR_aux.(unseal).
Lemma prophR_unseal : prophR = prophR_def. Proof. exact: seal_eq. Qed.

(** Ghost state *)
Class prophGS TY Σ := ProphGS {
  prophG_in :: inG Σ (prophR TY);
  proph_name : gname
}.
Local Instance inG_prophR_def `{!inG Σ (prophR PROP)} :
  inG Σ (prophR_def PROP).
Proof. rewrite -prophR_unseal. exact _. Qed.
Class prophGpreS TY Σ := prophGpreS_in :: inG Σ (prophR TY).
Definition prophΣ TY := GFunctor (prophR TY).
#[export] Instance subG_prophPreG `{!subG (prophΣ TY) Σ} : prophGpreS TY Σ.
Proof. solve_inG. Qed.

(** Namespace for the prophecy machinery *)
Definition prophN: namespace := nroot .@ "proph".

(** Access a summary at a prophecy *)
Local Notation proph_access S ξ := (S ξ.(aprvar_ty) !! ξ.(prvar_id)).

(** Fractional item *)
Local Definition fitem {TY} {X : TY} (q : Qp) : proph_itemR X := Cinl q.
(** Agreement item *)
Local Definition aitem {TY} {X : TY} aπ : proph_itemR X := Cinr (to_agree aπ).
(** One line in a prophecy summary *)
Local Definition line {TY} ξ it : proph_smryR TY :=
  .{[ξ.(aprvar_ty) := {[ξ.(prvar_id) := it]}]}.
(** Add a line in a prophecy summary *)
Local Definition add_line {TY} ξ it (S : proph_smryR TY) : proph_smryR TY :=
  .<[ξ.(aprvar_ty) := <[ξ.(prvar_id) := it]> (S ξ.(aprvar_ty))]> S.

(** Access [add_line] out of the additionn *)
Local Lemma add_line_ne {TY} {ξ η : aprvar TY} {S aπ} : ξ ≠ η →
  proph_access (add_line ξ (aitem aπ) S) η ≡ proph_access S η.
Proof.
  move: aπ. case: ξ η=> [X[h i]][Y[h' j]] ? ne.
  rewrite /add_line /discrete_fun_insert /=.
  case (decide (X = Y)); [|done]=> eq. simplify_eq=>/=.
  case (decide (i = j))=> ?; [|by rewrite lookup_insert_ne]. simplify_eq.
  move: ne. by rewrite (proof_irrel h h').
Qed.

(** A prophecy summary simulating a prophecy log *)
Local Definition proph_sim {TY} (S : proph_smryR TY) (L : proph_log TY) :=
  ∀ (ξ : aprvar _) aπ, proph_access S ξ ≡ Some (aitem aπ) ↔ .{ξ := aπ} ∈ L.
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

(** [:~] on [add_line] *)
Local Lemma add_line_fitem_sim {TY X} {S : proph_smryR TY} {L h i} :
  S :~ L → S X !! i = None → let ξ := Aprvar X (Prvar h i) in
  add_line ξ (fitem 1) S :~ L.
Proof.
  move=> sim no ?[Y [? j]]?.
  rewrite -sim /add_line /discrete_fun_insert /=.
  case: (decide (X = Y)); [|done]=> ?. subst=>/=.
  case: (decide (i = j))=> ?; [|by rewrite lookup_insert_ne]. subst.
  rewrite lookup_insert no.
  split=> eqv; [apply (inj Some) in eqv|]; inversion eqv.
Qed.
Local Lemma add_line_aitem_sim {TY} {S : proph_smryR TY} {L ξ aπ} :
  S :~ L → ξ ∉ pl_vars L →
  add_line ξ (aitem aπ) S :~ .{ξ := aπ} :: L.
Proof.
  move=> sim ?. have inLne η wπ : .{η := wπ} ∈ L → ξ ≠ η.
  { move=> /(elem_of_list_fmap_1 pli_var) ??. by subst. }
  move=> η bπ. rewrite elem_of_cons. case (decide (ξ = η))=> ?.
  { subst. rewrite /add_line discrete_fun_lookup_insert lookup_insert. split.
    - move=> /(inj (Some ∘ aitem)) ->. by left.
    - move=> [[?]|/inLne ?]; by [simplify_eq|]. }
  rewrite add_line_ne; [|done]. rewrite sim. split; [by right|].
  case; [|done]=> ?. simplify_eq.
Qed.

(** ** Iris propositions *)

Section defs.
  Context `{!prophGS TY Σ, !invGS_gen hlc Σ}.

  (** Token for a prophecy summary *)
  Local Definition proph_smry_tok (S : proph_smryR TY) : iProp Σ :=
    own proph_name (● S).
  (** Invariant for the prophecy *)
  Local Definition proph_inv : iProp Σ :=
    ∃ S, ⌜∃L, .✓ L ∧ S :~ L⌝ ∗ proph_smry_tok S.
  (** Prophecy context *)
  Local Definition proph_ctx_def : iProp Σ := inv prophN proph_inv.
  Lemma proph_ctx_aux : seal proph_ctx_def. Proof. by eexists. Qed.
  Definition proph_ctx := proph_ctx_aux.(unseal).
  Lemma proph_ctx_unseal : proph_ctx = proph_ctx_def.
  Proof. exact: seal_eq. Qed.

  (** Prophecy token *)
  Local Definition proph_tok_def (ξ : aprvar _) (q : Qp) : iProp Σ :=
    own proph_name (◯ line ξ (fitem q)).
  Lemma proph_tok_aux : seal proph_tok_def. Proof. by eexists. Qed.
  Definition proph_tok := proph_tok_aux.(unseal).
  Lemma proph_tok_unseal : proph_tok = proph_tok_def.
  Proof. exact: seal_eq. Qed.

  (** Atomic prophecy observation *)
  Local Definition proph_aobs pli : iProp Σ :=
    own proph_name (◯ line pli.(pli_var) (aitem pli.(pli_val))).
  (** Prophecy observation *)
  Local Definition proph_obs_def (φπ : proph _ Prop) : iProp Σ :=
    ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_aobs pli.
  Lemma proph_obs_aux : seal proph_obs_def. Proof. by eexists. Qed.
  Definition proph_obs := proph_obs_aux.(unseal).
  Lemma proph_obs_unseal : proph_obs = proph_obs_def.
  Proof. exact: seal_eq. Qed.
End defs.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 2, left associativity, format "q :[ ξ ]") : bi_scope.
Notation proph_toks ξl q := ([∗ list] ξ ∈ ξl, q:[ξ])%I (only parsing).
Notation "q :∗[ ξl ]" := (proph_toks ξl q)
  (at level 2, left associativity, format "q :∗[ ξl ]") : bi_scope.
Notation ".⟨ φπ ⟩" := (proph_obs φπ%type%stdpp)
  (at level 1, format ".⟨ φπ ⟩") : bi_scope.
Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
  (at level 1, format "⟨ π ,  φ ⟩") : bi_scope.

(** ** Lemmas *)

(** Allocate [proph_ctx] *)
Lemma proph_init `{!prophGpreS TY Σ, !invGS_gen hlc Σ} E :
  ↑prophN ⊆ E → ⊢ |={E}=> ∃ _ : prophGS TY Σ, proph_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●"; [by apply auth_auth_valid|].
  iExists (ProphGS _ _ _ γ). rewrite proph_ctx_unseal.
  iMod (inv_alloc _ _ proph_inv with "[●]") as "?"; [|done]. iModIntro.
  iExists ε. iFrame "●". iPureIntro. exists []. split; [done|]=> ??.
  rewrite lookup_empty. split=> hyp; inversion hyp.
Qed.

Section lemmas.
  Context `{!prophGS TY Σ, !invGS_gen hlc Σ}.
  Implicit Type (φπ ψπ : proph TY Prop).

  (** [proph_ctx] is persistent *)
  #[export] Instance proph_ctx_persistent : Persistent proph_ctx.
  Proof. rewrite proph_ctx_unseal. exact _. Qed.

  (** [proph_tok] is timelesss and fractional *)
  #[export] Instance proph_tok_timeless {q ξ} : Timeless q:[ξ].
  Proof. rewrite proph_tok_unseal. exact _. Qed.
  #[export] Instance proph_tok_fractional {ξ} : Fractional (λ q, q:[ξ]%I).
  Proof.
    move=> ??. by rewrite proph_tok_unseal -own_op -auth_frag_op
      discrete_fun_singleton_op singleton_op -Cinl_op.
  Qed.
  #[export] Instance proph_tok_as_fractional {q ξ} :
    AsFractional q:[ξ] (λ q, q:[ξ]%I) q.
  Proof. split; by [|exact _]. Qed.
  #[export] Instance frame_proph_tok `{!FrameFractionalQp q r s} {p ξ} :
    Frame p q:[ξ] r:[ξ] s:[ξ] | 5.
  Proof. apply: frame_fractional. Qed.
  (** [proph_toks] is fractional *)
  #[export] Instance proph_toks_as_fractional {q ξl} :
    AsFractional q:∗[ξl] (λ q, q:∗[ξl]%I) q.
  Proof. split; by [|exact _]. Qed.
  #[export] Instance frame_proph_toks `{!FrameFractionalQp q r s} {p ξl} :
    Frame p q:∗[ξl] r:∗[ξl] s:∗[ξl] | 5.
  Proof. apply: (frame_fractional _ _ _ _ _ _ _ proph_toks_as_fractional). Qed.

  (** [proph_obs] is persistent, timeless and monotone *)
  #[export] Instance proph_obs_persistent φπ : Persistent .⟨φπ⟩.
  Proof. rewrite proph_obs_unseal. exact _. Qed.
  #[export] Instance proph_obs_timeless φπ : Timeless .⟨φπ⟩.
  Proof. rewrite proph_obs_unseal. exact _. Qed.
  #[export] Instance proph_obs_mono :
    Proper (pointwise_relation _ impl ==> (⊢)) proph_obs.
  Proof.
    move=> ?? imp. rewrite proph_obs_unseal /proph_obs_def. do 4 f_equiv.
    move=> imp' ??. by apply imp, imp'.
  Qed.
  #[export] Instance proph_obs_mono' :
    Proper (pointwise_relation _ (flip impl) ==> flip (⊢)) proph_obs.
  Proof. solve_proper. Qed.
  #[export] Instance proph_obs_proper :
    Proper (pointwise_relation _ (↔) ==> (⊣⊢)) proph_obs.
  Proof.
    move=>/= ?? iff. by apply bi.equiv_entails; split; f_equiv=> ? /iff.
  Qed.

  (** On [proph_tok] *)
  Lemma proph_tok_singleton {ξ q} : q:[ξ] ⊣⊢ q:∗[[ξ]].
  Proof. by rewrite/= right_id. Qed.
  Lemma proph_tok_combine {ξl ηl q r} :
    q:∗[ξl] -∗ r:∗[ηl] -∗ ∃ s,
      s:∗[ξl ++ ηl] ∗ (s:∗[ξl ++ ηl] -∗ q:∗[ξl] ∗ r:∗[ηl]).
  Proof.
    case: (Qp.lower_bound q r)=> [s[?[?[->->]]]]. iIntros "[ξl ξl'][ηl ηl']".
    iExists s. iFrame "ξl ηl ξl' ηl'". iIntros "[$$]".
  Qed.

  (** On [proph_tok] *)
  Lemma proph_obs_true {φπ} : (∀π, φπ π) → ⊢ ⟨π, φπ π⟩.
  Proof. rewrite proph_obs_unseal=> ?. iExists []. by iSplit. Qed.
  Lemma proph_obs_and {φπ ψπ} : .⟨φπ⟩ -∗ .⟨ψπ⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
  Proof.
    rewrite proph_obs_unseal. iIntros "[%L[%Toφπ L]] [%L'[%Toψπ L']]".
    iExists (L ++ L'). iFrame "L L'". iPureIntro=> ? /Forall_app[??].
    split; by [apply Toφπ|apply Toψπ].
  Qed.
  #[export] Instance proph_obs_combine φπ ψπ :
    CombineSepAs .⟨φπ⟩ .⟨ψπ⟩ ⟨π, φπ π ∧ ψπ π⟩.
  Proof. rewrite /CombineSepAs. iIntros "#[??]". by iApply proph_obs_and. Qed.

  Lemma proph_intro (I : gset positive) {X : TY} (x : X) {E} :
    ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃ i, ⌜i ∉ I⌝ ∗
      1:[Prvar (synty_to_inhab x) i].
  Proof.
    rewrite proph_ctx_unseal proph_tok_unseal. iIntros (?) "?".
    iInv prophN as (S) ">[[%L[% %sim]] ●]".
    case (exist_fresh (I ∪ dom (S X)))=>
      i /not_elem_of_union[? /not_elem_of_dom nin].
    set ξ := Prvar (synty_to_inhab x) i. set S' := add_line ξ (fitem 1) S.
    iMod (own_update _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "●") as "[● ?]".
    { by apply auth_update_alloc,
        discrete_fun_insert_local_update, alloc_singleton_local_update. }
    iModIntro. iSplitL "●"; last first. { iModIntro. iExists i. by iFrame. }
    iModIntro. iExists S'. iFrame "●". iPureIntro. exists L.
    split; by [|apply add_line_fitem_sim].
  Qed.

  (** Lemmas for [proph_resolve] *)
  Local Lemma proph_tok_out {S L ξ q} :
    S :~ L → proph_smry_tok S -∗ q:[ξ] -∗ ⌜ξ ∉ pl_vars L⌝.
  Proof.
    rewrite proph_tok_unseal=> sim. iIntros "● ξ".
    iDestruct (own_valid_2 with "● ξ") as %val. iPureIntro.
    move=> /(elem_of_list_fmap_2 pli_var) [[[X ?]?][? /sim eqv]]. simpl in *.
    subst. move: val=> /auth_both_valid_discrete[inc _].
    move/(discrete_fun_included_spec_1 _ _ X) in inc.
    rewrite /line discrete_fun_lookup_singleton /= in inc. move: eqv.
    move: inc=> /singleton_included_l[?[-> inc]] eqv. apply (inj Some) in eqv.
    move: inc. by rewrite eqv=> /Some_csum_included [|[[?[?[_[?]]]]|[?[?[?]]]]].
  Qed.
  Local Lemma proph_tok_ne {ξ η q} : 1:[ξ] -∗ q:[η] -∗ ⌜ξ ≠ η⌝.
  Proof.
    rewrite proph_tok_unseal. iIntros "ξ η".
    iDestruct (own_valid_2 with "ξ η") as %val. iPureIntro=> ?. subst.
    move: val. rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
      discrete_fun_singleton_valid singleton_op singleton_valid -Cinl_op
      Cinl_valid.
    apply exclusive_l, _.
  Qed.
  Local Lemma proph_resolve_obs {S ξ aπ} :
    proph_smry_tok S -∗ 1:[ξ] ==∗
      proph_smry_tok (add_line ξ (aitem aπ) S) ∗ ⟨π, π ξ = aπ π⟩.
  Proof.
    rewrite proph_tok_unseal. iIntros "● ξ".
    iMod (own_update_2 with "● ξ") as "[$ ?]".
    { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any=> ? _.
      by apply exclusive_local_update. }
    iModIntro. rewrite proph_obs_unseal. iExists [.{ξ := aπ}].
    rewrite big_sepL_singleton. iSplitR; [|done]. iPureIntro=> ? sat.
    by inversion sat.
  Qed.
  (** Resolve a prophecy *)
  Lemma proph_resolve E ξ aπ ηl q : ↑prophN ⊆ E → aπ ./ ηl →
    proph_ctx -∗ 1:[ξ] -∗ q:∗[ηl] ={E}=∗ ⟨π, π ξ = aπ π⟩ ∗ q:∗[ηl].
  Proof.
    iIntros (? dep) "? ξ ηl". rewrite proph_ctx_unseal.
    iInv prophN as (S) ">[[%L[% %sim]] ●]".
    iDestruct (proph_tok_out with "● ξ") as %?; [done|].
    set L' := .{ξ := aπ} :: L.
    iAssert ⌜∀η, η ∈ ηl → η ∉ pl_vars L'⌝%I as %outηl.
    { iIntros (? el).
      iDestruct (big_sepL_elem_of with "ηl") as "η"; [apply el|].
      iDestruct (proph_tok_ne with "ξ η") as %?.
      iDestruct (proph_tok_out with "● η") as %?; [done|].
      by rewrite not_elem_of_cons. }
    iFrame "ηl". iMod (proph_resolve_obs with "● ξ") as "[● $]". iModIntro.
    iSplitL; [|done]. iExists _. iFrame "●". iPureIntro. exists L'.
    split; [|by apply add_line_aitem_sim].
    split; [done|split; [|done]]=> ?? eqv. apply dep=> ? /outηl ?. by apply eqv.
  Qed.

  (** Get a satisfiability from a prophecy observation *)
  Lemma proph_obs_sat {E φπ} :
    ↑prophN ⊆ E → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ ⌜∃ π, φπ π⌝.
  Proof.
    rewrite proph_ctx_unseal proph_obs_unseal. iIntros "% ? [%L'[%Toφπ #L']]".
    iInv prophN as (S) ">[[%L[%Lval %sim]] ●]".
    move: (Lval)=> /proph_valid_sat[π /Forall_forall sat]. iModIntro.
    iAssert ⌜π ◁ L'⌝%I as %?; last first.
    { iSplitL; last first. { iPureIntro. exists π. by apply Toφπ. }
      iModIntro. iExists S. iFrame "●". iPureIntro. by exists L. }
    rewrite /proph_sat Forall_forall. iIntros ([ξ aπ] el)=>/=.
    iAssert (proph_aobs .{ξ := aπ}) with "[L']" as "ξvπ".
    { iApply big_sepL_elem_of; by [apply el|]. }
    iDestruct (own_valid_2 with "● ξvπ") as %val. iPureIntro.
    move: val=> /auth_both_valid_discrete [inc val].
    apply (sat .{ξ := aπ}), sim.
    move/(discrete_fun_included_spec_1 _ _ ξ.(aprvar_ty)) in inc.
    rewrite /line discrete_fun_lookup_singleton in inc.
    move: inc=> /singleton_included_l[it[eqv /Some_included[->|inc]]]; [done|].
    rewrite eqv. constructor.
    apply (lookup_valid_Some _ ξ.(prvar_id) it) in val; [|done]. move: val.
    move: inc=> /csum_included [->|[[?[?[?]]]|[?[?[eq[->inc]]]]]]; [done|done|].
    move=> val. move: inc. move: val=> /Cinr_valid/to_agree_uninj [?<-].
    inversion eq. by move/to_agree_included <-.
  Qed.
  Lemma proph_obs_false E φπ :
    ↑prophN ⊆ E → (∀π, ¬ φπ π) → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ False.
  Proof.
    iIntros (? neg) "C obs".
    iMod (proph_obs_sat with "C obs") as %[? ex]; [done|].
    by apply neg in ex.
  Qed.
End lemmas.

(** ** Prophecy equalizer *)

(** Prophecy equalizer, an ability to get [⟨π, aπ π = bπ π⟩]
  after getting dependent prophecy tokens *)
Definition proph_eqz `{!prophGS TY Σ, !invGS_gen hlc Σ} {A}
  (aπ bπ : proph TY A) : iProp Σ :=
  ∀ E ξl q, ⌜↑prophN ⊆ E⌝ -∗ ⌜bπ ./ ξl⌝ -∗
    q:∗[ξl] ={E}=∗ ⟨π, aπ π = bπ π⟩ ∗ q:∗[ξl].

Notation "aπ :== bπ" := (proph_eqz aπ bπ)
  (at level 70, format "aπ  :==  bπ") : bi_scope.

Section proph_eqz.
  Context `{!prophGS TY Σ, !invGS_gen hlc Σ}.

  (** Construct an equalizer from a token *)
  Lemma proph_eqz_token ξ aπ : proph_ctx -∗ 1:[ξ] -∗ (.$ ξ) :== aπ.
  Proof.
    iIntros "C ξ" (?????) "ξl". by iMod (proph_resolve with "C ξ ξl").
  Qed.
  (** Construct an equalizer from an observation *)
  Lemma proph_eqz_obs {A} (aπ bπ : proph _ A) : ⟨π, aπ π = bπ π⟩ -∗ aπ :== bπ.
  Proof. iIntros "?" (?????) "? !>". iFrame. Qed.
  Lemma proph_eqz_refl {A} (aπ : proph _ A) : ⊢ aπ :== aπ.
  Proof. iApply proph_eqz_obs. by iApply proph_obs_true. Qed.

  (** Modify an equalizer with an observation *)
  Lemma proph_eqz_modify {A} (aπ bπ cπ : proph _ A) :
    ⟨π, aπ π = bπ π⟩ -∗ aπ :== cπ -∗ bπ :== cπ.
  Proof.
    iIntros "obs eqz" (?????) "ξl".
    iMod ("eqz" with "[//] [//] ξl") as "[obs' $]". iModIntro.
    iCombine "obs obs'" as "?". iStopProof. by f_equiv=> ?[->->].
  Qed.

  (** Construct a prophecy equalizer from injective functions *)
  Lemma proph_eqz_constr {A B} f `{!@Inj A B (=) (=) f} aπ bπ :
    aπ :== bπ -∗ (λ π, f (aπ π)) :== (λ π, f (bπ π)).
  Proof.
    iIntros "eqz" (???? dep) "ξl". move/proph_dep_destr in dep.
    iMod ("eqz" with "[//] [//] ξl") as "[? $]". iModIntro. iStopProof.
    by f_equiv=> ?->.
  Qed.
  Lemma proph_eqz_constr2 {A B C} f
    `{!@Inj2 A B C (=) (=) (=) f} aπ aπ' bπ bπ' :
    aπ :== aπ' -∗ bπ :== bπ' -∗
    (λ π, f (aπ π) (bπ π)) :== (λ π, f (aπ' π) (bπ' π)).
  Proof.
    iIntros "eqz eqz'" (???? dep) "ξl". move: dep=> /proph_dep_destr2[??].
    iMod ("eqz" with "[//] [//] ξl") as "[obs ξl]".
    iMod ("eqz'" with "[//] [//] ξl") as "[obs' $]". iModIntro.
    iCombine "obs obs'" as "?". iStopProof. by f_equiv=>/= ?[->->].
  Qed.
End proph_eqz.
