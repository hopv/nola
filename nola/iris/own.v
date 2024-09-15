(** * Utility for [own] *)

From nola Require Export prelude.
From nola.util Require Import gmap.
From iris.algebra Require Import functions gmap.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

Notation inG_unfold := iris.base_logic.lib.own.inG_unfold.
Notation inG_fold := iris.base_logic.lib.own.inG_fold.
Notation iRes_singleton := iris.base_logic.lib.own.iRes_singleton.
Notation own_def := iris.base_logic.lib.own.own_def.
Notation own_eq := iris.base_logic.lib.own.own_eq.
Notation inG_unfold_fold := iris.base_logic.lib.own.inG_unfold_fold.
Notation inG_fold_unfold := iris.base_logic.lib.own.inG_fold_unfold.

Section own.
  (** [cmra_transport] is [CmraMorphism] *)
  #[export] Instance cmra_transport_cmra_morphism {A B} {H : A = B} :
    CmraMorphism (cmra_transport H).
  Proof. subst. exact _. Qed.

  (** Take out the state for the camera and the ghost name in [iResUR] *)
  Definition iRes_at `{i : !inG Σ A} (γ : gname) (r : iResUR Σ) : option A :=
    cmra_transport (eq_sym inG_prf) ∘ inG_fold <$> r (inG_id i) !! γ.

  (** [iRes_at] is non-expansive *)
  #[export] Instance iRes_at_ne `{i : !inG Σ A} {γ} :
    NonExpansive (iRes_at (i:=i) γ).
  Proof. move=> ? r r' eq. by rewrite /iRes_at (eq (inG_id i)). Qed.
  #[export] Instance iRes_at_proper `{i : !inG Σ A} {γ} :
    Proper ((≡) ==> (≡)) (iRes_at (i:=i) γ).
  Proof. apply ne_proper, _. Qed.

  (** [iRes_at] over [⋅] *)
  Lemma iRes_at_op `{i : !inG Σ A} {γ r r'} :
    iRes_at (i:=i) γ (r ⋅ r') ≡ iRes_at γ r ⋅ iRes_at γ r'.
  Proof.
    rewrite /iRes_at discrete_fun_lookup_op lookup_op.
    move: (r (inG_id i) !! γ) (r' (inG_id i) !! γ)=> [a|][a'|]//=.
    by rewrite -Some_op cmra_morphism_op cmra_transport_op.
  Qed.

  (** [✓] over [iRes_at] *)
  Lemma iRes_at_validN `{i : !inG Σ A} {n γ r} :
    ✓{n} r → ✓{n} iRes_at (i:=i) γ r.
  Proof.
    move=> val. rewrite /iRes_at. apply cmra_morphism_validN; [exact _|].
    apply val.
  Qed.
  Lemma iRes_at_valid `{i : !inG Σ A} {γ r} : ✓ r → ✓ iRes_at (i:=i) γ r.
  Proof.
    move=> /cmra_valid_validN ?. apply cmra_valid_validN=> ?.
    by apply iRes_at_validN.
  Qed.

  (** [iRes_at] over [iRes_singleton] *)
  Lemma iRes_at_singleton `{i : !inG Σ A} {γ a} :
    iRes_at γ (iRes_singleton (i:=i) γ a) ≡ Some a.
  Proof.
    rewrite /iRes_at /iRes_singleton discrete_fun_lookup_singleton.
    rewrite lookup_singleton. case: i=> >. subst=>/=.
    by rewrite inG_fold_unfold.
  Qed.
  (** Adjunction between [iRes_singleton] and [iRes_at] *)
  Lemma iRes_singleton_at_adj_1 `{i : !inG Σ A} {γ a r n} :
    iRes_singleton (i:=i) γ a ≼{n} r → Some a ≼{n} iRes_at γ r.
  Proof.
    move=> [r' eq]. rewrite -(iRes_at_singleton (γ:=γ)). exists (iRes_at γ r').
    rewrite -iRes_at_op. by f_equiv.
  Qed.
  Lemma iRes_singleton_at_adj_2 `{i : !inG Σ A} {γ a r n} :
    Some a ≼{n} iRes_at γ r → iRes_singleton (i:=i) γ a ≼{n} r.
  Proof.
    move=> [oa eq].
    exists (discrete_fun_insert _
      (insdel γ (inG_unfold ∘ cmra_transport inG_prf <$> oa) (r _)) r).
    move=> k. rewrite discrete_fun_lookup_op /iRes_singleton.
    case: (decide (inG_id i = k))=> ?; last first.
    { rewrite discrete_fun_lookup_singleton_ne; [|done].
      rewrite discrete_fun_lookup_insert_ne; [|done]. by rewrite left_id. }
    subst. rewrite discrete_fun_lookup_singleton discrete_fun_lookup_insert.
    move=> γ'. rewrite lookup_op. case: (decide (γ = γ'))=> ?; last first.
    { rewrite lookup_singleton_ne; [|done]. rewrite lookup_insdel_ne; [|done].
      by rewrite left_id. }
    subst. rewrite lookup_singleton lookup_insdel.
    have <- : inG_unfold ∘ cmra_transport inG_prf <$> Some a =
      Some (inG_unfold (cmra_transport inG_prf a)) by done.
    rewrite -cmra_morphism_op -eq /iRes_at.
    case: (r (inG_id i) !! γ'); [|done]=>/= ?. f_equiv.
    by rewrite cmra_transport_trans eq_trans_sym_inv_l /= inG_unfold_fold.
  Qed.
  Lemma iRes_singleton_at_adj `{i : !inG Σ A} {γ a r n} :
    iRes_singleton (i:=i) γ a ≼{n} r ↔ Some a ≼{n} iRes_at γ r.
  Proof.
    split; [exact iRes_singleton_at_adj_1|exact iRes_singleton_at_adj_2].
  Qed.

  (** [uPred_holds] over [own] *)
  Lemma own_uPred_holds `{i : !inG Σ A} {γ a n r} :
    uPred_holds (own γ a) n r ↔ Some a ≼{n} iRes_at (i:=i) γ r.
  Proof.
    rewrite own_eq /own_def. uPred.unseal. apply iRes_singleton_at_adj.
  Qed.
End own.
