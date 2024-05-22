(** * Showcase logic *)

From nola.util Require Import fn cit.
From nola.bi Require Import ofe.
From nola.iris Require Import ofe inv.
From nola.heap_lang Require Import notation proofmode.
Import WpwNotation iPropAppNotation.

Implicit Type (N : namespace) (l : loc).

(** ** [binsel]: Binary operator selector *)
Variant binsel :=
| (** Conjunction *) s_and
| (** Disjunction *) s_or
| (** Implication *) s_imp
| (** Separating conjunction *) s_sep
| (** Magic wand *) s_wand.

(** ** [unsel]: Unary operator selector *)
Variant unsel :=
| (** Plainly *) s_plain
| (** Persistently *) s_pers
| (** Basic update *) s_bupd.

(** ** [sel]: Selector *)
Variant sel :=
| (** Universal quantifier *) s_all (A : Type)
| (** Existential quantifier *) s_ex (A : Type)
| (** Binary operator *) s_bin (s : binsel)
| (** Unary operator *) s_un (s : unsel)
| (** Pure proposition *) s_pure
| (** Later *) s_later
| (** Invariant *) s_inv (N : namespace).
Coercion s_bin : binsel >-> sel.
Coercion s_un : unsel >-> sel.

(** ** [idom]: Domain for inductive parts *)
Definition idom (s : sel) : Type := match s with
  | s_all A | s_ex A => A | s_bin _ => bool | s_un _ => unit
  | _ => Empty_set
  end.

(** ** [cdom]: Domain for coinductive parts *)
Definition cdom (s : sel) : Type := match s with
  | s_inv _ => unit
  | _ => Empty_set
  end.

(** ** [dataOF]: Data [oFunctor] *)
Definition dataOF (s : sel) : oFunctor := match s with
  | s_pure => PropO
  | s_later => laterOF ∙
  | _ => unitO
  end.

(** [dataOF] is contractive *)
#[export] Instance dataOF_contractive {s} : oFunctorContractive (dataOF s).
Proof. case s=>/=; exact _. Qed.

Definition nPropOF : oFunctor := citOF idom cdom dataOF.
Definition nProp Σ : Type := cit idom cdom (λ s, dataOF s $oi Σ).

Section nProp.
  Context {Σ : gFunctors}.
  Implicit Type Px Qx : nProp Σ.
  Definition n_all {A} (Φxs : A → nProp Σ) : nProp Σ :=
    CitX (s_all A) Φxs nullary ().
  Definition n_ex {A} (Φxs : A → nProp Σ) : nProp Σ :=
    CitX (s_ex A) Φxs nullary ().
  Definition n_bin s Px Qx : nProp Σ :=
    CitX (s_bin s) (binary Px Qx) nullary ().
  Definition n_and := n_bin s_and.
  Definition n_or := n_bin s_or.
  Definition n_imp := n_bin s_imp.
  Definition n_sep := n_bin s_sep.
  Definition n_wand := n_bin s_wand.
  Definition n_un s Px : nProp Σ := CitX (s_un s) (unary Px) nullary ().
  Definition n_plain := n_un s_plain.
  Definition n_pers := n_un s_pers.
  Definition n_bupd := n_un s_bupd.
  Definition n_pure (φ : Prop) : nProp Σ := CitX s_pure nullary nullary φ.
  Definition n_later (P : iProp Σ) : nProp Σ :=
    CitX s_later nullary nullary (Next P%I).
  Definition n_inv N Px : nProp Σ :=
    CitX (s_inv N) nullary (unary Px) ().
End nProp.

Declare Scope nProp_scope.
Delimit Scope nProp_scope with n.
Bind Scope nProp_scope with nProp.
Notation "∀ x .. y , Px" :=
  (n_all (λ x, .. (n_all (λ y, Px%n)) ..)) : nProp_scope.
Notation "∃ x .. y , Px" :=
  (n_ex (λ x, .. (n_ex (λ y, Px%n)) ..)) : nProp_scope.
Infix "→" := n_imp : nProp_scope.
Infix "∗" := n_sep : nProp_scope.
Infix "-∗" := n_wand : nProp_scope.
Notation "■ Px" := (n_plain Px) : nProp_scope.
Notation "□ Px" := (n_pers Px) : nProp_scope.
Notation "|==> Px" := (n_bupd Px) : nProp_scope.
Notation "⌜ φ ⌝" := (n_pure φ).
Notation "▷ P" := (n_later P).

Section iris.
  Context `{!inv'GS nPropOF Σ}.

  (** ** [bintp]: Base interpretation *)
  Definition bintp s : (idom s -d> iProp Σ) → (cdom s -d> nProp Σ) →
    dataOF s $oi Σ → iProp Σ :=
    match s with
    | s_all _ => λ Ps _ _, ∀ a, Ps a
    | s_ex _ => λ Ps _ _, ∃ a, Ps a
    | s_bin s => λ Ps _ _, let P := Ps true in let Q := Ps false in
        match s with
        | s_and => P ∧ Q | s_or => P ∨ Q | s_imp => P → Q
        | s_sep => P ∗ Q | s_wand => P -∗ Q
        end
    | s_un s => λ Ps _ _, let P := Ps () in
        match s with
        | s_plain => ■ P | s_pers => □ P | s_bupd => |==> P
        end
    | s_pure => λ _ _ φ, ⌜φ⌝
    | s_inv N => λ _ Pxs _, inv_tok N (Pxs ())
    | s_later => λ _ _, laterl
    end%I.

  (** [bintp] is non-expansive *)
  #[export] Instance bintp_ne {s} : NonExpansive3 (bintp s).
  Proof.
    case s=>/=; try solve_proper.
    - move=> ???????. by apply laterl_ne.
    - move=> ??????? eqv ???. f_equiv. apply eqv.
  Qed.

  (** ** [intp]: Interpretation of [nPropOF] *)
  Definition intp : nProp Σ → iProp Σ := cit_intp bintp.

  (** [intp] is non-expansive *)
  Fact intp_ne : NonExpansive intp.
  Proof. exact _. Qed.
End iris.

(** ** Target function: Linked list mutation *)
Definition iter : val := rec: "self" "f" "c" "l" :=
  if: !"c" = #0 then #() else
    "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (!("l" +ₗ #1)).

Section iris.
  Context `{!inv'GS nPropOF Σ, !heapGS_gen hlc Σ}.

  Section ilist.
    Context N (Φ : loc → nProp Σ).

    (** [ilist]: Proposition for a syntactic list *)
    Definition ilist_gen Ilist' l : nProp Σ :=
      n_inv N (Φ l) ∗ n_inv N (Ilist' l).
    Definition ilist'_gen Ilist' l : nProp Σ :=
      ∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ ilist_gen Ilist' l'.
    CoFixpoint ilist' : loc → nProp Σ := ilist'_gen ilist'.
    Definition ilist : loc → nProp Σ := ilist_gen ilist'.
  End ilist.

  (** ** Termination of [iter] *)
  Lemma twp_iter {N Φ c l} {f : val} {n : nat} :
    (∀ l0 : loc,
      [[{ inv_tok N (Φ l0) }]][inv_wsat intp]
        f #l0 @ ↑N
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ intp (ilist N Φ l) }]][inv_wsat intp]
      iter f #c #l @ ↑N
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "#Hf". iIntros (Ψ) "!> [c↦ #[ihd itl]]/= HΨ".
    iInduction n as [|m] "IH" forall (l) "ihd itl".
    { wp_rec. wp_pures. wp_load. wp_pures. by iApply "HΨ". }
    wp_rec. wp_pures. wp_load. wp_pures. wp_apply "Hf"; [done|]. iIntros "_".
    wp_pures. wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    wp_op. wp_bind (! _)%E.
    iMod (inv_tok_acc (PROP:=nPropOF) (intp:=intp) with "itl") as
      "/=[(%l' & >↦l' & #itlhd & #itltl) cl]/="; [done|].
    wp_load. iModIntro. iMod ("cl" with "[↦l']") as "_".
    { iExists _. iFrame "↦l'". by iSplit. }
    iModIntro. by iApply ("IH" with "c↦ HΨ").
  Qed.
End iris.
