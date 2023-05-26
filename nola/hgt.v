(** * [hgt]: General height of a tree *)

From nola Require Export prelude.
Import EqNotations.

(** [hgt]: General height of a tree *)
Inductive hgt : Type := Hgtᶠ {
  hgt_dom : Type;
  hgt_kids :> hgt_dom → hgt;
}.
Arguments Hgtᶠ {A} hs : rename.
Add Printing Constructor hgt.

Definition Hgt₀ : hgt := Hgtᶠ (λ e : Empty_set, match e with end).
Definition Hgt₁ (h : hgt) : hgt := Hgtᶠ (λ _ : nat, h).
Definition Hgt₂ (h₀ h₁ : hgt) : hgt :=
  Hgtᶠ (λ n, match n with 0 => h₀ | _ => h₁ end).
Definition Hgt₃ (h₀ h₁ h₂ : hgt) : hgt :=
  Hgtᶠ (λ n, match n with 0 => h₀ | 1 => h₁ | _ => h₂ end).

(** [hgt] is a set *)

(** [hAcc]: Accessibility on [hgt] *)
Inductive hAcc (h : hgt) : Prop := HAcc {
  hateq : ∀ h' a, h' = h a → hAcc h'
}.
Arguments HAcc {h} _.
Arguments hateq {h} H {h'} a : rename.
Add Printing Constructor hAcc.

(** Destruct [hAcc] *)
Notation "H ‼ʰ[ eq ] a" := (H.(hateq) a eq) (at level 20, no associativity)
  : nola_scope.
Notation hat H a := (H ‼ʰ[ eq_refl ] a).
Infix "‼ʰ" := hat (at level 20, no associativity) : nola_scope.

(** [hwf]: [hAcc h] for all [h : hgt] *)
Fixpoint hwf {h} : hAcc h := HAcc (λ _ _ eq, rew eq_sym eq in hwf).

(** Simplify [rew eq_sym … in hwf] *)
Lemma rew_eq_hwf {h h'} (eq : h' = h) : rew[hAcc] eq_sym eq in hwf = hwf.
Proof. by subst. Qed.

(** Under functional extensionality *)
From nola Require Import util.funext.

(** The only value of [hAcc h] is [hwf] *)
Lemma eq_hwf {h} (H : hAcc h) : H = hwf.
Proof.
  move: h H. fix FIX 1=> [[??]][?]/=. f_equal. do 3 funext=>/= ?. by subst.
Qed.
Lemma eq_hacc {h} (H H' : hAcc h) : H = H'.
Proof. by rewrite (eq_hwf H) (eq_hwf H'). Qed.
