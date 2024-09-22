(** * Basic utility *)

From nola Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.

Implicit Type PROP : bi.

Section util.
  Context {PROP}.

  (** ** On [∗-∗] *)

  #[export] Instance wand_iff_comm : Comm (⊣⊢) (@bi_wand_iff PROP).
  Proof. move=> ??. by rewrite /bi_wand_iff comm. Qed.

  (** ** On [step_fupdN] *)

  (** [step_fupdN] is non-expansive *)
  Lemma step_fupdN_ne `{!BiFUpd PROP} {n E E' k} {P Q : PROP} :
    P ≡{n}≡ Q → (|={E}[E']▷=>^k P)%I ≡{n}≡ (|={E}[E']▷=>^k Q)%I.
  Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
  Lemma step_fupdN_proper `{!BiFUpd PROP} {E E' k} {P Q : PROP} :
    P ⊣⊢ Q → (|={E}[E']▷=>^k P) ⊣⊢ |={E}[E']▷=>^k Q.
  Proof.
    move=> PQ. apply equiv_dist=> n. apply step_fupdN_ne. by rewrite PQ.
  Qed.
End util.

(** Adding [◇] inside lets [M] absorb [◇] for introduceable [M] *)
Lemma is_except_0_intro {PROP} {M : PROP → PROP} {P} :
  (∀ P, P ⊢ M P) → IsExcept0 (M (◇ P))%I.
Proof.
  rewrite /IsExcept0 /bi_except_0=> intro. iIntros "[?|$]". iApply intro.
  by iLeft.
Qed.
