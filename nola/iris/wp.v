(** * Weakest precondition *)

From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.

Local Transparent iris_invGS.
Local Notation wp_unseal := iris.program_logic.weakestpre.wp_aux.(seal_eq).

Section fupd.
  Context `{!BiFUpd PROP}.
  Open Scope bi_scope.

  Lemma step_fupdN_ne {n Eo Ei k} {P Q : PROP} :
    P ≡{n}≡ Q → (|={Eo}[Ei]▷=>^k P) ≡{n}≡ (|={Eo}[Ei]▷=>^k Q).
  Proof. move=> PQ. by elim k; [done|]=>/= ? ->. Qed.
End fupd.

Section wp.
  Context `{!invGS_gen hlc Σ} {Λ : language}
    {fp : val Λ → iProp Σ} {nl : nat → nat}.

  Local Notation IrG Φ monoΦ := (IrisG _ Φ fp nl monoΦ).
  Local Notation wpx Φ monoΦ := (@wp' _ _ _ (IrG Φ monoΦ)).

  Lemma wpx_ne {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {n monoΦ monoΨ} :
    Φ ≡{n}≡ Ψ → (wpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ wpx Ψ monoΨ.
  Proof.
    move=> ΦΨ. rewrite /wp' wp_unseal=> ?. apply fixpoint_ne=> ????.
    unfold wp_pre=>/=. do 12 f_equiv; [by apply ΦΨ|]. do 13 f_equiv.
    apply step_fupdN_ne. do 2 f_equiv. apply ΦΨ.
  Qed.
  Lemma wpx_proper {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {monoΦ monoΨ} :
    Φ ≡ Ψ → (wpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡ wpx Ψ monoΨ.
  Proof. rewrite !equiv_dist=> ??. by apply wpx_ne. Qed.
End wp.
