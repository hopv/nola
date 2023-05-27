(** * Weakest precondition *)

From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.bi Require Import fixpoint.
From iris.proofmode Require Import tactics.

Local Transparent iris_invGS.
Local Notation wp_unseal := iris.program_logic.weakestpre.wp_aux.(seal_eq).
Local Notation twp_unseal :=
  iris.program_logic.total_weakestpre.twp_aux.(seal_eq).
Local Notation twp_pre' := iris.program_logic.total_weakestpre.twp_pre'.

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
  Local Notation twpx Φ monoΦ := (@twp' _ _ _ (IrG Φ monoΦ)).

  Lemma wp_ne_interp {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {n monoΦ monoΨ} :
    Φ ≡{n}≡ Ψ → (wpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ wpx Ψ monoΨ.
  Proof.
    move=> ΦΨ. rewrite /wp' wp_unseal=> ?. apply fixpoint_ne=> ????.
    unfold wp_pre=>/=. do 12 f_equiv; [by apply ΦΨ|]. do 13 f_equiv.
    apply step_fupdN_ne. do 2 f_equiv. apply ΦΨ.
  Qed.
  Lemma wp_proper_interp {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {monoΦ monoΨ} :
    Φ ≡ Ψ → (wpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡ wpx Ψ monoΨ.
  Proof. rewrite !equiv_dist=> ??. by apply wp_ne_interp. Qed.

  Lemma twp_ne_interp {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {n monoΦ monoΨ} :
    Φ ≡{n}≡ Ψ → (twpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ twpx Ψ monoΨ.
  Proof.
    move=> ΦΨ. rewrite /twp' twp_unseal=> ????.
    apply least_fixpoint_ne; [|done]=> ?[[??]?]. rewrite /twp_pre'/twp_pre/=.
    do 10 f_equiv; [by apply ΦΨ|]. do 14 f_equiv. apply ΦΨ.
  Qed.
  Lemma twp_proper_interp {Φ Ψ : _ -d> _ -d> _ -d> _ -d> _} {monoΦ monoΨ} :
    Φ ≡ Ψ → (twpx Φ monoΦ : _ -d> _ -d> _ -d> _ -d> _) ≡ twpx Ψ monoΨ.
  Proof. rewrite !equiv_dist=> ??. by apply twp_ne_interp. Qed.
End wp.
