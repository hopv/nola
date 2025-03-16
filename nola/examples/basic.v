(** * Basic examples *)

From nola.examples Require Export con.
From nola.lrust Require Export notation proofmode.
Import ModwNotation WpwNotation CsemNotation.

(** Vacuous loop of [n] steps *)
Definition just_loop : val := rec: "self" ["n"] :=
  if:: "n" > #0 then "self" ["n" - #1].

Section basic.
  Context `{!lrustGS_gen hlc Σ}.

  (** [just_loop] terminates for any non-negative [n] *)
  Lemma twp_just_loop {W E} {n : nat} :
    [[{ True }]][W] just_loop [ #n] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (?) "_ →Φ".
    iInduction n as [|n] "IH"; wp_rec; wp_op; wp_case; [by iApply "→Φ"|].
    wp_op. have ->: (S n - 1)%Z = n by lia. by iApply "IH".
  Qed.

  (** [just_loop] called with [Ndnat] *)
  Lemma twp_just_loop_nd {W E} :
    [[{ True }]][W] just_loop [Ndnat] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (?) "_ →Φ". wp_apply twp_ndnat=>//. iIntros (?) "_".
    by wp_apply twp_just_loop.
  Qed.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !inv'GS (cifOF CON) Σ,
    !inv_tokC CON, !inv_tokCS CON JUDG Σ}.

  (** [just_loop] called with a value taken from an invariant *)
  Lemma twp_just_loop_inv {N E l} : ↑N ⊆ E →
    [[{ inv_tok N (∃ n : nat, ▷ l ↦ #n)%cif }]][inv_wsat ⟦⟧ᶜ]
      just_loop [(!ˢᶜ#l)] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (??) "#i →Φ". wp_bind (!ˢᶜ_)%E.
    iMod (inv_tok_acc with "i") as "/=[[% >↦] cl]"=>//. wp_read.
    iMod ("cl" with "[$↦]"). iModIntro. by wp_apply twp_just_loop.
  Qed.
End basic.
