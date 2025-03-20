(** * Basic examples *)

From nola.examples Require Export con.
From nola.lrust Require Export notation proofmode.
Import ModwNotation WpwNotation CsemNotation.

(** Vacuous loop of [n] steps *)
Definition just_loop : val := rec: "self" ["n"] :=
  if:: "n" > #0 then "self" ["n" - #1].

(** Loop decrementing the value of a location *)
Definition decr_loop : val := rec: "self" ["l"] :=
  if:: !"l" > #0 then "l" <- !"l" - #1;; "self" ["l"].

Section basic.
  Context `{!lrustGS_gen hlc Σ}.

  (** [just_loop] terminates for any [n] *)
  Lemma twp_just_loop {W E} {n : nat} :
    [[{ True }]][W] just_loop [ #n] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (?) "_ →Φ".
    iInduction n as [|n] "IH"; wp_rec; wp_op; wp_case; [by iApply "→Φ"|].
    wp_op. have ->: (S n - 1)%Z = n by lia. by iApply "IH".
  Qed.

  (** [just_loop] called with a non-deterministic input *)
  Lemma twp_just_loop_nd {W E} :
    [[{ True }]][W] just_loop [Ndnat] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (?) "_ →Φ". wp_apply twp_ndnat=>//. iIntros (?) "_".
    by wp_apply twp_just_loop.
  Qed.

  (** [decr_loop] terminates for any [n] *)
  Lemma twp_decr_loop {W E l} {n : nat} :
    [[{ l ↦ #n }]][W] decr_loop [ #l] @ E [[{ RET #☠; l ↦ #0 }]].
  Proof.
    iIntros (?) "↦ →Φ".
    iInduction n as [|n] "IH"; wp_rec; wp_read; wp_op; wp_case;
      [by iApply "→Φ"|].
    wp_read. wp_op. wp_write. have ->: (S n - 1)%Z = n by lia.
    iApply ("IH" with "↦ →Φ").
  Qed.

  (** [decr_loop] called with non-deterministic initialization *)
  Lemma twp_decr_loop_nd {W E l v} :
    [[{ l ↦ v }]][W] #l <- Ndnat;; decr_loop [ #l] @ E [[{ RET #☠; l ↦ #0 }]].
  Proof.
    iIntros (?) "↦ →Φ". wp_apply twp_ndnat=>//. iIntros (?) "_". wp_write.
    wp_apply (twp_decr_loop with "↦ →Φ").
  Qed.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !inv'GS (cifOF CON) Σ,
    !inv_tokC CON, !inv_tokCS CON JUDG Σ}.

  (** [just_loop] called with a value taken from an invariant *)
  Lemma twp_just_loop_inv {N E l} : ↑N ⊆ E →
    [[{ inv_tok N (∃ n : nat, ▷ l ↦ #n)%cif }]][inv_wsat ⟦⟧ᶜ]
      just_loop [!ˢᶜ #l] @ E [[{ RET #☠; True }]].
  Proof.
    iIntros (??) "#i →Φ". wp_bind (!ˢᶜ _)%E.
    iMod (inv_tok_acc with "i") as "/=[[% >↦] cl]"=>//. wp_read.
    iMod ("cl" with "[$↦]"). iModIntro. by wp_apply twp_just_loop.
  Qed.

  (** [decr_loop] called with a value taken from an invariant *)
  Lemma twp_decr_loop_inv {N E l l' v} : ↑N ⊆ E →
    [[{ inv_tok N (∃ n : nat, ▷ l' ↦ #n)%cif ∗ l ↦ v }]][inv_wsat ⟦⟧ᶜ]
      #l <- !ˢᶜ #l';; decr_loop [ #l] @ E [[{ RET #☠; l ↦ #0 }]].
  Proof.
    iIntros (??) "[#i ↦] →Φ". wp_bind (!ˢᶜ _)%E.
    iMod (inv_tok_acc with "i") as "/=[[% >↦'] cl]"=>//. wp_read.
    iMod ("cl" with "[$↦']"). iModIntro. wp_write.
    wp_apply (twp_decr_loop with "↦ →Φ").
  Qed.
End basic.
