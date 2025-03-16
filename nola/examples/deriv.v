(** * Derivability *)

From nola.examples Require Export con.
From nola.lrust Require Export notation proofmode.
Import ModwNotation WpwNotation CsemNotation LftNotation.

Section deriv.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !inv'GS (cifOF CON) Σ, !invC CON, !iffJ (cifO CON Σ) JUDG,
    !invCS CON JUDG Σ, !iffJS (cifOF CON) JUDG Σ, !borrowGS (cifOF CON) Σ,
    !bor_tokC CON, !bor_tokCS CON JUDG Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ).

  (** ** On derivability *)

  (** [inv'] is persistent *)
  #[export] Instance inv'_persistent `{!Deriv ih δ} {N Px} :
    Persistent (inv' δ N Px).
  Proof. exact _. Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' `{!Deriv ih δ} {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    iIntros "$". iApply Deriv_factor. iIntros. rewrite in_js. iModIntro.
    iSplit; by iIntros.
  Qed.

  (** Allocate a relaxed invariant *)
  Lemma inv'_alloc `{!Deriv ih δ} {N Px} : ⟦ Px ⟧ᶜ =[inv_wsat ⟦⟧ᶜ]=∗ inv' δ N Px.
  Proof. rewrite -inv_tok_inv'. exact: inv_tok_alloc. Qed.

  (** Access the body of a relaxed invariant *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      ⟦ Px ⟧ᶜ ∗ (⟦ Px ⟧ᶜ =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "[%Qx[#PQ i]]". iDestruct (der_sound with "PQ") as "{PQ}PQ".
    iMod (inv_tok_acc with "i") as "[Qx cl]"; [done|]. rewrite in_js /=.
    iDestruct ("PQ" with "Qx") as "$". iIntros "!> Px". iApply "cl".
    by iApply "PQ".
  Qed.
  (** Access the body of a relaxed invariant via a view shift *)
  Lemma invd_acc_vs {N Px E Q R} : ↑N ⊆ E →
    □ (⟦ Px ⟧ᶜ -∗ Q =[inv_wsat ⟦⟧ᶜ]{E∖↑N}=∗ ⟦ Px ⟧ᶜ ∗ R) -∗
      □ (invd N Px -∗ Q =[inv_wsat ⟦⟧ᶜ]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (invd_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.
  (** Access the body of a relaxed invariant via a total Hoare triple *)
  Lemma invd_acc_twp {N Px E Q Ψ} `{!Atomic (stuckness_to_atomicity s) e} :
    ↑N ⊆ E → to_val e = None →
    [[{ ⟦ Px ⟧ᶜ ∗ Q }]][inv_wsat ⟦⟧ᶜ] e @ s; E∖↑N
    [[{ v, RET v; ⟦ Px ⟧ᶜ ∗ Ψ v }]] -∗
      [[{ invd N Px ∗ Q }]][inv_wsat ⟦⟧ᶜ] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (invd_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** General rule for semantic alteration of relaxed invariants *)
  Lemma inv'_iff `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧ᶜ(δ') ∗-∗ ⟦ Qx ⟧ᶜ(δ')) -∗
      inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    iIntros "#iff [%Rx[PR i]]". iExists Rx. iFrame "i".
    iApply Deriv_map; [|done]. iIntros (????). rewrite !in_js /=.
    iIntros "#[PR RP] !>". iSplit.
    - iIntros "Qx". iApply "PR". by iApply "iff".
    - iIntros "Rx". iApply "iff"; [done..|]. by iApply "RP".
  Qed.
  Lemma inv'_iff' `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧ᶜ(δ') ∗-∗ ⟦ Qx ⟧ᶜ(δ')) -∗
      inv' δ N Px ∗-∗ inv' δ N Qx.
  Proof.
    iIntros "#iff". iSplit; iApply inv'_iff; [done|]. iIntros "!>" (????).
    rewrite bi.wand_iff_sym. by iApply "iff".
  Qed.

  (** Derived semantic alteration of relaxed invariants *)
  Local Lemma inv'_sep_comm' `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite bi.sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_sep_comm `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊣⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof. apply bi.equiv_entails. split; exact inv'_sep_comm'. Qed.
  Local Lemma inv'_inv'_sep_comm' `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite !sem_cif_in /=.
    rewrite inv'_sep_comm. iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_inv'_sep_comm `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv N' (Px ∗ Qx)) ⊣⊢ inv' δ N (cif_inv N' (Qx ∗ Px)).
  Proof. apply bi.equiv_entails. split; exact inv'_inv'_sep_comm'. Qed.
  Local Lemma inv'_bor_lft' `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗
      inv' δ N (cif_bor_tok α Px) -∗ inv' δ N (cif_bor_tok β Px).
  Proof.
    iIntros "#? #?". iApply inv'_iff. iIntros "!>" (????).
    rewrite /= !sem_cif_in /=. iSplit; by iApply bor_tok_lft.
  Qed.
  Lemma inv'_bor_lft `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗
      inv' δ N (cif_bor_tok α Px) ∗-∗ inv' δ N (cif_bor_tok β Px).
  Proof. iIntros "#? #?". iSplit; by iApply inv'_bor_lft'. Qed.
End deriv.
