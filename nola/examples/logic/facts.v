(** * Facts *)

From nola.examples.logic Require Export deriv.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Fact nintp_pure {κ δ φ} : ⟦ ⌜φ⌝ ⟧{κ}(δ) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Fact nintp_persistently {κ δ P} : ⟦ □ P ⟧{κ}(δ) ⊣⊢ □ ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_plainly {κ δ P} : ⟦ ■ P ⟧{κ}(δ) ⊣⊢ ■ ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_bupd {κ δ P} : ⟦ |==> P ⟧{κ}(δ) ⊣⊢ |==> ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_fupd {κ δ P E E'} :
    ⟦ |={E,E'}=> P ⟧{κ}(δ) ⊣⊢ |={E,E'}=> ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_and {κ δ P Q} : ⟦ P ∧ Q ⟧{κ}(δ) ⊣⊢ ⟦ P ⟧{κ}(δ) ∧ ⟦ Q ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_or {κ δ P Q} : ⟦ P ∨ Q ⟧{κ}(δ) ⊣⊢ ⟦ P ⟧{κ}(δ) ∨ ⟦ Q ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_impl {κ δ P Q} : ⟦ P → Q ⟧{κ}(δ) ⊣⊢ (⟦ P ⟧{κ}(δ) → ⟦ Q ⟧{κ}(δ)).
  Proof. done. Qed.
  Fact nintp_sep {κ δ P Q} : ⟦ P ∗ Q ⟧{κ}(δ) ⊣⊢ ⟦ P ⟧{κ}(δ) ∗ ⟦ Q ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_wand {κ δ P Q} : ⟦ P -∗ Q ⟧{κ}(δ) ⊣⊢ (⟦ P ⟧{κ}(δ) -∗ ⟦ Q ⟧{κ}(δ)).
  Proof. done. Qed.
  Fact nintp_forall {κ δ A Φ} : ⟦ ∀' Φ ⟧{κ}(δ) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_exist {κ δ A Φ} : ⟦ ∃' Φ ⟧{κ}(δ) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_later {κ δ} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(δ) ⊣⊢ ▷ ⟦ P ⟧(δ).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Fact nintp_indir {κ δ} {P : _ (;ᵞ)} : ⟦ ○{nil} P ⟧{κ}(δ) ⊣⊢ ⸨ P ⸩(δ).
  Proof. done. Qed.
  Fact nintp_ag {κ δ γ} {P : _ (;ᵞ)} : ⟦ n_ag γ P ⟧{κ}(δ) ⊣⊢ nag γ P.
  Proof. done. Qed.
  Fact nintp_inv {κ δ N} {P : _ (;ᵞ)} : ⟦ n_inv N P ⟧{κ}(δ) ⊣⊢ nninv δ N P.
  Proof. done. Qed.
  Fact nintp_na_inv {κ δ p N} {P : _ (;ᵞ)} :
    ⟦ n_na_inv p N P ⟧{κ}(δ) ⊣⊢ na_nninv δ p N P.
  Proof. done. Qed.
  Fact nintp_wpw {κ δ W s E e Φ} :
    ⟦ WP[W] e @ s ; E {{ Φ }} ⟧{κ}(δ) ⊣⊢
      WP[⟦ W ⟧(δ)] e @ s ; E {{ v, ⟦ Φ v ⟧(δ) }}.
  Proof. done. Qed.
  Fact nintp_twpw {κ δ W s E e Φ} :
    ⟦ WP[W] e @ s ; E [{ Φ }] ⟧{κ}(δ) ⊣⊢
      WP[⟦ W ⟧(δ)] e @ s ; E [{ v, ⟦ Φ v ⟧(δ) }].
  Proof. done. Qed.
  Fact nintp_n_forall {κ δ V P} : ⟦ ∀: V, P ⟧{κ}(δ) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(δ).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_exist {κ δ V P} : ⟦ ∃: V, P ⟧{κ}(δ) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(δ).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_recs {κ δ A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(δ) ⊣⊢ ⟦ Φ a /: rec:ˢ' Φ ⟧(δ).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_n_recl {δ A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(δ) ⊣⊢ ⟦ Φ a /: rec:ˡ' Φ ⟧(δ).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_subus {δ P} : ⟦ !ᵘˢ P ⟧(δ) ⊣⊢ ⟦ ↑ˡ P ⟧(δ).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.

  (** On [nag] *)
  Lemma nag_agree {γ} {P Q : _ (;ᵞ)} : nag γ P -∗ nag γ Q -∗ ⌜P = Q⌝.
  Proof.
    iIntros "P Q". iCombine "P Q" as "o".
    iDestruct (own_valid with "o") as %v. by apply to_agree_op_valid_L in v.
  Qed.

  Context `{!nderivy ih δ}.
  Implicit Type P Q : nPropL (;ᵞ).

  (** Make connectives go inside the derivability *)
  Fact derivy_and {P Q} :
    ⸨ P ⸩(δ) ∧ ⸨ Q ⸩(δ) -∗ ⸨ P ∧ Q ⸩(δ).
  Proof.
    iIntros "PQ". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    iSplit; iApply "→"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Fact derivy_or {P Q} :
    ⸨ P ⸩(δ) ∨ ⸨ Q ⸩(δ) -∗ ⸨ P ∨ Q ⸩(δ).
  Proof.
    iIntros "[?|?]"; iApply derivy_byintp; iIntros (?? _) "/= #→ _ _";
      [iLeft|iRight]; by iApply "→".
  Qed.
  Fact derivy_forall {A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(δ)) -∗ ⸨ ∀' Φ ⸩(δ).
  Proof.
    iIntros "Φ". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _ %".
    iApply "→". iApply "Φ".
  Qed.
  Fact derivy_exist {A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(δ)) -∗ ⸨ ∃' Φ ⸩(δ).
  Proof.
    iDestruct 1 as (a) "Φ". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    iExists a. iApply "→". iApply "Φ".
  Qed.
  Fact derivy_sep {P Q} :
    ⸨ P ⸩(δ) ∗ ⸨ Q ⸩(δ) -∗ ⸨ P ∗ Q ⸩(δ).
  Proof.
    iIntros "[P Q]". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    iSplitL "P"; by iApply "→".
  Qed.
  Fact derivy_persistently {P} : □ ⸨ P ⸩(δ) -∗ ⸨ □ P ⸩(δ).
  Proof.
    iIntros "#P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _ !>".
    by iApply "→".
  Qed.
  Fact derivy_bupd {P} : (|==> ⸨ P ⸩(δ)) -∗ ⸨ |==> P ⸩(δ).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    by iApply "→".
  Qed.
  Fact derivy_fupd {E E' P} :
    (|={E,E'}=> ⸨ P ⸩(δ)) -∗ ⸨ |={E,E'}=> P ⸩(δ).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    by iApply "→".
  Qed.
  Fact derivy_later {P} : ▷ ⸨ P ⸩(δ) -∗ ⸨ ▷{nil} P ⸩(δ).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    rewrite nintp_fp_nintp. by iApply "→".
  Qed.
  Fact derivy_n_forall {V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(δ)) -∗ ⸨ ∀: V, P ⸩(δ).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _ %".
    rewrite rew_eq_hwf. iApply "→". iApply "P".
  Qed.
  Fact derivy_n_exist {V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(δ)) -∗ ⸨ ∃: V, P ⸩(δ).
  Proof.
    iDestruct 1 as (Φ) "P". iApply derivy_byintp. iIntros (?? _) "/= #→ _ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "→". iApply "P".
  Qed.

  (** Introduce [○] *)
  Fact derivy_indir_intro {P} : ⸨ P ⸩(δ) -∗ ⸨ ○{nil} P ⸩(δ).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (δ' _ _) "/= _ #→δ' _".
    by iApply "→δ'".
  Qed.
End facts.
