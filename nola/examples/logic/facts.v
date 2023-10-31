(** * Facts *)

From nola.examples.logic Require Export deriv.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Fact nintp_pure {κ δ φ} : ⟦ ⌜φ⌝ ⟧{κ}(δ) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Fact nintp_except_0 {κ δ P} : ⟦ ◇ P ⟧{κ}(δ) ⊣⊢ ◇ ⟦ P ⟧{κ}(δ).
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
  Fact nintp_bupdw {κ δ W P} :
    ⟦ |=[W]=> P ⟧{κ}(δ) ⊣⊢ |=[⟦ W ⟧{κ}(δ)]=> ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_fupdw {κ δ W E E' P} :
    ⟦ |=[W]{E,E'}=> P ⟧{κ}(δ) ⊣⊢ |=[⟦ W ⟧{κ}(δ)]{E,E'}=> ⟦ P ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_forall {κ δ A Φ} : ⟦ ∀' Φ ⟧{κ}(δ) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_exist {κ δ A Φ} : ⟦ ∃' Φ ⟧{κ}(δ) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(δ).
  Proof. done. Qed.
  Fact nintp_later {κ δ} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(δ) ⊣⊢ ▷ ⟦ P ⟧(δ).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Fact nintp_indir {κ δ} {P : _ (;ᵞ)} : ⟦ ○{nil} P ⟧{κ}(δ) ⊣⊢ ⸨ P ⸩(δ).
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

  Context `{!nDeriv ih δ}.
  Implicit Type P Q : nPropL (;ᵞ).

  (** Make connectives go inside the derivability *)
  Fact Deriv_and {P Q} :
    ⸨ P ⸩(δ) ∧ ⸨ Q ⸩(δ) -∗ ⸨ P ∧ Q ⸩(δ).
  Proof.
    iIntros "PQ". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    iSplit; iApply "→"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Fact Deriv_or {P Q} :
    ⸨ P ⸩(δ) ∨ ⸨ Q ⸩(δ) -∗ ⸨ P ∨ Q ⸩(δ).
  Proof.
    iIntros "[?|?]"; iApply Deriv_byintp; iIntros (?? _) "/= #→ _";
      [iLeft|iRight]; by iApply "→".
  Qed.
  Fact Deriv_forall {A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(δ)) -∗ ⸨ ∀' Φ ⸩(δ).
  Proof.
    iIntros "Φ". iApply Deriv_byintp. iIntros (?? _) "/= #→ _ %".
    iApply "→". iApply "Φ".
  Qed.
  Fact Deriv_exist {A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(δ)) -∗ ⸨ ∃' Φ ⸩(δ).
  Proof.
    iDestruct 1 as (a) "Φ". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    iExists a. iApply "→". iApply "Φ".
  Qed.
  Fact Deriv_sep {P Q} :
    ⸨ P ⸩(δ) ∗ ⸨ Q ⸩(δ) -∗ ⸨ P ∗ Q ⸩(δ).
  Proof.
    iIntros "[P Q]". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    iSplitL "P"; by iApply "→".
  Qed.
  Fact Deriv_persistently {P} : □ ⸨ P ⸩(δ) -∗ ⸨ □ P ⸩(δ).
  Proof.
    iIntros "#P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _ !>".
    by iApply "→".
  Qed.
  Fact Deriv_bupd {P} : (|==> ⸨ P ⸩(δ)) -∗ ⸨ |==> P ⸩(δ).
  Proof.
    iIntros "P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    by iApply "→".
  Qed.
  Fact Deriv_fupd {E E' P} :
    (|={E,E'}=> ⸨ P ⸩(δ)) -∗ ⸨ |={E,E'}=> P ⸩(δ).
  Proof.
    iIntros "P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    by iApply "→".
  Qed.
  Fact Deriv_later {P} : ▷ ⸨ P ⸩(δ) -∗ ⸨ ▷{nil} P ⸩(δ).
  Proof.
    iIntros "P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    rewrite nintp_fp_nintp. by iApply "→".
  Qed.
  Fact Deriv_n_forall {V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(δ)) -∗ ⸨ ∀: V, P ⸩(δ).
  Proof.
    iIntros "P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _ %".
    rewrite rew_eq_hwf. iApply "→". iApply "P".
  Qed.
  Fact Deriv_n_exist {V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(δ)) -∗ ⸨ ∃: V, P ⸩(δ).
  Proof.
    iDestruct 1 as (Φ) "P". iApply Deriv_byintp. iIntros (?? _) "/= #→ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "→". iApply "P".
  Qed.

  (** Introduce [○] *)
  Fact Deriv_indir_intro {P} : ⸨ P ⸩(δ) -∗ ⸨ ○{nil} P ⸩(δ).
  Proof.
    iIntros "P". iApply Deriv_byintp. iIntros (δ' _ _) "/= _ #→δ'".
    by iApply "→δ'".
  Qed.
End facts.
