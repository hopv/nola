(** * Facts *)

From nola.examples.logic Require Export deriv.

Section facts.
  Context `{!nintpGS Σ}.

  (** ** Behavior of [nintp] *)
  Fact nintp_pure {κ d φ} : ⟦ ⌜φ⌝ ⟧{κ}(d) ⊣⊢ ⌜φ⌝.
  Proof. done. Qed.
  Fact nintp_persistently {κ d P} : ⟦ □ P ⟧{κ}(d) ⊣⊢ □ ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_plainly {κ d P} : ⟦ ■ P ⟧{κ}(d) ⊣⊢ ■ ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_bupd {κ d P} : ⟦ |==> P ⟧{κ}(d) ⊣⊢ |==> ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_fupd {κ d P E E'} :
    ⟦ |={E,E'}=> P ⟧{κ}(d) ⊣⊢ |={E,E'}=> ⟦ P ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_and {κ d P Q} : ⟦ P ∧ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∧ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_or {κ d P Q} : ⟦ P ∨ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∨ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_impl {κ d P Q} : ⟦ P → Q ⟧{κ}(d) ⊣⊢ (⟦ P ⟧{κ}(d) → ⟦ Q ⟧{κ}(d)).
  Proof. done. Qed.
  Fact nintp_sep {κ d P Q} : ⟦ P ∗ Q ⟧{κ}(d) ⊣⊢ ⟦ P ⟧{κ}(d) ∗ ⟦ Q ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_wand {κ d P Q} : ⟦ P -∗ Q ⟧{κ}(d) ⊣⊢ (⟦ P ⟧{κ}(d) -∗ ⟦ Q ⟧{κ}(d)).
  Proof. done. Qed.
  Fact nintp_forall {κ d A Φ} : ⟦ ∀' Φ ⟧{κ}(d) ⊣⊢ ∀ x : A, ⟦ Φ x ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_exist {κ d A Φ} : ⟦ ∃' Φ ⟧{κ}(d) ⊣⊢ ∃ x : A, ⟦ Φ x ⟧{κ}(d).
  Proof. done. Qed.
  Fact nintp_later {κ d} {P : _ (;ᵞ)} : ⟦ ▷{nil} P ⟧{κ}(d) ⊣⊢ ▷ ⟦ P ⟧(d).
  Proof. by rewrite/= nintp_fp_nintp. Qed.
  Fact nintp_indir {κ d i} {P : _ (;ᵞ)} : ⟦ ○{nil}(i) P ⟧{κ}(d) ⊣⊢ ⸨ P ⸩(d,i).
  Proof. done. Qed.
  Fact nintp_ag {κ d γ} {P : _ (;ᵞ)} : ⟦ n_ag γ P ⟧{κ}(d) ⊣⊢ nag γ P.
  Proof. done. Qed.
  Fact nintp_inv {κ d i N} {P : _ (;ᵞ)} :
    ⟦ n_inv i N P ⟧{κ}(d) ⊣⊢ nninv d i N P.
  Proof. done. Qed.
  Fact nintp_na_inv {κ d i p N} {P : _ (;ᵞ)} :
    ⟦ n_na_inv i p N P ⟧{κ}(d) ⊣⊢ na_nninv d i p N P.
  Proof. done. Qed.
  Fact nintp_wpw {κ d W s E e Φ} :
    ⟦ WP[W] e @ s ; E {{ Φ }} ⟧{κ}(d) ⊣⊢
      WP[⟦ W ⟧(d)] e @ s ; E {{ v, ⟦ Φ v ⟧(d) }}.
  Proof. done. Qed.
  Fact nintp_twpw {κ d W s E e Φ} :
    ⟦ WP[W] e @ s ; E [{ Φ }] ⟧{κ}(d) ⊣⊢
      WP[⟦ W ⟧(d)] e @ s ; E [{ v, ⟦ Φ v ⟧(d) }].
  Proof. done. Qed.
  Fact nintp_n_forall {κ d V P} : ⟦ ∀: V, P ⟧{κ}(d) ⊣⊢ ∀ Φ, ⟦ P /: Φ ⟧(d).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_exist {κ d V P} : ⟦ ∃: V, P ⟧{κ}(d) ⊣⊢ ∃ Φ, ⟦ P /: Φ ⟧(d).
  Proof. simpl. f_equiv=> ?. by rewrite rew_eq_hwf. Qed.
  Fact nintp_n_recs {κ d A Φ} {a : A} :
    ⟦ rec:ˢ' Φ a ⟧{κ}(d) ⊣⊢ ⟦ Φ a /: rec:ˢ' Φ ⟧(d).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_n_recl {d A Φ} {a : A} :
    ⟦ rec:ˡ' Φ a ⟧(d) ⊣⊢ ⟦ Φ a /: rec:ˡ' Φ ⟧(d).
  Proof. by rewrite/= rew_eq_hwf. Qed.
  Fact nintp_subus {d P} : ⟦ !ᵘˢ P ⟧(d) ⊣⊢ ⟦ ↑ˡ P ⟧(d).
  Proof. by rewrite/= nintpS_nintp_nlarge. Qed.

  (** On [nag] *)
  Lemma nag_agree {γ} {P Q : _ (;ᵞ)} : nag γ P -∗ nag γ Q -∗ ⌜P = Q⌝.
  Proof.
    iIntros "P Q". iCombine "P Q" as "o".
    iDestruct (own_valid with "o") as %v. by apply to_agree_op_valid_L in v.
  Qed.

  Context `{!nderivy Σ ih d}.
  Implicit Type (i j : nat) (P Q : nPropL (;ᵞ)).

  (** Make connectives go inside the derivability *)
  Fact derivy_and {i P Q} :
    ⸨ P ⸩(d, i) ∧ ⸨ Q ⸩(d, i) -∗ ⸨ P ∧ Q ⸩(d, i).
  Proof.
    iIntros "PQ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iSplit; iApply "to"; [iDestruct "PQ" as "[$_]"|iDestruct "PQ" as "[_$]"].
  Qed.
  Fact derivy_or {i P Q} :
    ⸨ P ⸩(d, i) ∨ ⸨ Q ⸩(d, i) -∗ ⸨ P ∨ Q ⸩(d, i).
  Proof.
    iIntros "[?|?]"; iApply derivy_byintp; iIntros (?? _) "/= #to _ _";
      [iLeft|iRight]; by iApply "to".
  Qed.
  Fact derivy_forall {i A} {Φ : A → nPropL (;ᵞ)} :
    (∀ a, ⸨ Φ a ⸩(d, i)) -∗ ⸨ ∀' Φ ⸩(d, i).
  Proof.
    iIntros "Φ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ %".
    iApply "to". iApply "Φ".
  Qed.
  Fact derivy_exist {i A} {Φ : A → nPropL (;ᵞ)} :
    (∃ a, ⸨ Φ a ⸩(d, i)) -∗ ⸨ ∃' Φ ⸩(d, i).
  Proof.
    iDestruct 1 as (a) "Φ". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iExists a. iApply "to". iApply "Φ".
  Qed.
  Fact derivy_sep {i P Q} :
    ⸨ P ⸩(d, i) ∗ ⸨ Q ⸩(d, i) -∗ ⸨ P ∗ Q ⸩(d, i).
  Proof.
    iIntros "[P Q]". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iSplitL "P"; by iApply "to".
  Qed.
  Fact derivy_persistently {i P} : □ ⸨ P ⸩(d, i) -∗ ⸨ □ P ⸩(d, i).
  Proof.
    iIntros "#P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ !>".
    by iApply "to".
  Qed.
  Fact derivy_bupd {i P} : (|==> ⸨ P ⸩(d, i)) -∗ ⸨ |==> P ⸩(d, i).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact derivy_fupd {i E E' P} :
    (|={E,E'}=> ⸨ P ⸩(d, i)) -∗ ⸨ |={E,E'}=> P ⸩(d, i).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    by iApply "to".
  Qed.
  Fact derivy_later {i P} : ▷ ⸨ P ⸩(d, i) -∗ ⸨ ▷{nil} P ⸩(d, i).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    rewrite nintp_fp_nintp. by iApply "to".
  Qed.
  Fact derivy_n_forall {i V} {P : nPropL ([V];ᵞ )} :
    (∀ Φ, ⸨ P /: Φ ⸩(d, i)) -∗ ⸨ ∀: V, P ⸩(d, i).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _ %".
    rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.
  Fact derivy_n_exist {i V} {P : nPropL ([V];ᵞ )} :
    (∃ Φ, ⸨ P /: Φ ⸩(d, i)) -∗ ⸨ ∃: V, P ⸩(d, i).
  Proof.
    iDestruct 1 as (Φ) "P". iApply derivy_byintp. iIntros (?? _) "/= #to _ _".
    iExists Φ. rewrite rew_eq_hwf. iApply "to". iApply "P".
  Qed.

  (** Introduce [○(i)] *)
  Fact derivy_indir_intro {i j P} :
    ⸨ P ⸩(d, i) -∗ ⸨ ○{nil}(i) P ⸩(d, j).
  Proof.
    iIntros "P". iApply derivy_byintp. iIntros (d' _ _) "/= _ #tos' _".
    by iApply "tos'".
  Qed.
  (** Eliminate [○(i)] under the derivability of level [j > i] *)
  Fact derivy_indir_elim {i j P} :
    i < j → ⸨ ○{nil}(i) P ⸩(d, j) -∗ ⸨ P ⸩(d, j).
  Proof.
    move=> ij. iIntros "○P". iApply derivy_byintp.
    iIntros (d' _ _) "/= #to _ #d'to". iDestruct ("to" with "○P") as "/= ○P".
    by iApply "d'to".
  Qed.
End facts.
