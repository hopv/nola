(** * Demonstration of how our program logic can emulate CFML *)
(** Based on
  https://softwarefoundations.cis.upenn.edu/slf-current/LibSepReference.html *)

From nola.lrust Require Import notation proofmode adequacy.
Import ModwNotation WpwNotation.

(** ** Soundness of the Hoare triple *)
Theorem triple_sound `{!lrustGpreS Σ} {s e σ φ} :
  (∀ `{!lrustGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ W, W ∗
    [[{ own heap_name (◯ to_heap σ) }]][W] e @ s; ⊤
    [[{ v, RET v; ∀ σ',
          own heap_name (● to_heap σ') -∗ W ={⊤,∅}=∗ ⌜φ v σ'⌝ }]]) →
  adequate s e σ φ ∧ sn erased_step ([e], σ).
Proof.
  move=> to. split.
  - eapply lrust_adequacy. iIntros (?) "◯σ". iMod to as (W) "[W to]". iModIntro.
    iExists W. iFrame "W". iApply twpw_wpw. iApply ("to" with "◯σ").
    iIntros (?) "$".
  - eapply lrust_total. iIntros (?) "◯σ". iMod to as (W) "[W to]". iModIntro.
    iExists W. iFrame "W". iExists _. iApply ("to" with "◯σ").
    by iIntros (?) "?".
Qed.

Section cfml.
  Context `{!lrustGS_gen HasNoLc Σ}.

  (** ** Structural rules *)

  (** Consequence *)
  Lemma triple_conseq {W s E e P P' Ψ Ψ'} :
    (P ⊢ P') → (∀ v, Ψ' v ⊢ Ψ v) →
    [[{ P' }]][W] e @ s; E [[{ v, RET v; Ψ' v }]] ⊢
      [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    move=> Pto toΨ. iIntros "#to !>" (?) "P →Φ". rewrite Pto.
    iApply ("to" with "P"). iIntros (?) "Ψ'". iApply "→Φ". by rewrite toΨ.
  Qed.

  (** Frame *)
  Lemma triple_frame {W s E e P Ψ R} :
    [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P ∗ R }]][W] e @ s; E [[{ v, RET v; Ψ v ∗ R }]].
  Proof.
    iIntros "#to !>" (?) "[P R] →Φ". iApply ("to" with "P"). iIntros (?) "Ψ".
    iApply "→Φ". iFrame.
  Qed.

  (** Extraction *)
  Lemma triple_hpure {W s E e φ P Ψ} :
    (⌜φ⌝ -∗ [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]]) ⊢
      [[{ ⌜φ⌝ ∗ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "#to !>" (?) "[% ?]". by iApply "to". Qed.
  Lemma triple_hexists {W s E e A Φ Ψ} :
    (∀ a : A, [[{ Φ a }]][W] e @ s; E [[{ v, RET v; Ψ v }]]) ⊢
      [[{ ∃ a, Φ a }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "#to !>" (?) "[% ?]". by iApply "to". Qed.
  Lemma triple_hforall {W s E e A a Φ Ψ} :
    [[{ Φ a }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ ∀ a : A, Φ a }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. apply triple_conseq=>//. by iIntros. Qed.
  Lemma triple_hwand_hpure_l {W s E e φ P Ψ} :
    φ → [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ ⌜φ⌝ -∗ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. move=> ?. apply triple_conseq=>//. iIntros "→P". by iApply "→P". Qed.
  Lemma triple_hpure' {W s E e φ Ψ} :
    (⌜φ⌝ -∗ [[{ True }]][W] e @ s; E [[{ v, RET v; Ψ v }]]) ⊢
      [[{ ⌜φ⌝ }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. rewrite triple_hpure. apply triple_conseq=>//. by iIntros. Qed.

  (** Heap-naming rule *)
  (** In Iris, an SL proposition can own any ghost state, not only heap
    fragments. So we add a constraint on the proposition [P]. *)
  Lemma triple_named_heap {W s E e P φ Ψ} :
    □ (P -∗ ∃ h, ⌜φ h⌝ ∗ own heap_name (◯ h)) -∗
    (∀ h, ⌜φ h⌝ -∗
        [[{ own heap_name (◯ h) }]][W] e @ s; E [[{ v, RET v; Ψ v }]]) -∗
      [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros "#P→ #to !>" (?) "P". iDestruct ("P→" with "P") as (??) "?".
    by iApply "to".
  Qed.

  (** Combination of consequence and frame rules *)
  Lemma triple_conseq_frame {W s E e P P' Ψ Ψ' R} :
    (P ⊢ P' ∗ R) → (∀ v, Ψ' v ∗ R ⊢ Ψ v) →
    [[{ P' }]][W] e @ s; E [[{ v, RET v; Ψ' v }]] ⊢
      [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. move=> ??. rewrite triple_frame. exact: triple_conseq. Qed.

  (** Ramified frame rule *)
  Lemma triple_ramified_frame {W s E e P P' Ψ Ψ'} :
    (P ⊢ P' ∗ (∀ v, Ψ' v -∗ Ψ v)) →
    [[{ P' }]][W] e @ s; E [[{ v, RET v; Ψ' v }]] ⊢
      [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    move=> ?. eapply triple_conseq_frame; [done|]. iIntros (?) "[? →Ψ]".
    by iApply "→Ψ".
  Qed.

  (** ** Rules for terms *)

  Lemma triple_eval_like {W s E e e' P Ψ} :
    (∀ Φ, WP[W] e @ s; E [{ v, Φ v }] ⊣⊢ WP[W] e' @ s; E [{ v, Φ v }]) →
    [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] e' @ s; E [[{ v, RET v; Ψ v }]].
  Proof. move=> eqv. iIntros "#to !>" (?). by rewrite -eqv. Qed.
  Lemma triple_val {W s E v P Ψ} :
    (P ⊢ Ψ v) → [[{ P }]][W] of_val v @ s; E [[{ v', RET v'; Ψ v' }]].
  Proof.
    move=> toΨ. iIntros (?) "P Ψ→". rewrite toΨ. wp_value_head.
    by iApply "Ψ→".
  Qed.
  Lemma triple_val_minimal {W s E v} :
    [[{ True }]][W] of_val v @ s; E [[{ v', RET v'; ⌜v' = v⌝ }]].
  Proof. apply triple_val. by iIntros. Qed.
  Lemma triple_fix `{!Closed (f :b: xl +b+ []) e} {W s E P Ψ} :
    (P ⊢ Ψ (rec: f xl := e)%V) →
    [[{ P }]][W] rec: f xl := e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. unlock. exact: triple_val. Qed.
  Lemma triple_fun `{!Closed (xl +b+ []) e} {W s E P Ψ} :
    (P ⊢ Ψ (λ: xl, e)%V) →
    [[{ P }]][W] λ: xl, e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. exact triple_fix. Qed.
  Lemma triple_let `{!Closed (x :b: []) e'} {W s E e P Ψ Ψ'} :
    [[{ P }]][W] e @ s; E [[{ u, RET u; Ψ u }]] -∗
    (∀ u, [[{ Ψ u }]][W] subst' x u e' @ s; E [[{ v, RET v; Ψ' v }]]) -∗
      [[{ P }]][W] let: x := e in e' @ s; E [[{ v, RET v; Ψ' v }]].
  Proof.
    iIntros "#e #e' !>" (?) "P →Φ". iApply (twp_bind (fill [LetCtx x e'])).
    iApply ("e" with "P"). iIntros (?) "Ψ". wp_let. iApply ("e'" with "Ψ →Φ").
  Qed.
  Lemma triple_seq `{!Closed [] e'} {W s E e P Q Ψ} :
    [[{ P }]][W] e @ s; E [[{ u, RET u; Q }]] -∗
    [[{ Q }]][W] e' @ s; E [[{ v, RET v; Ψ v }]] -∗
      [[{ P }]][W] e;; e' @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "e ?". iApply (triple_let with "e"). by iIntros. Qed.
  Lemma triple_let_val `{!Closed (x :b: []) e} {W s E u P Ψ} :
    [[{ P }]][W] subst' x (of_val u) e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] let: x := u in e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros "to". iApply (triple_let (Ψ:=λ v, ⌜v = u⌝ ∗ P)%I).
    { iIntros "!>" (?). iApply triple_val. by iIntros "$". }
    iIntros (?). iApply triple_hpure. by iIntros (->).
  Qed.
  Lemma triple_if {W s E e e' P Ψ} {b : bool} :
    [[{ P }]][W] if b then e else e' @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] if: #b then e else e' @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "#to !>" (?) "P →Φ". wp_case. iApply ("to" with "P →Φ"). Qed.
  Lemma triple_app_fix_direct `{!Closed (f :b: x :b: []) e} {W s E u P Ψ} :
    [[{ P }]][W] subst' f (rec: f [x] := e) (subst' x (of_val u) e) @ s; E
      [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] (rec: f [x] := e) [u] @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "#to !>" (?) "P →Φ". wp_rec. iApply ("to" with "P →Φ"). Qed.
  Lemma triple_app_fix `{!Closed (f :b: x :b: []) e} {W s E e' u P Ψ} :
    e' = (rec: f [x] := e)%E →
    [[{ P }]][W] subst' f e' (subst' x (of_val u) e) @ s; E
      [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] e' [u] @ s; E [[{ v, RET v; Ψ v }]].
  Proof. move=> ->. exact triple_app_fix_direct. Qed.
  Lemma triple_app_fun_direct `{!Closed (x :b: []) e} {W s E u P Ψ} :
    [[{ P }]][W] subst' x (of_val u) e @ s; E
      [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] (λ: [x], e) [u] @ s; E [[{ v, RET v; Ψ v }]].
  Proof. by rewrite -triple_app_fix_direct. Qed.
  Lemma triple_app_fun `{!Closed (x :b: []) e} {W s E e' u P Ψ} :
    e' = (λ: [x], e)%E →
    [[{ P }]][W] subst' x (of_val u) e @ s; E
      [[{ v, RET v; Ψ v }]] ⊢
      [[{ P }]][W] e' [u] @ s; E [[{ v, RET v; Ψ v }]].
  Proof. move=> ->. exact triple_app_fun_direct. Qed.

  (** Rules for heap-manipulating primitive operations *)
  Lemma triple_ref {W s E v} :
    [[{ True }]][W] let: "l" := Alloc #1 in "l" <- v;; "l" @ s; E
      [[{ l, RET #l; l ↦ v ∗ †l…1 }]].
  Proof.
    iIntros (?) "_ →Φ". wp_alloc l as "↦" "†". wp_let.
    rewrite heap_pointsto_vec_singleton. wp_write. iApply "→Φ". iFrame.
  Qed.
  Lemma triple_get {W s E l q v} :
    [[{ l ↦{q} v }]][W] !#l @ s; E [[{ RET v; l ↦{q} v }]].
  Proof. exact: twp_read_na. Qed.
  Lemma triple_set `{!IntoVal e w} {W s E l v} :
    [[{ l ↦ v }]][W] #l <- e @ s; E [[{ RET #☠; l ↦ w }]].
  Proof. exact: twp_write_na. Qed.
  Lemma triple_free {W s E l v} :
    [[{ l ↦ v ∗ †l…1 }]][W] Free #1 #l @ s; E [[{ RET #☠; True }]].
  Proof.
    iIntros (?). rewrite -heap_pointsto_vec_singleton. by iApply twp_free.
  Qed.
  Lemma triple_free' {W s E l v} :
    [[{ l ↦ v ∗ †l…1 }]][W] Free #1 #l @ s; E [[{ v, RET v; True }]].
  Proof. iIntros (?) "↦† ?". by iApply (triple_free with "↦†"). Qed.

  (** ** Rules for other primitive operations *)

  Lemma pure_un_op {op l l'} :
    PureExec (un_op_eval op l l') 1 (UnOp op (Lit l)) (Lit l').
  Proof. case=> >; exact: pure_exec. Qed.
  Lemma triple_unop' {W s E op l l' P} :
    un_op_eval op l l' → (⊢ P) →
    [[{ True }]][W] UnOp op #l @ s; E [[{ RET #l'; P }]].
  Proof. iIntros (???) "_ →Φ". have ? := pure_un_op. wp_op. by iApply "→Φ". Qed.
  Lemma triple_unop {W s E op l l'} :
    un_op_eval op l l' →
    [[{ True }]][W] UnOp op #l @ s; E [[{ RET #l'; True }]].
  Proof. move=> ?. exact: triple_unop'. Qed.
  Lemma triple_opp {W s E z} :
    [[{ True }]][W] - #z @ s; E [[{ RET #(-z); True }]].
  Proof. apply triple_unop. constructor. Qed.
  Lemma triple_negb {W s E b} :
    [[{ True }]][W] Negb #b @ s; E [[{ RET #(negb b); True }]].
  Proof. apply triple_unop. constructor. Qed.

  Lemma pure_bin_op {op l1 l2 l'} :
    PureExec (op ≠ EqOp ∧ bin_op_eval ∅ op l1 l2 l') 1
      (BinOp op (Lit l1) (Lit l2)) (Lit l').
  Proof. move=> [+ Bin]. case: Bin=>// *; exact: pure_exec. Qed.
  (** We assume [op ≠ EqOp], as the equality behaves awkwardly on locations *)
  Lemma triple_binop' {W s E op l1 l2 l' P} :
    op ≠ EqOp → bin_op_eval ∅ op l1 l2 l' → (⊢ P) →
    [[{ True }]][W] BinOp op #l1 #l2 @ s; E [[{ RET #l'; P }]].
  Proof.
    iIntros (????) "_ →Φ". have ? := pure_bin_op. wp_op. by iApply "→Φ".
  Qed.
  Lemma triple_binop {W s E op l1 l2 l'} :
    op ≠ EqOp → bin_op_eval ∅ op l1 l2 l' →
    [[{ True }]][W] BinOp op #l1 #l2 @ s; E [[{ RET #l'; True }]].
  Proof. move=> ??. exact: triple_binop'. Qed.
  Lemma triple_add {W s E z1 z2} :
    [[{ True }]][W] #z1 + #z2 @ s; E [[{ RET #(z1 + z2); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_sub {W s E z1 z2} :
    [[{ True }]][W] #z1 - #z2 @ s; E [[{ RET #(z1 - z2); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_mul {W s E z1 z2} :
    [[{ True }]][W] #z1 * #z2 @ s; E [[{ RET #(z1 * z2); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_div {W s E z1 z2} :
    [[{ True }]][W] #z1 / #z2 @ s; E [[{ RET #(z1 / z2); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_mod {W s E z1 z2} :
    [[{ True }]][W] #z1 `mod` #z2 @ s; E [[{ RET #(z1 `mod` z2); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_le {W s E z1 z2} :
    [[{ True }]][W] #z1 ≤ #z2 @ s; E [[{ RET #(bool_decide (z1 ≤ z2)); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_lt {W s E z1 z2} :
    [[{ True }]][W] #z1 < #z2 @ s; E [[{ RET #(bool_decide (z1 < z2)); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_ge {W s E z1 z2} :
    [[{ True }]][W] #z1 ≥ #z2 @ s; E
      [[{ RET #(bool_decide (z1 >= z2)); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_gt {W s E z1 z2} :
    [[{ True }]][W] #z1 > #z2 @ s; E [[{ RET #(bool_decide (z1 > z2)); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_ptr_add {W s E l z} :
    [[{ True }]][W] #l +ₗ #z @ s; E [[{ RET #(l +ₗ z); True }]].
  Proof. apply triple_binop=>//. constructor. Qed.
  Lemma triple_ptr_add_nat {W s E l} {n : nat} :
    [[{ True }]][W] #l +ₗ #n @ s; E [[{ RET #(l +ₗ n); True }]].
  Proof. exact triple_ptr_add. Qed.
  Lemma triple_eq {W s E} {z1 z2 : Z} :
    [[{ True }]][W] #z1 = #z2 @ s; E [[{ RET #(bool_decide (z1 = z2)); True }]].
  Proof. iIntros (?) "_ →Φ". wp_op. by iApply "→Φ". Qed.
  Lemma triple_neq {W s E} {z1 z2 : Z} :
    [[{ True }]][W] Negb (#z1 = #z2)%E @ s; E
      [[{ RET #(bool_decide (z1 ≠ z2)); True }]].
  Proof.
    iIntros (?) "_ →Φ". do 2 wp_op. rewrite bool_decide_not. by iApply "→Φ".
  Qed.
  Lemma triple_rand {W s E z} :
    z > 0 →
    [[{ True }]][W]
      let: "r" := Ndnat in if: "r" < #z then "r" else #0 @ s; E
      [[{ z', RET #z'; ⌜0 ≤ z' < z⌝ }]].
  Proof.
    iIntros (??) "_ →Φ". wp_apply twp_ndnat=>//. iIntros (?) "_". wp_let.
    wp_op. wp_case.
    case lt: (bool_decide (n < z)); wp_value_head; iApply "→Φ"; iPureIntro;
      [apply bool_decide_eq_true_1 in lt|]; lia.
  Qed.

  (** ** Structural rules for wp *)

  (** Equivalence between wp and triple *)
  Lemma wp_equiv {W s E e P Ψ} :
    □ (P -∗ WP[W] e @ s; E [{ v, Ψ v }]) ⊣⊢
      [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iSplit.
    - iIntros "#to !>" (?) "P →Φ". iDestruct ("to" with "P") as "wp".
      iApply (twp_wand with "wp →Φ").
    - iIntros "#to !> P". iApply ("to" with "P"). by iIntros.
  Qed.

  (** Consequence rule for wp *)
  Lemma wp_conseq {W s E e Ψ Ψ'} :
    (∀ v, Ψ v ⊢ Ψ' v) →
    WP[W] e @ s; E [{ v, Ψ v }] ⊢ WP[W] e @ s; E [{ v, Ψ' v }].
  Proof. move=> to. by setoid_rewrite to. Qed.

  (** Frame rule for wp *)
  Lemma wp_frame {W s E e Ψ R} :
    WP[W] e @ s; E [{ v, Ψ v }] ∗ R ⊢ WP[W] e @ s; E [{ v, Ψ v ∗ R }].
  Proof. iIntros "[wp R]". iApply (twp_wand with "wp"). by iIntros (?) "$". Qed.
  (** Corollaries, including ramified frame rule *)
  Lemma wp_ramified {W s E e Ψ Ψ'} :
    WP[W] e @ s; E [{ v, Ψ v }] ∗ (∀ v, Ψ v -∗ Ψ' v) ⊢
      WP[W] e @ s; E [{ v, Ψ' v }].
  Proof.
    rewrite wp_frame. apply wp_conseq=> ?. iIntros "[? Ψ→]". by iApply "Ψ→".
  Qed.
  Lemma wp_conseq_frame {W s E e R Ψ Ψ'} :
    (∀ v, Ψ v ∗ R ⊢ Ψ' v) →
    WP[W] e @ s; E [{ v, Ψ v }] ∗ R ⊢ WP[W] e @ s; E [{ v, Ψ' v }].
  Proof. move=> ?. rewrite wp_frame. exact: wp_conseq. Qed.
  Lemma wp_ramified_trans {W s E e P Ψ Ψ'} :
    (P ⊢ WP[W] e @ s; E [{ v, Ψ v }] ∗ (∀ v, Ψ v -∗ Ψ' v)) →
    (P ⊢ WP[W] e @ s; E [{ v, Ψ' v }]).
  Proof. by rewrite wp_ramified. Qed.

  (** ** Weakest-precondition style reasoning rules for terms *)

  Lemma wp_eval_like {W s E e e' Ψ} :
    (WP[W] e @ s; E [{ v, Ψ v }] ⊣⊢ WP[W] e' @ s; E [{ v, Ψ v }]) →
    WP[W] e @ s; E [{ v, Ψ v }] ⊢ WP[W] e' @ s; E [{ v, Ψ v }].
  Proof. by move=> ->. Qed.
  Lemma wp_val {W s E v Ψ} :
    Ψ v ⊢ WP[W] of_val v @ s; E [{ u, Ψ u }].
  Proof. exact: twp_value. Qed.
  Lemma wp_fix `{!Closed (f :b: xl +b+ []) e} {W s E Ψ} :
    Ψ (rec: f xl := e)%V ⊢
      WP[W] rec: f xl := e @ s; E [{ v, Ψ v }].
  Proof. unlock. by rewrite wp_val. Qed.
  Lemma wp_fun `{!Closed (xl +b+ []) e} {W s E Ψ} :
    Ψ (λ: xl, e)%V ⊢ WP[W] λ: xl, e @ s; E [{ v, Ψ v }].
  Proof. exact wp_fix. Qed.
  Lemma wp_app_fix `{!Closed (f :b: x :b: []) e} {W s E e' u Ψ} :
    e' = (rec: f [x] := e)%E →
    WP[W] subst' f e' (subst' x (of_val u) e) @ s; E [{ v,  Ψ v }] ⊢
      WP[W] e' [u] @ s; E [{ v, Ψ v }].
  Proof. iIntros (->) "?". by wp_rec. Qed.
  Lemma wp_app_fun `{!Closed (x :b: []) e} {W s E e' u Ψ} :
    e' = (λ: [x], e)%E →
    WP[W] subst' x (of_val u) e @ s; E [{ v,  Ψ v }] ⊢
      WP[W] e' [u] @ s; E [{ v, Ψ v }].
  Proof. exact wp_app_fix. Qed.
  Lemma wp_let `{!Closed (x :b: []) e'} {W s E e Ψ} :
    WP[W] e @ s; E [{ u, WP[W] subst' x u e' @ s; E [{ v, Ψ v }] }] ⊢
      WP[W] let: x := e in e' @ s; E [{ v, Ψ v }].
  Proof.
    iIntros "wp". iApply (twp_bind (fill [LetCtx x e'])).
    iApply (wp_conseq with "wp"). iIntros (?) "?". by wp_let.
  Qed.
  Lemma wp_seq `{!Closed [] e'} {W s E e Ψ} :
    WP[W] e @ s; E [{ _, WP[W] e' @ s; E [{ v, Ψ v }] }] ⊢
      WP[W] e;; e' @ s; E [{ v, Ψ v }].
  Proof. by rewrite -wp_let. Qed.
  Lemma wp_if {W s E e e' Ψ} {b : bool} :
    WP[W] if b then e else e' @ s; E [{ v, Ψ v }] ⊢
      WP[W] if: #b then e else e' @ s; E [{ v, Ψ v }].
  Proof. iIntros "?". by wp_case. Qed.
  Lemma wp_if_case {W s E e e' Ψ} {b : bool} :
    (if b then WP[W] e @ s; E [{ v, Ψ v }] else WP[W] e' @ s; E [{ v, Ψ v }]) ⊢
      WP[W] if: #b then e else e' @ s; E [{ v, Ψ v }].
  Proof. rewrite -wp_if. by case: b. Qed.

  Lemma wp_sound {W s E e} :
    ∀ Ψ, (λ Ψ, WP[W] e @ s; E [{ v, Ψ v }]) Ψ ⊢ WP[W] e @ s; E [{ v, Ψ v }].
  Proof. done. Qed.

  (** ** On additional separation logic operators *)

  (** Disjunction *)
  Lemma triple_hor {W s E e P P' Ψ} :
    [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]] -∗
    [[{ P' }]][W] e @ s; E [[{ v, RET v; Ψ v }]] -∗
      [[{ P ∨ P' }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. iIntros "#P→ #P'→ !>" (?) "[?|?]"; by [iApply "P→"|iApply "P'→"]. Qed.

  (** Conjunction *)
  Lemma triple_handl {W s E e P P' Ψ} :
    [[{ P }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P ∧ P' }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. apply triple_conseq=>//. by iIntros "[? _]". Qed.
  Lemma triple_handr {W s E e P P' Ψ} :
    [[{ P' }]][W] e @ s; E [[{ v, RET v; Ψ v }]] ⊢
      [[{ P ∧ P' }]][W] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof. apply triple_conseq=>//. by iIntros "[_ ?]". Qed.
End cfml.
