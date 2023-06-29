(** * Expression typing *)

From nola.examples.type Require Export sintp.
From nola.examples.heap_lang Require Export proofmode.

(** Function Iteration *)
Definition iter : val := λ: "f",
  rec: "self" "ix" :=
    let: "i" := Fst "ix" in let: "x" := Snd "ix" in
    if: "i" = # 0 then # () else
      "f" "x";; "self" ("i" - # 1, "x").

Section expr.
  Context `{!tintpGS L Σ}.

  (** [:ᵒ] is persistent *)
  Fact tobj_persistent {v i T} : Persistent (v :ᵒ{i} T).
  Proof. exact _. Qed.

  (** Modify [:ᵒ] with [⊑] *)
  Lemma tobj_tsub {v i T U} : T ⊑(tsintp) U → v :ᵒ{i} T ⊢ v :ᵒ{i} U.
  Proof. move=> TU. apply TU. Qed.

  (** Modify [:ᵉ] with [==>] *)
  Lemma texpr_ttrans {e i j T k U} :
    T ==>{j,k}(i,tsintp) U →  e :ᵉ(i) T ⊢ e :ᵉ(i) U.
  Proof. move=> TU. do 2 f_equiv. iIntros ">?". by iApply TU. Qed.

  (** Modify [:ᵒ] hypothesis of [:ᵉ] with [==>] *)
  Lemma texpr_tobj_ttrans {v e i j T k U l V} : T ==>{j,k}(i,tsintp) U →
    v :ᵒ T -∗ (v :ᵒ U -∗ e :ᵉ{l}(i) V) -∗ e :ᵉ(i) V.
  Proof.
    iIntros (TU) "T Ue". iApply fupdw_twpw_fupdw.
    iMod (TU with "T") as "U"; [done|]. iApply twpw_fupdw_fupdw.
    iApply ("Ue" with "U").
  Qed.

  (** [:ᵉ] is monotone over the level *)
  Lemma texpr_mono_lev `{! i ≤ⁿ i'} {e j T} : e :ᵉ{j}(i) T ⊢ e :ᵉ(i') T.
  Proof.
    iIntros "?". iApply twpw_expand; [iApply tinv_wsat_incl|].
    iStopProof. do 2 f_equiv. iApply fupdw_expand. iApply tinv_wsat_incl.
  Qed.

  (** Introduce [:ᵒ ⊤ᵗ] *)
  Lemma tobj_any {v i} : ⊢ v :ᵒ{i} ⊤ᵗ.
  Proof. done. Qed.

  (** Value *)
  Lemma texpr_val {v i j T} : v :ᵒ T ⊢ v :ᵉ{j}(i) T.
  Proof. iIntros "?". by iApply twp_value. Qed.

  (** Let binding *)
  Lemma texpr_let {x e e' i j T k U} :
    e :ᵉ{j}(i) T -∗ (∀ v, v :ᵒ T -∗ subst x v e' :ᵉ{k}(i) U) -∗
    (let: x := e in e') :ᵉ(i) U.
  Proof.
    iIntros "? e'". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) ">?". wp_pures. by iApply "e'".
  Qed.

  (** Thread forking *)
  Lemma texpr_fork {e i j k T} : e :ᵉ{j}(i) T -∗ Fork e :ᵉ{k}(i) 𝟙.
  Proof.
    iIntros "e". wp_apply (twp_fork with "[e]"); [|done].
    iApply (twp_wand with "[$]"). by iIntros.
  Qed.

  (** Literal *)
  Lemma texpr_lit_nat {n : nat} {i j} : ⊢ # n :ᵉ{j}(i) ℕ.
  Proof. iApply twp_value. iModIntro. by iExists _. Qed.
  Lemma texpr_lit_bool {b : bool} {i j} : ⊢ # b :ᵉ{j}(i) 𝔹.
  Proof. iApply twp_value. iModIntro. by iExists _. Qed.
  Lemma texpr_lit_unit {i j} : ⊢ # () :ᵉ{j}(i) 𝟙.
  Proof. iApply twp_value. iModIntro. by iPureIntro. Qed.

  (** Non-determinism *)
  Lemma texpr_ndnat {i j} : ⊢ Ndnat :ᵉ{j}(i) ℕ.
  Proof. wp_apply twp_ndnat; [done|]. iIntros "% _ !>". by iExists _. Qed.

  (** Pair *)
  Lemma texpr_pair {e e' i j T U} :
    e :ᵉ(i) T -∗ e' :ᵉ(i) U -∗ (e, e') :ᵉ{j}(i) T × U.
  Proof.
    iIntros "??". wp_bind e'. iApply (twp_wand with "[$]").
    iIntros (?) ">?". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) ">?". wp_pure. do 2 iModIntro=>/=. iExists _, _. by iFrame.
  Qed.
  Lemma texpr_fst {e i j T U} : e :ᵉ{j}(i) T × U -∗ Fst e :ᵉ(i) T.
  Proof.
    iIntros "?". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&%&->& ? &_)". by wp_pure.
  Qed.
  Lemma texpr_snd {e i j T U} : e :ᵉ{j}(i) T × U -∗ Snd e :ᵉ(i) U.
  Proof.
    iIntros "?". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (?) "/= >(%&%&->&_& ?)". by wp_pure.
  Qed.

  (** Function *)
  Lemma texpr_fun_intro `{! i ≤ⁿ j} {x e k T U} :
    □ (∀ v, v :ᵒ T -∗ subst x v e :ᵉ(i) U) -∗ (λ: x, e) :ᵉ{j}(k) (T →(i) U).
  Proof.
    iIntros "#e". wp_pure. do 2 iModIntro=>/=. iIntros "!> % ?".
    rewrite twpw_tinv_wsat_lt_tinv_wsat. iApply twpw_fupdw_nonval; [done|].
    wp_pure. by iApply "e".
  Qed.
  Lemma texpr_fun_call `{! i ≤ⁿ j, ! i ≤ⁿ k} {e e' T U} :
    e :ᵉ{k}(j) (T →(i) U) -∗ e' :ᵉ(j) T -∗ e e' :ᵉ(j) U.
  Proof.
    iIntros "??". wp_bind e'. iApply (twp_wand with "[$]"). iIntros (?) ">?".
    wp_bind e. iApply (twp_wand with "[$]"). iIntros (?) "/= >#hor".
    iApply fupdw_twpw_fupdw. iModIntro.
    setoid_rewrite twpw_tinv_wsat_lt_tinv_wsat.
    iApply twpw_expand; [iApply (tinv_wsat_incl (M':=j))|]. by iApply "hor".
  Qed.

  (** On [iter] *)
  Lemma texpr_fun_iter `{! i ≤ⁿ j} {k e T U} :
    e :ᵉ{j}(k) (T →(i) U) -∗ iter e :ᵉ(k) (ℕ × T →(i) 𝟙).
  Proof.
    iIntros "?". wp_bind e. iApply (twp_wand with "[$]").
    iIntros (f) "/= >#f". wp_lam. wp_pures. do 3 iModIntro.
    iIntros (?) "(%&%&->&[%n ->]& #?)".
    setoid_rewrite twpw_tinv_wsat_lt_tinv_wsat.
    iInduction n as [|n] "IH"; wp_pures; [done|]. wp_bind (f _).
    iApply (twp_wand with "[]"); [by iApply "f"|]. iIntros (?) "_".
    do 4 wp_pure. have ->: (S n - 1)%Z = n by lia. iApply "IH".
  Qed.
End expr.
