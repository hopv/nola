(** * Type conversion **)

From nola.examples.type Require Export deriv.

Section conv.
  Context `{!tintpGS L Σ}.

  (** [⊑] is reflexive and transitive *)
  #[export] Instance tsub_refl {δ i} : Reflexive (tsub δ (i:=i)).
  Proof. done. Qed.
  Lemma tsub_trans {δ i T j U k V} :
    T ⊑{i,j}(δ) U → U ⊑{_,k}(δ) V → T ⊑(δ) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** [≃] is reflexive, symmetric and transitive *)
  #[export] Instance teqv_refl {δ i} : Reflexive (teqv δ (i:=i)).
  Proof. done. Qed.
  Lemma teqv_symm {δ i T j U} : T ≃{i,j}(δ) U → U ≃(δ) T.
  Proof. move=> TU ?. by rewrite TU. Qed.
  Lemma teqv_trans {δ i T j U k V} :
    T ≃{i,j}(δ) U → U ≃{_,k}(δ) V → T ≃(δ) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** Conversion between [≃] and [⊑] *)
  Lemma teqv_tsub {δ i T j U} : (T ≃{i,j}(δ) U) ↔ (T ⊑(δ) U) ∧ (U ⊑(δ) T).
  Proof. split.
    - move=> TU. split=> ?; by rewrite TU.
    - move=> [??] ?. by apply bi.equiv_entails.
  Qed.
  Lemma teqv_fwd {δ i T j U} : T ≃{i,j}(δ) U → T ⊑(δ) U.
  Proof. apply teqv_tsub. Qed.
  Lemma teqv_bwd {δ i T j U} : T ≃{i,j}(δ) U → U ⊑(δ) T.
  Proof. apply teqv_tsub. Qed.

  (** [==>] is reflexive, transitive, and monotone over the level *)
  #[export] Instance ttrans_refl {δ i j} : Reflexive (ttrans δ i (j:=j)).
  Proof. by iIntros (????) "? !>". Qed.
  Lemma ttrans_trans {δ i j T k U l V} :
    T ==>{j,k}(i,δ) U → U ==>{_,l}(i,δ) V → T ==>{_,l}(i,δ) V.
  Proof.
    iIntros (TU UV ???) "T". iMod (TU with "T"); [done|]. by iApply UV.
  Qed.
  Lemma ttrans_mono_lev `{! i ≤ⁿ i'} {δ j T k U} :
    T ==>{j,k}(i,δ) U → T ==>{j,k}(i',δ) U.
  Proof.
    iIntros (TU ???) "T". by iMod (TU with "T").
  Qed.

  (** [⊑] into [==>] *)
  Lemma tsub_ttrans {δ i j T k U} : T ⊑{j,k}(δ) U → T ==>(i,δ) U.
  Proof. iIntros (TU ???) "T !>". by rewrite TU. Qed.
  (** [≃] into [<==>] *)
  Lemma teqv_tbitrans {δ i j T k U} : T ≃{j,k}(δ) U → T <==>(i,δ) U.
  Proof. move=> /teqv_tsub[??]; split; by apply tsub_ttrans. Qed.

  (** On [↑ᵗ] *)
  Lemma teqv_tbump `{! i ≤ⁿ j} {δ T} : ↑ᵗ T ≃{j,i}(δ) T.
  Proof. move=> ?. exact tintp_tbump. Qed.

  (** On [⊤ᵗ] *)
  Lemma tsub_any {δ i T j} : T ⊑{i,j}(δ) ⊤ᵗ.
  Proof. by iIntros. Qed.

  (** On [∧ᵗ] *)
  Lemma tsub_and_elim_l {δ i T U} : T ∧ᵗ U ⊑{i,_}(δ) T.
  Proof. iIntros (?) "/=[$ _]". Qed.
  Lemma tsub_and_elim_r {δ i T U} : T ∧ᵗ U ⊑{i,_}(δ) U.
  Proof. iIntros (?) "/=[_ $]". Qed.
  Lemma tsub_and_intro {δ j V i T U} : V ⊑{j,i}(δ) T → V ⊑(δ) U → V ⊑(δ) T ∧ᵗ U.
  Proof.
    iIntros (VT VU ?) "#V /=".
    iDestruct (VT with "V") as "$". iDestruct (VU with "V") as "$".
  Qed.
  Lemma ttrans_and {δ i j T U k T' U'} :
    T ==>(i,δ) T' →  U ==>(i,δ) U' → T ∧ᵗ U ==>{j,k}(i,δ) T' ∧ᵗ U'.
  Proof.
    iIntros (TT' UU' ???) "/=[T U]".
    iMod (TT' with "T") as "$"; [done|]. by iMod (UU' with "U") as "$".
  Qed.

  (** On [×] *)
  Lemma tsub_pair {δ i j T T' U U'} :
    T ⊑(δ) T' → U ⊑(δ) U' → T × U ⊑{i,j}(δ) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma teqv_pair {δ i j T T' U U'} :
    T ≃(δ) T' → U ≃(δ) U' → T × U ≃{i,j}(δ) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma ttrans_pair {δ i j k T T' U U'} :
    T ==>(i,δ) T' → U ==>(i,δ) U' → T × U ==>{j,k}(i,δ) T' × U'.
  Proof.
    iIntros (TT' UU' ???) "/=(%&%&%& T & U)".
    iMod (TT' with "T"); [done|]. iMod (UU' with "U"); [done|]. iModIntro.
    iExists _, _. by iFrame.
  Qed.

  (** On [→( )] *)
  Lemma tsub_fun `{! j ≤ⁿ i, ! j' ≤ⁿ i', ! j ≤ⁿ j'} {δ T U T' U'} :
    T' ==>(j',δ) T →  U ==>(j',δ) U' →  T →(j) U ⊑{i,i'}(δ) T' →(j') U'.
  Proof.
    move=> T'T UU' ? /=. do 3 f_equiv. iIntros "hor T'".
    rewrite !twpw_tinv_wsat_lt_tinv_wsat. iMod (T'T with "T'") as "T"; [done|].
    iDestruct ("hor" with "T") as "wp". iApply twpw_fupdw_nonval; [done|].
    iApply twpw_incl; [apply wsat_incl_tinv|]. iStopProof. do 2 f_equiv.
    by iApply UU'.
  Qed.
  Lemma teqv_fun `{! j ≤ⁿ i, ! j ≤ⁿ i'} {δ T U T' U'} :
    T <==>(j,δ) T' →  U <==>(j,δ) U' →  T →(j) U ≃{i,i'}(δ) T' →(j) U'.
  Proof.
    move=> TT' UU'.
    apply teqv_tsub; split; apply tsub_fun=> *; try apply TT'; apply UU'.
  Qed.

  (** Introduce [▽] *)
  Lemma ninv_tguard `{!tderivy ih δ, ! i <ⁿ L} {T v} :
    inv_tok tguardN (tinvd_guard T v) -∗ tguard δ (i:=i) T v.
  Proof.
    iIntros "#inv !>". iApply (derivy_intro (δ:=δ))=>/=. iIntros (?????).
    iMod (inv_tok_acc with "inv") as "/=[#T cl]"; [done|]. by iMod ("cl" with "T").
  Qed.
  Lemma ttrans_guard_intro `{!tderivy ih δ, ! i <ⁿ j} {k T} :
    T ==>{_,k}(j,δ) ▽{i,nil} T.
  Proof.
    iIntros (???) "/= #?". iApply fupdw_tinv_wsat_le. iIntros (?).
    have ? : i <ⁿ L by apply (nlt_nle_trans _ _).
    iMod (inv_tok_alloc (P:=tinvd_guard T _) with "[]") as "inv"; [done|].
    iApply (ninv_tguard with "inv").
  Qed.

  (** Eliminate [▽] *)
  Lemma ttrans_guard_elim {i T j} : ▽{i,nil} T ==>{j,_}(S i,tderiv) T.
  Proof.
    iIntros (???) "/= #gT". iDestruct tderiv_sound as "→".
    iDestruct ("→" with "gT") as "→T". by iApply "→T".
  Qed.

  (** More on [▽] *)
  Lemma tsub_guard `{!tderivy ih δ, ! j ≤ⁿ j'} {i i' T U} :
    (∀ `{!tderivy ih δ'}, ih δ' → T ==>(S j',δ') U) →
    ▽{j,nil} T ⊑{i,i'}(δ) ▽{j',nil} U.
  Proof.
    move=> TU ? /=. unfold tguard. f_equiv. iIntros "T".
    iApply (derivy_map (δ:=δ) with "[] T"). iIntros (?? IH) "/= big % %inE".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iMod ("big" $! _ inE) as "T". iModIntro.
    by iMod (TU _ _ IH with "T") as "$"; [solve_ndisj|].
  Qed.
  Lemma teqv_guard `{!tderivy ih δ} {i i' j T U} :
    (∀ `{!tderivy ih δ'}, ih δ' → T <==>(S j,δ') U) →
    ▽{j,nil} T ≃{i,i'}(δ) ▽{j,nil} U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_guard=> *; by apply TU.
  Qed.
  Lemma tsub_guard_lev `{!tderivy ih δ} {i i' j} {T : _ j (;ᵞ)} :
    ▽ T ⊑{i,i'}(δ) ▽ T.
  Proof. done. Qed.

  (** On [ref[ ]] *)
  Lemma tsub_ref `{!tderivy ih δ, ! j ≤ⁿ j'} {o i i' T U} :
    (∀ `{!tderivy ih δ'}, ih δ' → T <==>(S j',δ') U) →
    ref{j,nil}[o] T ⊑{i,i'}(δ) ref{j',nil}[o] U.
  Proof.
    move=> TU ? /=. unfold tref. do 4 f_equiv. iIntros "T".
    iApply (derivy_map (δ:=δ) with "[] T"). iIntros (?? IH) "/= big".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iMod "big" as (?) "(↦ & T & cl)". iModIntro.
    iMod (proj1 (TU _ _ IH) with "T") as "U"; [solve_ndisj|]. iModIntro.
    iExists _. iFrame "↦ U". iIntros (?) "↦ U".
    iMod (proj2 (TU _ _ IH) with "U") as "T"; [solve_ndisj|].
    by iMod ("cl" with "↦ T").
  Qed.
  Lemma teqv_ref `{!tderivy ih δ} {o i i' j T U} :
    (∀ `{!tderivy ih δ'}, ih δ' → T <==>(S j,δ') U) →
    ref{j,nil}[o] T ≃{i,i'}(δ) ref{j,nil}[o] U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_ref=> *; split; by apply TU.
  Qed.
  Lemma tsub_ref_lev `{!tderivy ih δ} {o i i' j} {T : _ j (;ᵞ)} :
    ref[o] T ⊑{i,i'}(δ) ref[o] T.
  Proof. done. Qed.

  (** On [∀:] *)
  Lemma tsub_forall_elim {δ i j T V} : (∀: j, T) ⊑{i,_}(δ) T /: V.
  Proof. move=> ? /=. setoid_rewrite rew_eq_hwf. by iIntros. Qed.
  Lemma tsub_forall_intro {δ i i' j T U} :
    (∀ V, U ⊑(δ) T /: V) → U ⊑{i,i'}(δ) (∀: j, T).
  Proof. iIntros (UT ?) "/= ? %". by rewrite rew_eq_hwf -UT. Qed.

  (** On [∃:] *)
  Lemma tsub_exist_intro {δ i j T V} : T /: V ⊑{i,_}(δ) (∃: j, T).
  Proof. iIntros (?) "/= ?". iExists _. by rewrite rew_eq_hwf. Qed.
  Lemma tsub_exist_elim {δ i i' j T U} :
    (∀ V, T /: V ⊑(δ) U) → (∃: j, T) ⊑{i,i'}(δ) U.
  Proof. iIntros (TU ?) "/=[% ?]". by rewrite rew_eq_hwf TU. Qed.
  Lemma ttrans_exist {δ i j j' k T U} :
    (∀ V, T /: V ==>(i,δ) U) → (∃: k, T) ==>{j,j'}(i,δ) U.
  Proof.
    iIntros (TU ???) "/=[% T]". iApply TU; [done|]. by rewrite rew_eq_hwf.
  Qed.

  (** On [recᵗ:] *)
  Lemma teqv_rec_expand `{! i ≤ⁿ j} {δ T} :
    (recᵗ: i, T) ≃{j,_}(δ) T /: (recᵗ: i, T).
  Proof. move=> ? /=. by rewrite rew_eq_hwf tintp_tbump. Qed.
  Lemma teqv_rec_lev `{! i ≤ⁿ j, ! i ≤ⁿ k} {δ T} :
    (recᵗ: i, T) ≃{j,k}(δ) (recᵗ: i, T).
  Proof. move=> ? /=. by rewrite !rew_eq_hwf !tintp_tbump. Qed.

  (** On [!ᵘ] *)
  Lemma teqv_subu `{! j <ⁿ i} {δ T} : !ᵘ T ≃{i,j}(δ) T.
  Proof. move=> ? /=. exact tintp_lt_tintp. Qed.
End conv.
