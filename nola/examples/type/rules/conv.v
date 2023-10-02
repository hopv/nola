(** * Type conversion **)

From nola.examples.type Require Export deriv.

Section conv.
  Context `{!tintpGS L Σ}.

  (** [⊑] is reflexive and transitive *)
  #[export] Instance tsub_refl {d i} : Reflexive (tsub d (i:=i)).
  Proof. done. Qed.
  Lemma tsub_trans {d i T j U k V} :
    T ⊑{i,j}(d) U → U ⊑{_,k}(d) V → T ⊑(d) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** [≃] is reflexive, symmetric and transitive *)
  #[export] Instance teqv_refl {d i} : Reflexive (teqv d (i:=i)).
  Proof. done. Qed.
  Lemma teqv_symm {d i T j U} : T ≃{i,j}(d) U → U ≃(d) T.
  Proof. move=> TU ?. by rewrite TU. Qed.
  Lemma teqv_trans {d i T j U k V} :
    T ≃{i,j}(d) U → U ≃{_,k}(d) V → T ≃(d) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** Conversion between [≃] and [⊑] *)
  Lemma teqv_tsub {d i T j U} : (T ≃{i,j}(d) U) ↔ (T ⊑(d) U) ∧ (U ⊑(d) T).
  Proof. split.
    - move=> TU. split=> ?; by rewrite TU.
    - move=> [??] ?. by apply bi.equiv_entails.
  Qed.
  Lemma teqv_fwd {d i T j U} : T ≃{i,j}(d) U → T ⊑(d) U.
  Proof. apply teqv_tsub. Qed.
  Lemma teqv_bwd {d i T j U} : T ≃{i,j}(d) U → U ⊑(d) T.
  Proof. apply teqv_tsub. Qed.

  (** [==>] is reflexive, transitive, and monotone over the level *)
  #[export] Instance ttrans_refl {d i j} : Reflexive (ttrans d i (j:=j)).
  Proof. by iIntros (????) "? !>". Qed.
  Lemma ttrans_trans {d i j T k U l V} :
    T ==>{j,k}(i,d) U → U ==>{_,l}(i,d) V → T ==>{_,l}(i,d) V.
  Proof.
    iIntros (TU UV ???) "T". iMod (TU with "T"); [done|]. by iApply UV.
  Qed.
  Lemma ttrans_mono_lev `{! i ≤ⁿ i'} {d j T k U} :
    T ==>{j,k}(i,d) U → T ==>{j,k}(i',d) U.
  Proof.
    iIntros (TU ???) "T". iApply fupdw_incl; [apply wsat_incl_tinv|].
    by iApply TU.
  Qed.

  (** [⊑] into [==>] *)
  Lemma tsub_ttrans {d i j T k U} : T ⊑{j,k}(d) U → T ==>(i,d) U.
  Proof. iIntros (TU ???) "T !>". by rewrite TU. Qed.
  (** [≃] into [<==>] *)
  Lemma teqv_tbitrans {d i j T k U} : T ≃{j,k}(d) U → T <==>(i,d) U.
  Proof. move=> /teqv_tsub[??]; split; by apply tsub_ttrans. Qed.

  (** On [↑ᵗ] *)
  Lemma teqv_tbump `{! i ≤ⁿ j} {d T} : ↑ᵗ T ≃{j,i}(d) T.
  Proof. move=> ?. exact tintp_tbump. Qed.

  (** On [⊤ᵗ] *)
  Lemma tsub_any {d i T j} : T ⊑{i,j}(d) ⊤ᵗ.
  Proof. by iIntros. Qed.

  (** On [∧ᵗ] *)
  Lemma tsub_and_elim_l {d i T U} : T ∧ᵗ U ⊑{i,_}(d) T.
  Proof. iIntros (?) "/=[$ _]". Qed.
  Lemma tsub_and_elim_r {d i T U} : T ∧ᵗ U ⊑{i,_}(d) U.
  Proof. iIntros (?) "/=[_ $]". Qed.
  Lemma tsub_and_intro {d j V i T U} : V ⊑{j,i}(d) T → V ⊑(d) U → V ⊑(d) T ∧ᵗ U.
  Proof.
    iIntros (VT VU ?) "#V /=".
    iDestruct (VT with "V") as "$". iDestruct (VU with "V") as "$".
  Qed.
  Lemma ttrans_and {d i j T U k T' U'} :
    T ==>(i,d) T' →  U ==>(i,d) U' → T ∧ᵗ U ==>{j,k}(i,d) T' ∧ᵗ U'.
  Proof.
    iIntros (TT' UU' ???) "/=[T U]".
    iMod (TT' with "T") as "$"; [done|]. by iMod (UU' with "U") as "$".
  Qed.

  (** On [×] *)
  Lemma tsub_pair {d i j T T' U U'} :
    T ⊑(d) T' → U ⊑(d) U' → T × U ⊑{i,j}(d) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma teqv_pair {d i j T T' U U'} :
    T ≃(d) T' → U ≃(d) U' → T × U ≃{i,j}(d) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma ttrans_pair {d i j k T T' U U'} :
    T ==>(i,d) T' → U ==>(i,d) U' → T × U ==>{j,k}(i,d) T' × U'.
  Proof.
    iIntros (TT' UU' ???) "/=(%&%&%& T & U)".
    iMod (TT' with "T"); [done|]. iMod (UU' with "U"); [done|]. iModIntro.
    iExists _, _. by iFrame.
  Qed.

  (** On [→( )] *)
  Lemma tsub_fun `{! j ≤ⁿ i, ! j' ≤ⁿ i', ! j ≤ⁿ j'} {d T U T' U'} :
    T' ==>(j',d) T →  U ==>(j',d) U' →  T →(j) U ⊑{i,i'}(d) T' →(j') U'.
  Proof.
    move=> T'T UU' ? /=. do 3 f_equiv. iIntros "hor T'".
    rewrite !twpw_tinv_wsat_lt_tinv_wsat. iMod (T'T with "T'") as "T"; [done|].
    iDestruct ("hor" with "T") as "wp". iApply twpw_fupdw_nonval; [done|].
    iApply twpw_incl; [apply wsat_incl_tinv|]. iStopProof. do 2 f_equiv.
    by iApply UU'.
  Qed.
  Lemma teqv_fun `{! j ≤ⁿ i, ! j ≤ⁿ i'} {d T U T' U'} :
    T <==>(j,d) T' →  U <==>(j,d) U' →  T →(j) U ≃{i,i'}(d) T' →(j) U'.
  Proof.
    move=> TT' UU'.
    apply teqv_tsub; split; apply tsub_fun=> *; try apply TT'; apply UU'.
  Qed.

  (** Introduce [▽] *)
  Lemma ninv_tguard `{!tderivy Σ ih d, ! i <ⁿ L} {T v} :
    ninv tguardN (tinvd_guard T v) -∗ tguard d (i:=i) T v.
  Proof.
    iIntros "#inv !>". iApply (derivy_intro (d:=d))=>/=. iIntros (?????).
    iApply fupdw_incl; [apply wsat_incl_tinv_tninv|].
    iMod (ninv_acc with "inv") as "/=[#$ cl]"; [done|]. by iApply "cl".
  Qed.
  Lemma ttrans_guard_intro `{!tderivy Σ ih d, ! i <ⁿ j} {k T} :
    T ==>{_,k}(j,d) ▽{i,nil} T.
  Proof.
    iIntros (???) "/= #?". iApply fupdw_tinv_wsat_le. iIntros (?).
    have ? : i <ⁿ L by apply (nlt_nle_trans _ _).
    iApply fupdw_incl; [apply wsat_incl_tinv_tninv|].
    iMod (ninv_alloc (P:=tinvd_guard T _) with "[]") as "inv"; [done|].
    iApply (ninv_tguard with "inv").
  Qed.

  (** Eliminate [▽] *)
  Lemma ttrans_guard_elim {i T j} : ▽{i,nil} T ==>{j,_}(S i,tderiv) T.
  Proof.
    iIntros (???) "/= #gT". iDestruct tderiv_sound as "→".
    iDestruct ("→" with "gT") as "→T". by iApply "→T".
  Qed.

  (** More on [▽] *)
  Lemma tsub_guard `{!tderivy Σ ih d, ! j ≤ⁿ j'} {i i' T U} :
    (∀ `{!tderivy Σ ih d'}, ih d' → T ==>(S j',d') U) →
    ▽{j,nil} T ⊑{i,i'}(d) ▽{j',nil} U.
  Proof.
    move=> TU ? /=. unfold tguard. f_equiv. iIntros "T".
    iApply (derivy_map (d:=d) with "[] T"). iIntros (?? IH) "/= big % %inE".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iApply fupdw_incl; [apply wsat_incl_tinv|]. iMod ("big" $! _ inE) as "T".
    iModIntro. by iMod (TU _ _ IH with "T") as "$"; [solve_ndisj|].
  Qed.
  Lemma teqv_guard `{!tderivy Σ ih d} {i i' j T U} :
    (∀ `{!tderivy Σ ih d'}, ih d' → T <==>(S j,d') U) →
    ▽{j,nil} T ≃{i,i'}(d) ▽{j,nil} U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_guard=> *; by apply TU.
  Qed.
  Lemma tsub_guard_lev `{!tderivy Σ ih d} {i i' j} {T : _ j (;ᵞ)} :
    ▽ T ⊑{i,i'}(d) ▽ T.
  Proof. done. Qed.

  (** On [ref[ ]] *)
  Lemma tsub_ref `{!tderivy Σ ih d, ! j ≤ⁿ j'} {o i i' T U} :
    (∀ `{!tderivy Σ ih d'}, ih d' → T <==>(S j',d') U) →
    ref{j,nil}[o] T ⊑{i,i'}(d) ref{j',nil}[o] U.
  Proof.
    move=> TU ? /=. unfold tref. do 4 f_equiv. iIntros "T".
    iApply (derivy_map (d:=d) with "[] T"). iIntros (?? IH) "/= big".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iApply fupdw_incl; [apply wsat_incl_tinv|].
    iMod "big" as (?) "(↦ & T & cl)". iModIntro.
    iMod (proj1 (TU _ _ IH) with "T") as "U"; [solve_ndisj|]. iModIntro.
    iExists _. iFrame "↦ U". iIntros (?) "↦ U".
    iMod (proj2 (TU _ _ IH) with "U") as "T"; [solve_ndisj|].
    iApply fupdw_incl; [apply wsat_incl_tinv|]. by iMod ("cl" with "↦ T").
  Qed.
  Lemma teqv_ref `{!tderivy Σ ih d} {o i i' j T U} :
    (∀ `{!tderivy Σ ih d'}, ih d' → T <==>(S j,d') U) →
    ref{j,nil}[o] T ≃{i,i'}(d) ref{j,nil}[o] U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_ref=> *; split; by apply TU.
  Qed.
  Lemma tsub_ref_lev `{!tderivy Σ ih d} {o i i' j} {T : _ j (;ᵞ)} :
    ref[o] T ⊑{i,i'}(d) ref[o] T.
  Proof. done. Qed.

  (** On [∀:] *)
  Lemma tsub_forall_elim {d i j T V} : (∀: j, T) ⊑{i,_}(d) T /: V.
  Proof. move=> ? /=. setoid_rewrite rew_eq_hwf. by iIntros. Qed.
  Lemma tsub_forall_intro {d i i' j T U} :
    (∀ V, U ⊑(d) T /: V) → U ⊑{i,i'}(d) (∀: j, T).
  Proof. iIntros (UT ?) "/= ? %". by rewrite rew_eq_hwf -UT. Qed.

  (** On [∃:] *)
  Lemma tsub_exist_intro {d i j T V} : T /: V ⊑{i,_}(d) (∃: j, T).
  Proof. iIntros (?) "/= ?". iExists _. by rewrite rew_eq_hwf. Qed.
  Lemma tsub_exist_elim {d i i' j T U} :
    (∀ V, T /: V ⊑(d) U) → (∃: j, T) ⊑{i,i'}(d) U.
  Proof. iIntros (TU ?) "/=[% ?]". by rewrite rew_eq_hwf TU. Qed.
  Lemma ttrans_exist {d i j j' k T U} :
    (∀ V, T /: V ==>(i,d) U) → (∃: k, T) ==>{j,j'}(i,d) U.
  Proof.
    iIntros (TU ???) "/=[% T]". iApply TU; [done|]. by rewrite rew_eq_hwf.
  Qed.

  (** On [recᵗ:] *)
  Lemma teqv_rec_expand `{! i ≤ⁿ j} {d T} :
    (recᵗ: i, T) ≃{j,_}(d) T /: (recᵗ: i, T).
  Proof. move=> ? /=. by rewrite rew_eq_hwf tintp_tbump. Qed.
  Lemma teqv_rec_lev `{! i ≤ⁿ j, ! i ≤ⁿ k} {d T} :
    (recᵗ: i, T) ≃{j,k}(d) (recᵗ: i, T).
  Proof. move=> ? /=. by rewrite !rew_eq_hwf !tintp_tbump. Qed.

  (** On [!ᵘ] *)
  Lemma teqv_subu `{! j <ⁿ i} {d T} : !ᵘ T ≃{i,j}(d) T.
  Proof. move=> ? /=. exact tintp_lt_tintp. Qed.
End conv.
