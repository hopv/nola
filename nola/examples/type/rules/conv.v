(** * Type conversion **)

From nola.examples.type Require Export sintp.

Section conv.
  Context `{!tintpGS L Σ}.

  (** [⊑] is reflexive and transitive *)
  Lemma tsub_refl {s i T} : T ⊑{i,_}(s) T.
  Proof. done. Qed.
  Lemma tsub_trans {s i T j U k V} :
    T ⊑{i,j}(s) U → U ⊑{_,k}(s) V → T ⊑(s) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** [≃] is reflexive, symmetric and transitive *)
  Lemma teqv_refl {s i T} : T ≃{i,_}(s) T.
  Proof. done. Qed.
  Lemma teqv_symm {s i T j U} : T ≃{i,j}(s) U → U ≃(s) T.
  Proof. move=> TU ?. by rewrite TU. Qed.
  Lemma teqv_trans {s i T j U k V} :
    T ≃{i,j}(s) U → U ≃{_,k}(s) V → T ≃(s) V.
  Proof. move=> TU UV ?. by rewrite TU UV. Qed.

  (** Conversion between [≃] and [⊑] *)
  Lemma teqv_tsub {s i T j U} : (T ≃{i,j}(s) U) ↔ (T ⊑(s) U) ∧ (U ⊑(s) T).
  Proof. split.
    - move=> TU. split=> ?; by rewrite TU.
    - move=> [??] ?. by apply bi.equiv_entails.
  Qed.

  (** [==>] is reflexive, transitive, and monotone over the level *)
  Lemma ttrans_refl {s i j T} : T ==>{j,_}(i,s) T.
  Proof. by iIntros (???) "? !>". Qed.
  Lemma ttrans_trans {s i j T k U l V} :
    T ==>{j,k}(i,s) U → U ==>{_,l}(i,s) V → T ==>{_,l}(i,s) V.
  Proof.
    iIntros (TU UV ???) "T". iMod (TU with "T"); [done|]. by iApply UV.
  Qed.
  Lemma ttrans_mono_lev `{! i ≤ⁿ i'} {s j T k U} :
    T ==>{j,k}(i,s) U → T ==>{j,k}(i',s) U.
  Proof.
    iIntros (TU ???) "T". iApply fupdw_expand; [|by iApply TU].
    iApply tinv_wsat_incl.
  Qed.

  (** [⊑] into [==>] *)
  Lemma tsub_ttrans {s i j T k U} : T ⊑{j,k}(s) U → T ==>(i,s) U.
  Proof. iIntros (TU ???) "T !>". by rewrite TU. Qed.
  (** [≃] into [<==>] *)
  Lemma teqv_tbitrans {s i j T k U} : T ≃{j,k}(s) U → T <==>(i,s) U.
  Proof. move=> /teqv_tsub[??]; split; by apply tsub_ttrans. Qed.

  (** On [↑ᵗ] *)
  Lemma teqv_tbump `{! i ≤ⁿ j} {s T} : ↑ᵗ T ≃{j,i}(s) T.
  Proof. move=> ?. exact tintp_tbump. Qed.

  (** On [⊤ᵗ] *)
  Lemma tsub_any {s i T j} : T ⊑{i,j}(s) ⊤ᵗ.
  Proof. by iIntros. Qed.

  (** On [∧ᵗ] *)
  Lemma tsub_and_elim_l {s i T U} : T ∧ᵗ U ⊑{i,_}(s) T.
  Proof. iIntros (?) "/=[$ _]". Qed.
  Lemma tsub_and_elim_r {s i T U} : T ∧ᵗ U ⊑{i,_}(s) U.
  Proof. iIntros (?) "/=[_ $]". Qed.
  Lemma tsub_and_intro {s j V i T U} : V ⊑{j,i}(s) T → V ⊑(s) U → V ⊑(s) T ∧ᵗ U.
  Proof.
    iIntros (VT VU ?) "#V /=".
    iDestruct (VT with "V") as "$". iDestruct (VU with "V") as "$".
  Qed.
  Lemma ttrans_and {s i j T U k T' U'} :
    T ==>(i,s) T' →  U ==>(i,s) U' → T ∧ᵗ U ==>{j,k}(i,s) T' ∧ᵗ U'.
  Proof.
    iIntros (TT' UU' ???) "/=[T U]".
    iMod (TT' with "T") as "$"; [done|]. by iMod (UU' with "U") as "$".
  Qed.

  (** On [×] *)
  Lemma tsub_pair {s i j T T' U U'} :
    T ⊑(s) T' → U ⊑(s) U' → T × U ⊑{i,j}(s) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma teqv_pair {s i j T T' U U'} :
    T ≃(s) T' → U ≃(s) U' → T × U ≃{i,j}(s) T' × U'.
  Proof. move=> ??? /=. by do 6 f_equiv. Qed.
  Lemma ttrans_pair {s i j k T T' U U'} :
    T ==>(i,s) T' → U ==>(i,s) U' → T × U ==>{j,k}(i,s) T' × U'.
  Proof.
    iIntros (TT' UU' ???) "/=(%&%&%& T & U)".
    iMod (TT' with "T"); [done|]. iMod (UU' with "U"); [done|]. iModIntro.
    iExists _, _. by iFrame.
  Qed.

  (** On [→( )] *)
  Lemma tsub_fun `{! j ≤ⁿ i, ! j' ≤ⁿ i', ! j ≤ⁿ j'} {s T U T' U'} :
    T' ==>(j',s) T →  U ==>(j',s) U' →  T →(j) U ⊑{i,i'}(s) T' →(j') U'.
  Proof.
    move=> T'T UU' ? /=. do 3 f_equiv. iIntros "hor T'".
    rewrite !twpw_tinv_wsat_lt_tinv_wsat. iMod (T'T with "T'") as "T"; [done|].
    iDestruct ("hor" with "T") as "wp".
    iDestruct (twpw_expand with "[] wp") as "?"; [iApply tinv_wsat_incl|].
    iApply twpw_fupdw_nonval; [done|]. iStopProof. do 2 f_equiv. by iApply UU'.
  Qed.
  Lemma teqv_fun `{! j ≤ⁿ i, ! j ≤ⁿ i'} {s T U T' U'} :
    T <==>(j,s) T' →  U <==>(j,s) U' →  T →(j) U ≃{i,i'}(s) T' →(j) U'.
  Proof.
    move=> TT' UU'.
    apply teqv_tsub; split; apply tsub_fun=> *; try apply TT'; apply UU'.
  Qed.

  (** Introduce [▽] *)
  Lemma ninv_tguard `{!tsintpy Σ ih s, ! i <ⁿ L} {T v} :
    ninv tguardN (tinvd_guard T v) -∗ tguard s (i:=i) T v.
  Proof.
    iIntros "#inv !>". iApply (sintpy_intro (s:=s))=>/=. iIntros (?????).
    iApply fupdw_expand; [iApply (tinv_wsat_tninv_wsat (M:=S i))|].
    iMod (ninv_acc with "inv") as "/=[#$ cl]"; [done|]. by iApply "cl".
  Qed.
  Lemma ttrans_guard_intro `{!tsintpy Σ ih s, ! i <ⁿ j} {k T} :
    T ==>{_,k}(j,s) ▽{i,nil} T.
  Proof.
    iIntros (???) "/= #?". iApply fupdw_tinv_wsat_le. iIntros (?).
    have ?: i <ⁿ L by apply (nlt_nle_trans _ _).
    iApply fupdw_expand; [iApply (tinv_wsat_tninv_wsat (M:=j))|].
    iMod (ninv_alloc (P:=tinvd_guard T _) with "[]") as "inv"; [done|].
    iApply (ninv_tguard with "inv").
  Qed.

  (** Eliminate [▽] *)
  Lemma ttrans_guard_elim {i T j} : ▽{i,nil} T ==>{j,_}(S i,tsintp) T.
  Proof.
    iIntros (???) "/= #gT". iDestruct tsintp_sound as "to".
    iDestruct ("to" with "gT") as "toT". by iApply "toT".
  Qed.

  (** More on [▽] *)
  Lemma tsub_guard `{!tsintpy Σ ih s, ! j ≤ⁿ j'} {i i' T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T ==>(S j',s') U) →
    ▽{j,nil} T ⊑{i,i'}(s) ▽{j',nil} U.
  Proof.
    move=> TU ? /=. unfold tguard. f_equiv. iIntros "T".
    iApply (sintpy_map (s:=s) with "[] T"). iIntros (?? IH) "/= big % %inE".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iApply fupdw_expand; [iApply tinv_wsat_incl|]. iMod ("big" $! _ inE) as "T".
    iModIntro. by iMod (TU _ _ IH with "T") as "$"; [solve_ndisj|].
  Qed.
  Lemma teqv_guard `{!tsintpy Σ ih s} {i i' j T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T <==>(S j,s') U) →
    ▽{j,nil} T ≃{i,i'}(s) ▽{j,nil} U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_guard=> *; by apply TU.
  Qed.

  (** On [ref[ ]] *)
  Lemma tsub_ref `{!tsintpy Σ ih s, ! j ≤ⁿ j'} {o i i' T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T <==>(S j',s') U) →
    ref{j,nil}[o] T ⊑{i,i'}(s) ref{j',nil}[o] U.
  Proof.
    move=> TU ? /=. unfold tref. do 4 f_equiv. iIntros "T".
    iApply (sintpy_map (s:=s) with "[] T"). iIntros (?? IH) "/= big".
    iApply fupdw_trans. assert (S j ≤ⁿ S j') by exact _.
    iApply fupdw_expand; [iApply tinv_wsat_incl|].
    iMod "big" as (?) "(↦ & T & cl)". iModIntro.
    iMod (proj1 (TU _ _ IH) with "T") as "U"; [solve_ndisj|]. iModIntro.
    iExists _. iFrame "↦ U". iIntros (?) "↦ U".
    iMod (proj2 (TU _ _ IH) with "U") as "T"; [solve_ndisj|].
    iApply fupdw_expand; [iApply tinv_wsat_incl|]. by iMod ("cl" with "↦ T").
  Qed.
  Lemma teqv_ref `{!tsintpy Σ ih s} {o i i' j T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T <==>(S j,s') U) →
    ref{j,nil}[o] T ≃{i,i'}(s) ref{j,nil}[o] U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_ref=> *; split; by apply TU.
  Qed.

  (** On [∀:] *)
  Lemma tsub_forall_elim {s i j T V} : (∀: j, T) ⊑{i,_}(s) T /: V.
  Proof. move=> ? /=. setoid_rewrite rew_eq_hwf. by iIntros. Qed.
  Lemma tsub_forall_intro {s i i' j T U} :
    (∀ V, U ⊑(s) T /: V) → U ⊑{i,i'}(s) (∀: j, T).
  Proof. iIntros (UT ?) "/= ? %". by rewrite rew_eq_hwf -UT. Qed.

  (** On [∃:] *)
  Lemma tsub_exist_intro {s i j T V} : T /: V ⊑{i,_}(s) (∃: j, T).
  Proof. iIntros (?) "/= ?". iExists _. by rewrite rew_eq_hwf. Qed.
  Lemma tsub_exist_elim {s i i' j T U} :
    (∀ V, T /: V ⊑(s) U) → (∃: j, T) ⊑{i,i'}(s) U.
  Proof. iIntros (TU ?) "/=[% ?]". by rewrite rew_eq_hwf TU. Qed.
  Lemma ttrans_exist {s i j j' k T U} :
    (∀ V, T /: V ==>(i,s) U) → (∃: k, T) ==>{j,j'}(i,s) U.
  Proof.
    iIntros (TU ???) "/=[% T]". iApply TU; [done|]. by rewrite rew_eq_hwf.
  Qed.

  (** On [recᵗ:] *)
  Lemma teqv_rec `{! j ≤ⁿ i} {s T} : (recᵗ: j, T) ≃{i,_}(s) T /: (recᵗ: j, T).
  Proof. move=> ? /=. by rewrite rew_eq_hwf tintp_tbump. Qed.

  (** On [!ᵘ] *)
  Lemma teqv_subu `{! j <ⁿ i} {s T} : !ᵘ T ≃{i,j}(s) T.
  Proof. move=> ? /=. exact tintp_lt_tintp. Qed.
End conv.
