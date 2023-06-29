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

  (** On [↑ᵗ] *)
  Lemma teqv_tbump `{! i ≤ⁿ j} {s T} : ↑ᵗ T ≃{j,i}(s) T.
  Proof. move=> ?. exact tintp_tbump. Qed.

  (** On [ref[ ]] *)
  Lemma tsub_ref `{!tsintpy Σ ih s, ! j ≤ⁿ j'} {o i i' T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T ≃{j,j'}(s') U) →
    ref{j,nil}[o] T ⊑{i,i'}(s) ref{j',nil}[o] U.
  Proof.
    move=> TU ? /=. unfold tref. do 4 f_equiv. iIntros "T".
    iApply (sintpy_byintp (s:=s)). iIntros (???) "/= #to _ _".
    iDestruct ("to" with "T") as "/= big". iClear "to".
    iApply fupdw_expand; [iApply tinv_wsat_incl|]. iStopProof.
    do 5 f_equiv; [by rewrite TU|].
    do 3 f_equiv; [|iApply fupdw_expand; iApply tinv_wsat_incl].
    f_equiv. by rewrite TU.
  Qed.
  Lemma teqv_ref `{!tsintpy Σ ih s} {o i i' j T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T ≃{j,j}(s') U) →
    ref{j,nil}[o] T ≃{i,i'}(s) ref{j,nil}[o] U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_ref=> *?; by rewrite TU.
  Qed.

  (** On [▽] *)
  Lemma tsub_guard `{!tsintpy Σ ih s, ! j ≤ⁿ j'} {i i' T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T ⊑(s') U) →
    ▽{j,nil} T ⊑{i,i'}(s) ▽{j',nil} U.
  Proof.
    move=> TU ? /=. unfold tguard. f_equiv. iIntros "T".
    iApply (sintpy_byintp (s:=s)). iIntros (???) "/= #to _ _".
    iDestruct ("to" with "T") as "/= big". iClear "to".
    iApply fupdw_expand; [iApply tinv_wsat_incl|]. iStopProof.
    f_equiv. by apply TU.
  Qed.
  Lemma teqv_guard `{!tsintpy Σ ih s} {i i' j T U} :
    (∀ `{!tsintpy Σ ih s'}, ih s' → T ≃(s') U) →
    ▽{j,nil} T ≃{i,i'}(s) ▽{j,nil} U.
  Proof.
    move=> TU. apply teqv_tsub; split; apply tsub_guard=> *?; by rewrite TU.
  Qed.

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

  (** On [→( )] *)
  Lemma tsub_fun `{! j ≤ⁿ i, ! j' ≤ⁿ i', ! j ≤ⁿ j'} {s T U T' U'} :
    T' ⊑(s) T →  U ⊑(s) U' →  T →(j) U ⊑{i,i'}(s) T' →(j') U'.
  Proof.
    move=> T'T UU' ? /=. do 4 f_equiv; [by apply T'T|].
    rewrite twp_mono; [|apply UU']. rewrite !twpw_tinv_wsat_lt_tinv_wsat.
    iApply twpw_expand. iApply tinv_wsat_incl.
  Qed.
  Lemma teqv_fun `{! j ≤ⁿ i, ! j ≤ⁿ i'} {s T U T' U'} :
    T ≃(s) T' →  U ≃(s) U' →  T →(j) U ≃{i,i'}(s) T' →(j) U'.
  Proof.
    move=> TT' UU' ? /=. do 4 f_equiv; [by apply TT'|].
    rewrite !twpw_tinv_wsat_lt_tinv_wsat. by f_equiv.
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

  (** On [recᵗ:] *)
  Lemma teqv_rec `{! j ≤ⁿ i} {s T} : (recᵗ: j, T) ≃{i,_}(s) T /: (recᵗ: j, T).
  Proof. move=> ? /=. by rewrite rew_eq_hwf tintp_tbump. Qed.

  (** On [!ᵘ] *)
  Lemma teqv_subu `{! j <ⁿ i} {s T} : !ᵘ T ≃{i,j}(s) T.
  Proof. move=> ? /=. exact tintp_lt_tintp. Qed.
End conv.
