(** * On well-foundedness *)

From nola Require Export prelude.

(** Well-foundedness of the lexicographic order over [bool] *)
Lemma wf_bool_lexico : @well_founded bool lexico.
Proof.
  have ?: Acc lexico false by constructor; case.
  case; [|done]; constructor; case; by case.
Qed.

(** Well-foundedness of the usual order over [nat] *)
Lemma wf_nat_lt : well_founded (<).
Proof. exact lt_wf. Qed.

(** Well-foundedness of the usual order over [positive] *)
Lemma wf_positive_lt : well_founded (<)%positive.
Proof. apply (well_founded_lt_compat _ Pos.to_nat). lia. Qed.

(** Well-foundedness of the usual order over [N] *)
Lemma wf_N_lt : well_founded (<)%N.
Proof. apply (well_founded_lt_compat _ N.to_nat). lia. Qed.

(** Well-foundedness of the bounded order over [Z] *)
Lemma wf_Z_lt {z} : well_founded (λ a b, z ≤ a < b)%Z.
Proof. exact: Z.lt_wf. Qed.

(** Well-foundedness of the lexicographic order over pairs *)
Lemma wf_prod_lexico `{!Lexico A, !Lexico B} :
  @well_founded A lexico → @well_founded B lexico →
  @well_founded (A * B) lexico.
Proof.
  move=> wfA wfB [a +]. elim: (wfA a)=> {}a _ IH b. elim: (wfB b)=> {}b _ IH'.
  constructor=> [[??][/=?|/=[->?]]/=]; [exact: IH|exact: IH'].
Qed.

(** Well-foundedness of the lexicographic order over [sig] *)
Lemma wf_sig_lexico `{!Lexico A} {P : A → Prop} `{!∀ a, ProofIrrel (P a)} :
  @well_founded A lexico → @well_founded (sig P) lexico.
Proof. by apply (wf_projected _ proj1_sig). Qed.
