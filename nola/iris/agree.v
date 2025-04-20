(** * Utility for [agree] *)

From nola Require Export prelude.
From iris.algebra Require Export agree.

Implicit Type SI : sidx.

Section agree.
  Context {SI}.

  (** Turn [agree] to an element *)
  Local Lemma of_eq_true_false {A} : true = false → A. Proof. done. Qed.
  Definition unagree {A} (ag : agree A) : A :=
    match ag with
    | {| agree_car := a :: _ |} => a
    | {| agree_car := []; agree_not_nil := p |} => of_eq_true_false p
    end.

  (** Modify [unagree] under validity *)
  Lemma unagree_dist {A : ofe} {ag ag' : agree A} {n} :
    ✓{n} ag → ag ≡{n}≡ ag' → unagree ag ≡{n}≡ unagree ag'.
  Proof.
    move: ag ag'=> [[//|??]?][[//|??]?]/= /agree_validN_def val [_ go].
    move: (go _ (elem_of_list_here _ _))=> [a[el ?]].
    move: (val _ _ el (elem_of_list_here _ _))=> ?. by etrans.
  Qed.
  Lemma unagree_includedN {A : ofe} {ag ag' : agree A} {n} :
    ✓{n} ag → ag' ≼{n} ag → unagree ag ≡{n}≡ unagree ag'.
  Proof.
    move: ag ag'=> [[//|??]?][[//|??]?]/= /agree_validN_def val [?[_ go]].
    move: (go _ (elem_of_list_here _ _))=> [a[el ?]].
    move: (val _ _ el (elem_of_list_here _ _))=> ?. by etrans.
  Qed.
  Lemma unagree_equiv {A : ofe} {ag ag' : agree A} :
    ✓ ag → ag ≡ ag' → unagree ag ≡ unagree ag'.
  Proof. move=> ??. apply equiv_dist=> ?. exact: unagree_dist. Qed.
  (** Modify [unagree] with [≼] *)
  Lemma unagree_included {A : ofe} {ag ag' : agree A} :
    ✓ ag → ag' ≼ ag → unagree ag ≡ unagree ag'.
  Proof.
    move=> ??. apply equiv_dist=> ?. apply unagree_includedN; [done|].
    exact: cmra_included_includedN.
  Qed.

  (** [unagree] over [to_agree] *)
  Lemma unagree_to_agree {A : ofe} {a : A} : unagree (to_agree a) = a.
  Proof. done. Qed.

  (** [to_agree] over [unagree] *)
  Lemma to_agree_unagree {A : ofe} {ag : agree A} : to_agree (unagree ag) ≼ ag.
  Proof.
    exists ag. case: ag=> l +. case: l; [done|]=>/= >.
    split=>/= a ?; exists a; set_solver.
  Qed.
End agree.
