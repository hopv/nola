(** * Numeric types *)

From nola.examples.rust_halt Require Export type.
Import ProdNotation PlistNotation BigSepPLNotation ModwNotation WpwNotation
  iPropAppNotation ProphNotation LftNotation CsemNotation.

Implicit Type (sz d : nat) (X Y : xty) (t : thread_id) (v : val) (e : expr)
  (l : loc) (α : lft) (CON : cifcon) (Σ : gFunctors).

Section num.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  (** ** [ty_int]: Integer type *)
  Definition pty_int : pty CON Σ Zₓ := λ n vl, ⌜vl = [ #n]⌝%cif.
  Definition ty_int : ty CON Σ Zₓ := ty_pty pty_int.
  (** [ty_int] satisfies [Pty] *)
  #[export] Instance ty_int_pty : Pty pty_int 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** ** [ty_nat]: Natural number type *)
  Definition pty_nat : pty CON Σ natₓ := λ n vl, ⌜vl = [ #n]⌝%cif.
  Definition ty_nat : ty CON Σ natₓ := ty_pty pty_nat.
  (** [ty_nat] satisfies [Pty] *)
  #[export] Instance ty_nat_pty : Pty pty_nat 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** ** [ty_bool]: Boolean type *)
  Definition pty_bool : pty CON Σ boolₓ := λ b vl, ⌜vl = [ #b]⌝%cif.
  Definition ty_bool : ty CON Σ boolₓ := ty_pty pty_bool.
  (** [ty_bool] satisfies [Pty] *)
  #[export] Instance ty_bool_pty : Pty pty_bool 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** Subtyping *)
  Lemma subty_nat_int {α δ} : ⊢ subty δ ty_nat ty_int id.
  Proof. iApply (subty_pty pty_nat pty_int). by iIntros (??). Qed.
  Lemma subty_bool_nat {α δ} :
    ⊢ subty δ ty_bool ty_nat (λ b, if b then 1 else 0).
  Proof. iApply (subty_pty pty_bool pty_nat). by iIntros ([|]?). Qed.

  (** Integer operations *)
  Lemma type_add_int v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_int; v' ◁ ty_int] Γi Γr get getr} :
    ⊢ type α Γi (v + v') (λ r, r ◁ ty_int ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_sub_int v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_int; v' ◁ ty_int] Γi Γr get getr} :
    ⊢ type α Γi (v - v') (λ r, r ◁ ty_int ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in post (n - n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_eq_int v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_int; v' ◁ ty_int] Γi Γr get getr} :
    ⊢ type α Γi (v = v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in
        post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_le_int v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_int; v' ◁ ty_int] Γi Γr get getr} :
    ⊢ type α Γi (v ≤ v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in
        post (bool_decide (n ≤ n')%Z, getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    by rewrite eq eq'.
  Qed.

  (** Natural number operations *)
  Lemma type_add_nat v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_nat; v' ◁ ty_nat] Γi Γr get getr} :
    ⊢ type α Γi (v + v') (λ r, r ◁ ty_nat ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>/=.
    { move=> ?. by rewrite eq eq'. } { do 3 f_equal. lia. }
  Qed.
  Lemma type_sub_nat v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_nat; v' ◁ ty_nat] Γi Γr get getr} :
    ⊢ type α Γi (v - v') (λ r, r ◁ ty_nat ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in
        n ≥ n' ∧ post (n - n', getr xl)')%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iExists (λ _, _). iSplit.
    { by iApply (proph_obs_impl with "pre")=>/= [?[??]]. }
    iSplit=>//. iExists 0, _. iSplit.
    { iPureIntro=> ?. by rewrite eq eq' /=. }
    rewrite proph_obs_sat. iRevert "pre". iPureIntro. case=>/= [?+].
    rewrite eq eq'. case=> ??. do 3 f_equal. lia.
  Qed.
  Lemma type_eq_nat v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_nat; v' ◁ ty_nat] Γi Γr get getr} :
    ⊢ type α Γi (v = v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in
        post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_le_nat v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_nat; v' ◁ ty_nat] Γi Γr get getr} :
    ⊢ type α Γi (v ≤ v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(n, n', _)' := get xl in
        post (bool_decide (n ≤ n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_ndnat {α Xl Γ} :
    ⊢ type (Xl:=Xl) α Γ Ndnat (λ r, r ◁ ty_nat ᵖ:: Γ)
      (λ post xl, ∀ n, post (n ᵖ:: xl))%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre Γ".
    wp_apply twp_ndnat=>//. iIntros (?) "_ !>". iExists _.
    iSplit. { iApply (proph_obs_impl with "pre")=> ? post. apply post. }
    iSplit=>//=. by iExists 0, _.
  Qed.

  (** Boolean operations *)
  Lemma type_eq_bool v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_bool; v' ◁ ty_bool]
        Γi Γr get getr} :
    ⊢ type α Γi (v = v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(b, b', _)' := get xl in
        post (bool_decide (b = b'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & b & eq & [= ->]) & (? & b' & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. by case b; case b'.
  Qed.
  Lemma type_le_bool v v' {α}
    `{!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁ ty_bool; v' ◁ ty_bool]
        Γi Γr get getr} :
    ⊢ type α Γi (v ≤ v') (λ r, r ◁ ty_bool ᵖ:: Γr)
      (λ post xl, let '(b, b', _)' := get xl in
        post (negb b || b', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & b & eq & [= ->]) & (? & b' & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists 0, _. split=>//= ?.
    rewrite eq eq'. by case b; case b'.
  Qed.

  (** If expression *)
  Lemma type_if v
    `{!EtcxExtract (Yl:=Xl) (Zl:=Yl) (v ◁ ty_bool) Γi Γr get getr}
    {Zl α e e' Γo pre pre'} :
    type (Yl:=Zl) α Γr e Γo pre -∗ type α Γr e' Γo pre' -∗
      type α Γi (if: v then e else e') Γo
        (λ post xl, if get xl then pre post (getr xl) else pre' post (getr xl)).
  Proof.
    rewrite /= type_unseal. iIntros "#type #type' !>/=" (????) "α t #pre".
    rewrite etcx_extract. iIntros "/=[%vb Γr]".
    destruct vb as (? & b & eq & [= ->]).
    destruct b; wp_if;
      [iApply ("type" with "α t [] Γr")|iApply ("type'" with "α t [] Γr")];
      iApply (proph_obs_impl with "pre")=> ?; by rewrite eq.
  Qed.
End num.
