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
  Lemma type_add_int {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_int; v' ◁ ty_int] (v + v') (λ r, ᵖ[r ◁ ty_int])
      (λ post '(n, n', _)', post ᵖ[n + n']%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. by rewrite eq eq'.
  Qed.
  Lemma type_sub_int {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_int; v' ◁ ty_int] (v - v') (λ r, ᵖ[r ◁ ty_int])
      (λ post '(n, n', _)', post ᵖ[n - n']%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. by rewrite eq eq'.
  Qed.
  Lemma type_eq_int {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_int; v' ◁ ty_int] (v = v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(n, n', _)', post ᵖ[bool_decide (n = n')]%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. by rewrite eq eq'.
  Qed.
  Lemma type_le_int {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_int; v' ◁ ty_int] (v ≤ v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(n, n', _)', post ᵖ[bool_decide (n ≤ n')]%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _.
    iSplit=>//=. iPureIntro=> ?. by rewrite eq eq'.
  Qed.

  (** Natural number operations *)
  Lemma type_add_nat {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_nat; v' ◁ ty_nat] (v + v') (λ r, ᵖ[r ◁ ty_nat])
      (λ post '(n, n', _)', post ᵖ[n + n']).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _.
    iSplit=>//=; iPureIntro=> >. { by rewrite eq eq'. } { do 3 f_equal. lia. }
  Qed.
  Lemma type_sub_nat {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_nat; v' ◁ ty_nat] (v - v') (λ r, ᵖ[r ◁ ty_nat])
      (λ post '(n, n', _)', n ≥ n' ∧ post ᵖ[n - n'])%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iExists (λ _, _). iSplit.
    { by iApply (proph_obs_impl with "pre")=>/= [?[??]]. }
    iSplit=>//. iExists 0, _. iSplit. { iPureIntro=> ?. by rewrite eq eq'. }
    rewrite proph_obs_sat. iRevert "pre". iPureIntro. case=>/= [?+].
    rewrite eq eq'. case=> ??. do 3 f_equal. lia.
  Qed.
  Lemma type_eq_nat {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_nat; v' ◁ ty_nat] (v = v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(n, n', _)', post ᵖ[bool_decide (n = n')]%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_le_nat {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_nat; v' ◁ ty_nat] (v ≤ v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(n, n', _)', post ᵖ[bool_decide (n ≤ n')]%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & ? & eq & [= ->]) & (? & ? & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_ndnat {α v v'} :
    ⊢ type α ᵖ[] Ndnat (λ r, ᵖ[r ◁ ty_nat]) (λ post _, ∀ n, post ᵖ[n])%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre _".
    wp_apply twp_ndnat=>//. iIntros (?) "_ !>". iExists _.
    iSplit. { iApply (proph_obs_impl with "pre")=> ? post. apply post. }
    iSplit=>//. by iExists 0, _.
  Qed.

  (** Boolean operations *)
  Lemma type_eq_bool {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_bool; v' ◁ ty_bool] (v = v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(b, b', _)', post ᵖ[bool_decide (b = b')]%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & b & eq & [= ->]) & (? & b' & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. rewrite eq eq'. apply bool_decide_ext. by case b; case b'.
  Qed.
  Lemma type_le_bool {α v v'} :
    ⊢ type α ᵖ[v ◁ ty_bool; v' ◁ ty_bool] (v ≤ v') (λ r, ᵖ[r ◁ ty_bool])
      (λ post '(b, b', _)', post ᵖ[negb b || b']%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $$ pre".
    iIntros (((? & b & eq & [= ->]) & (? & b' & eq' & [= ->]) & _)). wp_op.
    iModIntro. iFrame "pre". iSplit=>//. iExists 0, _. iSplit=>//=.
    iPureIntro=> ?. rewrite eq eq'. by case b; case b'.
  Qed.

  (** If expression *)
  Lemma type_if {Xl Yl α v v' Γi e e' Γo pre pre'} :
    type (Xl:=Xl) (Yl:=Yl) α Γi e Γo pre -∗ type α Γi e' Γo pre' -∗
      type α (v ◁ ty_bool ᵖ:: Γi) (if: v then e else e') Γo
        (λ post '(b, xl)', if b then pre post xl else pre' post xl).
  Proof.
    rewrite /= type_unseal. iIntros "#type #type' !>/=" (????) "α t #pre [v Γ]".
    iDestruct "v" as %(? & b & eq & [= ->]).
    destruct b; wp_if;
      [iApply ("type" with "α t [] Γ")|iApply ("type'" with "α t [] Γ")];
      iApply (proph_obs_impl with "pre")=> ?; by rewrite eq.
  Qed.
End num.
