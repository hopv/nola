(** * Numeric types *)

From nola.examples.rust_halt Require Export type.

Section num.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [ty_int]: Integer type *)
  Definition pty_int : pty CON Σ Zₓ := λ n vl, ⌜vl = [ #n]⌝%cif.
  Definition ty_int : ty CON Σ Zₓ := ty_pty pty_int.
  (** [pty_int] satisfies [Pty] *)
  #[export] Instance pty_int_pty : Pty pty_int 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** [ty_nat]: Natural number type *)
  Definition pty_nat : pty CON Σ natₓ := λ n vl, ⌜vl = [ #n]⌝%cif.
  Definition ty_nat : ty CON Σ natₓ := ty_pty pty_nat.
  (** [pty_nat] satisfies [Pty] *)
  #[export] Instance ty_nat_pty : Pty pty_nat 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** [ty_bool]: Boolean type *)
  Definition pty_bool : pty CON Σ boolₓ := λ b vl, ⌜vl = [ #b]⌝%cif.
  Definition ty_bool : ty CON Σ boolₓ := ty_pty pty_bool.
  (** [pty_bool] satisfies [Pty] *)
  #[export] Instance ty_bool_pty : Pty pty_bool 1.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** Subtyping *)
  Lemma subty_nat_int {δ} : ⊢ subty δ ty_nat ty_int id.
  Proof. iApply (subty_pty pty_nat pty_int). by iIntros (??). Qed.
  Lemma subty_bool_nat {δ} :
    ⊢ subty δ ty_bool ty_nat (λ b, if b then 1 else 0).
  Proof. iApply (subty_pty pty_bool pty_nat). by iIntros ([|]?). Qed.

  (** Integer operations *)
  Lemma type_int (n : Z) {κ Xl Γ} :
    ⊢ type (Xl:=Xl) κ Γ #n (λ r, r ◁{0} ty_int ᵖ:: Γ)
        (λ post xl, post (n, xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre Γ". wp_value_head.
    iModIntro. iFrame "pre Γ". iPureIntro. eexists _. split=>//=.
  Qed.
  Lemma type_add_int v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_int; v' ◁{d'} ty_int]
        Γi Γr get getr) :
    ⊢ type κ Γi (v + v') (λ r, r ◁{0} ty_int ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_sub_int v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_int; v' ◁{d'} ty_int]
        Γi Γr get getr) :
    ⊢ type κ Γi (v - v') (λ r, r ◁{0} ty_int ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n - n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_int_eq v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_int; v' ◁{d'} ty_int]
        Γi Γr get getr) :
    ⊢ type κ Γi (v = v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_int_le v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_int; v' ◁{d'} ty_int]
        Γi Γr get getr) :
    ⊢ type κ Γi (v ≤ v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n ≤ n')%Z, getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.

  (** Natural number operations *)
  Lemma type_nat (n : nat) {κ Xl Γ} :
    ⊢ type (Xl:=Xl) κ Γ #n (λ r, r ◁{0} ty_nat ᵖ:: Γ)
        (λ post xl, post (n, xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre Γ". wp_value_head.
    iModIntro. iFrame "pre Γ". iPureIntro. eexists _. split=>//=.
  Qed.
  Lemma type_add_nat v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_nat; v' ◁{d'} ty_nat]
        Γi Γr get getr) :
    ⊢ type κ Γi (v + v') (λ r, r ◁{0} ty_nat ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>/=.
    { move=> ?. by rewrite eq eq'. } { do 3 f_equal. lia. }
  Qed.
  Lemma type_sub_nat v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_nat; v' ◁{d'} ty_nat]
        Γi Γr get getr) :
    ⊢ type κ Γi (v - v') (λ r, r ◁{0} ty_nat ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          n ≥ n' ∧ post (n - n', getr xl)')%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iExists (λ _, _). iSplit.
    { by iApply (proph_obs_impl with "pre")=>/= [?[??]]. }
    iSplit=>//. iExists _. iSplit. { iPureIntro=> ?. by rewrite eq eq' /=. }
    rewrite proph_obs_sat. iRevert "pre". iPureIntro. case=>/= [?+].
    rewrite eq eq'. case=> ??. do 3 f_equal. lia.
  Qed.
  Lemma type_nat_eq v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_nat; v' ◁{d'} ty_nat]
        Γi Γr get getr) :
    ⊢ type κ Γi (v = v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_nat_le v v' {κ d d'}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_nat; v' ◁{d'} ty_nat]
        Γi Γr get getr) :
    ⊢ type κ Γi (v ≤ v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n ≤ n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((? & eq & [= ->]) & (? & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_ndnat {κ Xl Γ} :
    ⊢ type (Xl:=Xl) κ Γ Ndnat (λ r, r ◁{0} ty_nat ᵖ:: Γ)
        (λ post xl, ∀ n, post (n ᵖ:: xl))%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre Γ".
    wp_apply twp_ndnat=>//. iIntros (?) "_ !>". iExists _.
    iSplit. { iApply (proph_obs_impl with "pre")=> ? post. apply post. }
    iSplit=>//=. by iExists _.
  Qed.

  (** Boolean operations *)
  Lemma type_bool (b : bool) {κ Xl Γ} :
    ⊢ type (Xl:=Xl) κ Γ #b (λ r, r ◁{0} ty_bool ᵖ:: Γ)
        (λ post xl, post (b, xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre Γ". wp_value_head.
    iModIntro. iFrame "pre Γ". iPureIntro. eexists _. split=>//=.
  Qed.
  Lemma type_eq_bool v v' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_bool; v' ◁{d'} ty_bool]
        Γi Γr get getr) :
    ⊢ type κ Γi (v = v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
      (λ post xl, let '(b, b', _)' := get xl in
        post (bool_decide (b = b'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((b & eq & [= ->]) & (b' & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. by case b; case b'.
  Qed.
  Lemma type_le_bool v v' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[v ◁{d} ty_bool; v' ◁{d'} ty_bool]
        Γi Γr get getr) :
    ⊢ type κ Γi (v ≤ v') (λ r, r ◁{0} ty_bool ᵖ:: Γr)
      (λ post xl, let '(b, b', _)' := get xl in
        post (negb b || b', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!>/= $ $ pre". rewrite tcx_extract.
    iIntros "/=[%Γf Γr]".
    destruct Γf as ((b & eq & [= ->]) & (b' & eq' & [= ->]) & _). wp_op.
    iModIntro. iFrame "pre Γr". iPureIntro. eexists _. split=>//= ?.
    rewrite eq eq'. by case b; case b'.
  Qed.

  (** If expression *)
  Lemma type_if v
    `(!EtcxExtract (Yl:=Xl) (Zl:=Yl) (v ◁{d} ty_bool) Γi Γr get getr)
    {Zl κ e e' Γo pre pre'} :
    type (Yl:=Zl) κ Γr e Γo pre -∗ type κ Γr e' Γo pre' -∗
      type κ Γi (if: v then e else e') Γo
        (λ post xl, if get xl then pre post (getr xl) else pre' post (getr xl)).
  Proof.
    rewrite /= type_unseal. iIntros "#type #type' !>/=" (????) "κ t #pre".
    rewrite etcx_extract. iIntros "/=[%vb Γr]".
    destruct vb as (b & eq & [= ->]).
    destruct b; wp_if;
      [iApply ("type" with "κ t [] Γr")|iApply ("type'" with "κ t [] Γr")];
      iApply (proph_obs_impl with "pre")=> ?; by rewrite eq.
  Qed.

  (** ** [nat_iter]: Iterating a function with a natural number counter *)
  Definition nat_iter : val :=
    rec: "nat_iter" ["f"; "n"; "x"] := if: "n" ≤ #0 then "x" else
      let: "n'" := "n" - #1 in "nat_iter" ["f"; "n'"; "f" ["n'"; "x"]].

  (** Predicate transformer for [nat_iter] *)
  Section pre_nat_iter.
    Context {X Zl} (pre : xpred (X :: Zl) → xpred (natₓ :: X :: Zl))
      (post : xpred (X :: Zl)).
    Fixpoint pre_nat_iter (n : nat) (x : X) (zl : xlist Zl) : Prop :=
      match n with 0 => post (x, zl)' |
        S n' => pre (λ '(x', zl')', pre_nat_iter n' x' zl') (n', x, zl)' end.
  End pre_nat_iter.
  (** Typing [nat_iter] *)
  Local Lemma type'_nat_iter {f : val} {κ d d' X T Zl v w Γ pre} :
    (∀ v w, type (Xl:=_::X::Zl) κ (v ◁{d} ty_nat ᵖ:: w ◁{d'} T ᵖ:: Γ)
      (f [v; w]%E) (λ r, r ◁{d'} T ᵖ:: Γ) pre) ⊢
    type κ (v ◁{d} ty_nat ᵖ:: w ◁{d'} T ᵖ:: Γ) (nat_iter [f; v; w]%E)
      (λ r, r ◁{d'} T ᵖ:: Γ)
      (λ post '(n, x, zl)', pre_nat_iter pre post n x zl).
  Proof.
    rewrite /= type_unseal.
    iIntros "#type !>/=" (?? postπ xlπ) "κ t pre (%vi & T & Γ)".
    destruct vi as (n & eq & [= ->]). setoid_rewrite eq. clear.
    iInduction n as [|n'] "IH" forall (postπ xlπ w); wp_rec; wp_op; wp_case.
    { iModIntro. do 2 iFrame. }
    wp_op. have -> : (S n' - 1)%Z = n' by lia. wp_let. wp_bind (f _).
    iDestruct ("type" with "κ t pre [T Γ]") as "twp"=>/=.
    { iFrame. by iExists _. }
    iApply (twp_wand with "twp"). iIntros (?) ">(% & κ & t & pre & T & Γ)".
    iApply ("IH" $! _ (λ _,(0,_)') with "κ t pre T Γ").
  Qed.
  Lemma type_nat_iter {κ X T} {f : val}
    `(!TcxExtract (Xl:=[_;X]) (Yl:=Yl) (Zl:=Zl) ᵖ[v ◁{d} ty_nat; w ◁{d'} T]
        Γi Γr get getr) {pre} :
    (∀ v w, type κ (v ◁{d} ty_nat ᵖ:: w ◁{d'} T ᵖ:: Γr) (f [v; w]%E)
      (λ r, r ◁{d'} T ᵖ:: Γr) pre) ⊢
    type κ Γi (nat_iter [f; v; w]%E) (λ r, r ◁{d'} T ᵖ:: Γr)
      (λ post yl, let '(n, x, _)' := get yl in
        pre_nat_iter pre post n x (getr yl))%type.
  Proof.
    rewrite type'_nat_iter /=. iIntros "type".
    iDestruct (type_in with "[] type") as "type"; by [iApply sub_tcx_extract|].
  Qed.
End num.
