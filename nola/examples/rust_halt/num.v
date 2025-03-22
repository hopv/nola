(** * Numeric types *)

From nola.examples.rust_halt Require Export type.

Section num.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [ty_int]: Integer type *)
  Definition pty_int : pty CON Σ Zₓ := pair 1 (λ (n : Z) vl, ⌜vl = [ #n]⌝%cif).
  Definition ty_int : ty CON Σ Zₓ := ty_pty pty_int.
  (** [pty_int] satisfies [Pty] *)
  #[export] Instance pty_int_pty : Pty pty_int.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** [ty_nat]: Natural number type *)
  Definition pty_nat : pty CON Σ natₓ :=
    pair 1 (λ (n : nat) vl, ⌜vl = [ #n]⌝%cif).
  Definition ty_nat : ty CON Σ natₓ := ty_pty pty_nat.
  (** [pty_nat] satisfies [Pty] *)
  #[export] Instance ty_nat_pty : Pty pty_nat.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** [ty_bool]: Boolean type *)
  Definition pty_bool : pty CON Σ boolₓ :=
    pair 1 (λ (b : bool) vl, ⌜vl = [ #b]⌝%cif).
  Definition ty_bool : ty CON Σ boolₓ := ty_pty pty_bool.
  (** [pty_bool] satisfies [Pty] *)
  #[export] Instance ty_bool_pty : Pty pty_bool.
  Proof. split=>/= *; [exact _|]. by iIntros "->". Qed.

  (** Trivial resolution over numeric types *)
  #[export] Instance resol_int {κ} : Resol ty_int κ (λ _, True).
  Proof. exact _. Qed.
  #[export] Instance resol_nat {κ} : Resol ty_nat κ (λ _, True).
  Proof. exact _. Qed.
  #[export] Instance resol_bool {κ} : Resol ty_bool κ (λ _, True).
  Proof. exact _. Qed.

  (** Subtyping *)
  Lemma subty_nat_int {δ} : ⊢ subty δ ty_nat ty_int id.
  Proof. iApply (subty_pty pty_nat pty_int)=>//. by iIntros (??). Qed.
  Lemma subty_bool_nat {δ} :
    ⊢ subty δ ty_bool ty_nat (λ b, if b then 1 else 0).
  Proof. iApply (subty_pty pty_bool pty_nat)=>//. by iIntros ([|]?). Qed.

  (** Literals *)
  #[export] Instance etcx_extract_int {Xl Γ} (n : Z) :
    EtcxExtract (Yl:=Xl) (#n ◁ ty_int) Γ Γ (λ _, n) id | 20.
  Proof.
    constructor. iIntros (??) "$". iExists _, 0. iSplit; [done|].
    rewrite /ty_int ty_pty_unseal /=. by iExists _.
  Qed.
  #[export] Instance etcx_extract_nat {Xl Γ} (n : nat) :
    EtcxExtract (Yl:=Xl) (#n ◁ ty_nat) Γ Γ (λ _, n) id | 20.
  Proof.
    constructor. iIntros (??) "$". iExists _, 0. iSplit; [done|].
    rewrite /ty_nat ty_pty_unseal /=. by iExists _.
  Qed.
  #[export] Instance etcx_extract_nat_zero {Xl Γ} :
    EtcxExtract (Yl:=Xl) (#0 ◁ ty_nat) Γ Γ (λ _, 0) id | 5.
  Proof. exact (etcx_extract_nat 0). Qed.
  #[export] Instance etcx_extract_nat_pos {Xl Γ} (n : positive) :
    EtcxExtract (Yl:=Xl) (#(Z.pos n) ◁ ty_nat) Γ Γ
      (λ _, Pos.to_nat n) id | 5.
  Proof. have ->: Z.pos n = Pos.to_nat n by lia. exact _. Qed.
  #[export] Instance etcx_extract_bool {Xl Γ} (b : bool) :
    EtcxExtract (Yl:=Xl) (#b ◁ ty_bool) Γ Γ (λ _, b) id | 20.
  Proof.
    constructor. iIntros (??) "$". iExists _, 0. iSplit; [done|].
    rewrite /ty_bool ty_pty_unseal /=. by iExists _.
  Qed.
  #[export] Instance etcx_extract_bool_true {Xl Γ} :
    EtcxExtract (Yl:=Xl) (#1 ◁ ty_bool) Γ Γ (λ _, true) id | 5.
  Proof. exact (etcx_extract_bool true). Qed.
  #[export] Instance etcx_extract_bool_false {Xl Γ} :
    EtcxExtract (Yl:=Xl) (#0 ◁ ty_bool) Γ Γ (λ _, false) id | 5.
  Proof. exact (etcx_extract_bool false). Qed.

  (** Integer operations *)
  Lemma type_add_int p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_int; p' ◁ ty_int] Γi Γr get getr) :
    ⊢ type κ Γi (p + p') (λ r, r ◁ ty_int ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_int ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_sub_int p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_int; p' ◁ ty_int] Γi Γr get getr) :
    ⊢ type κ Γi (p - p') (λ r, r ◁ ty_int ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n - n', getr xl)'%Z).
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_int ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_eq_int p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_int; p' ◁ ty_int] Γi Γr get getr) :
    ⊢ type κ Γi (p = p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_int /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.
  Lemma type_le_int p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_int; p' ◁ ty_int] Γi Γr get getr) :
    ⊢ type κ Γi (p ≤ p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n ≤ n')%Z, getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_int /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    by rewrite eq eq'.
  Qed.

  (** Natural number operations *)
  Lemma type_add_nat p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_nat; p' ◁ ty_nat] Γi Γr get getr) :
    ⊢ type κ Γi (p + p') (λ r, r ◁ ty_nat ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in post (n + n', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_nat ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//=.
    { move=> ?. by rewrite eq eq'. } { do 3 f_equal. lia. }
  Qed.
  Lemma type_sub_nat p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_nat; p' ◁ ty_nat] Γi Γr get getr) :
    ⊢ type κ Γi (p - p') (λ r, r ◁ ty_nat ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          n ≥ n' ∧ post (n - n', getr xl)')%type.
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_nat ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iExists (λ _, _). iSplit.
    { by iApply (proph_obs_impl with "pre")=>/= [?[??]]. }
    iSplit=>//. iExists _, 0. iSplit; [by rewrite of_path_val|]. iExists _.
    iSplit. { iPureIntro=> ?. by rewrite eq eq' /=. }
    rewrite proph_obs_sat. iRevert "pre". iPureIntro. case=>/= [?+].
    rewrite eq eq'. case=> ??. do 3 f_equal. lia.
  Qed.
  Lemma type_eq_nat p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_nat; p' ◁ ty_nat] Γi Γr get getr) :
    ⊢ type κ Γi (p = p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n = n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_nat /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_le_nat p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_nat; p' ◁ ty_nat] Γi Γr get getr) :
    ⊢ type κ Γi (p ≤ p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(n, n', _)' := get xl in
          post (bool_decide (n ≤ n'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_nat /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & ? & eq & [=->]) &
      (? & ? & ? & ? & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. lia.
  Qed.
  Lemma type_ndnat {κ Xl Γ} :
    ⊢ type (Xl:=Xl) κ Γ Ndnat (λ r, r ◁ ty_nat ᵖ:: Γ)
        (λ post xl, ∀ n, post (n ᵖ:: xl))%type.
  Proof.
    rewrite /ty_nat ty_pty_unseal type_unseal /=.
    iIntros (????) "!>/= $$ pre Γ". wp_apply twp_ndnat=>//. iIntros (?) "_ !>".
    iExists _. iSplit.
    { iApply (proph_obs_impl with "pre")=> ? post. apply post. }
    iSplit; [|done]. iExists _, 0. iSplit; [done|]=>/=. by iExists _.
  Qed.

  (** Boolean operations *)
  Lemma type_eq_bool p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_bool; p' ◁ ty_bool] Γi Γr
        get getr) :
    ⊢ type κ Γi (p = p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(b, b', _)' := get xl in
          post (bool_decide (b = b'), getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & b & eq & [=->]) &
      (? & ? & ? & b' & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    rewrite eq eq'. apply bool_decide_ext. by case b; case b'.
  Qed.
  Lemma type_le_bool p p' {κ}
    `(!TcxExtract (Yl:=Xl) (Zl:=Yl) ᵖ[p ◁ ty_bool; p' ◁ ty_bool] Γi Γr
        get getr) :
    ⊢ type κ Γi (p ≤ p') (λ r, r ◁ ty_bool ᵖ:: Γr)
        (λ post xl, let '(b, b', _)' := get xl in
          post (negb b || b', getr xl)').
  Proof.
    rewrite /= type_unseal. iIntros (????) "!> $$ pre".
    rewrite tcx_extract /ty_bool ty_pty_unseal /=. iIntros "[%Γf Γr]".
    destruct Γf as ((? & ? & ? & b & eq & [=->]) &
      (? & ? & ? & b' & eq' & [=->]) & _).
    wp_path p. wp_path p'. wp_op. iModIntro. iFrame "pre Γr". iPureIntro.
    eexists _, 0. split; [by rewrite of_path_val|]. eexists _. split=>//= ?.
    rewrite eq eq'. by case b; case b'.
  Qed.

  (** If expression *)
  Lemma type_if p
    `(!EtcxExtract (Yl:=Xl) (Zl:=Yl) (p ◁ ty_bool) Γi Γr get getr)
    {Zl κ e e' Γo pre pre'} :
    type (Yl:=Zl) κ Γr e Γo pre -∗ type κ Γr e' Γo pre' -∗
      type κ Γi (if: p then e else e') Γo
        (λ post xl, if get xl then pre post (getr xl) else pre' post (getr xl)).
  Proof.
    rewrite type_unseal. iIntros "#type #type' !>/=" (????) "κ t #pre".
    rewrite etcx_extract /ty_bool ty_pty_unseal /=. iIntros "[%vb Γr]".
    destruct vb as (? & ? & ? & b & eq & [=->]).
    destruct b; wp_path p; wp_if;
      [iApply ("type" with "κ t [] Γr")|iApply ("type'" with "κ t [] Γr")];
      iApply (proph_obs_impl with "pre")=> ?; by rewrite eq.
  Qed.
End num.
