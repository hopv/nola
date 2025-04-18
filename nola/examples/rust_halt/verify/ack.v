(** * Ackermann function *)

From nola.examples.rust_halt Require Export core num ptrs_more.

(** Ackermann function in Coq *)
Fixpoint ack (m n : nat) : nat :=
  match m with
  | 0 => S n
  | S m' =>
      (fix ack' n := match n with 0 => ack m' 1 | S n' => ack m' (ack' n') end)
      n
  end.

(** Ackermann function in λRust *)
Definition ackr : val := rec: "ackr" ["m"; "n"] :=
  if: "m" = #0 then "n" + #1
  else if: "n" = #0 then "ackr" ["m" - #1; #1]
  else "ackr" ["m" - #1; "ackr" ["m"; "n" - #1]].

(** Ackermann function that returns the output through a mutable reference *)
Definition ackmut : val := rec: "ackmut" ["m"; "n"; "r"] :=
  if: "m" = #0 then "r" <- "n" + #1
  else if: "n" = #0 then "ackmut" ["m" - #1; #1; "r"]
  else "ackmut" ["m"; "n" - #1; "r"];; "ackmut" ["m" - #1; !"r"; "r"].

Section ack.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !rust_haltJ CON JUDG Σ,
    !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !rust_haltCS CON JUDG Σ,
    !rust_haltJS CON JUDG Σ}.

  (** Typing [ackr] *)
  Lemma type_ackr {κ p q Xl Γ} :
    ⊢ type (Yl:=_ :: Xl) κ (p ◁ ty_nat ᵖ:: q ◁ ty_nat ᵖ:: Γ) (ackr [p; q])
        (λ r, r ◁ ty_nat ᵖ:: Γ) (λ post '(m, n, xl)', post (ack m n, xl)').
  Proof.
    have: ∀ (m n : nat) (p q : path) Xl Γ, ⊢ type (Yl:=_ :: Xl) κ
      (p ◁ ty_nat ᵖ:: q ◁ ty_nat ᵖ:: Γ) (ackr [p; q]) (λ r, r ◁ ty_nat ᵖ:: Γ)
      (λ post '(m', n', xl)', m' = m ∧ n' = n ∧ post (ack m' n', xl)')%type;
      last first.
    { move=> goal. iApply type_pre; last first.
      { iApply (type_real (Yl':=_::_) q nat (λ _ '(_, _, _)', _)). iIntros (n).
        iApply type_pre; last first.
        { iApply (type_real (Yl':=_::_) p nat (λ _ '(_, _, _)', _ = n ∧ _)).
          iIntros (?). iApply type_pre; [|by iApply goal]. by move=>/= ?[?[??]].
          }
        by move=>/= ?[?[??]]/=. }
      by move=>/=. }
    clear p q Xl Γ. elim.
    { move=> n p q Xl Γ. iApply type_pre; last first.
      { type_path p as (?). type_path q as (?). iApply type_call.
        type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
        iIntros (veq). iApply (type_if veq _); [|by iApply type_false].
        iApply type_add_nat. }
      move=>/= ?[?[??]][->[->/=]]. by have ->: n + Pos.to_nat 1 = S n by lia. }
    move=> m IH. elim.
    { move=> p q ??. iApply type_pre; last first.
      { type_path p as (v). type_path q as (?). iApply type_call.
        iApply (type_copy v); [solve_extract|exact _|]. type_bind (_ = _)%E.
        { iApply type_eq_nat. solve_extract. }
        iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
        type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
        iIntros (veq'). iApply (type_if veq' _); [|by iApply type_false].
        type_bind (_ - _)%E; [by iApply type_sub_nat|]. iIntros (?).
        iApply type_in; [|by iApply IH]. iApply sub_leak_rest. }
      move=>/= ?[?[??]][->[->/=?]]. do 2 (split; [lia|]).
      by have ->: m - 0 = m by lia. }
    move=> n IH' p q ??. iApply type_pre; last first.
    { type_path p as (v). type_path q as (v'). iApply type_call.
      iApply (type_copy v' _). iApply (type_copy v); [solve_extract|exact _|].
      type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
      iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
      type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
      iIntros (veq'). iApply (type_if veq' _); [by iApply type_false|].
      iApply (type_copy v _). type_bind (_ - _)%E.
      { iApply type_sub_nat. solve_extract. }
      iIntros (?). type_bind (_ - _)%E. { iApply type_sub_nat. solve_extract. }
      iIntros (?). type_bind (ackr [v; _])%E.
      { iApply type_in; [|by iApply IH']. iApply sub_leak_rest. solve_extract. }
      iIntros (?). iApply type_in; [|by iApply IH]. iApply sub_leak_rest.
      solve_extract. }
    move=>/= ?[?[??]][->[->/=?]]. do 2 (do 2 (split; [lia|]))=> _.
    have ->: m - 0 = m by lia. by have ->: n - 0 = n by lia.
  Qed.

  (** Typing [ackmut] *)
  Lemma type_ackmut `(!LftIncl κ α) {p q r Xl Γ} :
    ⊢ type (Yl:=Xl) κ
        (p ◁ ty_nat ᵖ:: q ◁ ty_nat ᵖ:: r ◁ ty_mutref α ty_nat ᵖ:: Γ)
        (ackmut [p; q; r]) (λ _, Γ)
        (λ post '(m, n, (_, o)', xl)', o = ack m n → post xl)%type.
  Proof.
    have: ∀ (m n : nat) `(!LftIncl κ α) (p q r : path) Xl Γ, ⊢ type (Yl:=Xl) κ
      (p ◁ ty_nat ᵖ:: q ◁ ty_nat ᵖ:: r ◁ ty_mutref α ty_nat ᵖ:: Γ)
      (ackmut [p; q; r]) (λ _, Γ)
      (λ post '(m', n', (_, o)', xl)', m' = m ∧ n' = n ∧
        (o = ack m' n' → post xl))%type;
      last first.
    { move=> goal. iApply type_pre; last first.
      { iApply (type_real (Yl':=_::_) q nat (λ _ '(_, _, _)', _));
          [solve_extract|exact _|].
        iIntros (n). iApply type_pre; last first.
        { iApply (type_real (Yl':=_::_::_) p nat
            (λ _ '(_, _, _, _)', _ = n ∧ _)).
          iIntros (?). iApply type_pre; [|by iApply goal].
          by move=>/= ?[?[?[??]]]. }
       by move=>/= ?[?[??]]/=. }
      by move=>/=. }
    clear κ α LftIncl0 p q r Xl Γ. elim.
    { move=> n κ α ? p q r Xl Γ. iApply type_pre; last first.
      { type_path p as (?). type_path q as (?). type_path r as (?).
        iApply type_call. type_bind (_ = _)%E.
        { iApply type_eq_nat. solve_extract. }
        iIntros (veq). iApply (type_if veq _); [|by iApply type_false].
        type_bind (_ + _)%E. { iApply type_add_nat. solve_extract. }
        iIntros (?). iApply type_out.
        { iApply type_write;
            [solve_extract|exact: write_mutref|exact _..|done|].
          iApply subty_refl. }
        iIntros (?). iApply (sub_leak ᵖ[_]).
        exact: (resol_tcx_cons_owned _ (Yl:=[])). }
      move=>/= ?[?[??]][->[->/=]] to _. have ->: n + Pos.to_nat 1 = S n by lia.
      move=> [? _]. auto. }
    move=> m IH. elim.
    { move=> κ α ? p q r ??. iApply type_pre; last first.
      { type_path p as (v). type_path q as (?). type_path r as (?).
        iApply type_call. iApply (type_copy v); [solve_extract|exact _|].
        type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
        iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
        type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
        iIntros (veq'). iApply (type_if veq' _); [|by iApply type_false].
        type_bind (_ - _)%E. { iApply type_sub_nat. solve_extract. }
        iIntros (?). iApply type_in; [|by iApply IH]. iApply sub_leak_rest.
        solve_extract. }
      move=>/= ?[?[??]][->[->/=?]]. do 2 (split; [lia|]).
      by have ->: m - 0 = m by lia. }
    move=> n IH' κ α ? p q r ??. iApply type_pre; last first.
    { type_path p as (v). type_path q as (v'). type_path r as (?).
      iApply type_call. iApply (type_copy v'); [solve_extract|exact _|].
      iApply (type_copy v); [solve_extract|exact _|].
      type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
      iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
      type_bind (_ = _)%E. { iApply type_eq_nat. solve_extract. }
      iIntros (veq'). iApply (type_if veq' _); [by iApply type_false|].
      iApply (type_copy v _). type_bind (_ - _)%E.
      { iApply type_sub_nat. solve_extract. }
      iIntros (?). iApply type_lft_new. iIntros (β). iApply type_seq.
      { iApply type_out.
        { iApply (type_lft_use β); [solve_extract|].
          iApply (type_reborrow _ (α ⊓ β)); [solve_extract|exact _|].
          iApply type_in; [|iApply (IH' _ (α ⊓ β))]. iApply sub_leak_rest.
          solve_extract. }
        iIntros (?). iApply sub_refl. }
      iIntros (?). iApply type_lft_end; [solve_extract|]. iIntros "!> #†".
      iApply type_retrieve; [solve_extract|exact _|..].
      { rewrite lft_incl_dead //. exact lft_incl_meet_r. }
      type_bind (_ - _)%E. { iApply type_sub_nat. solve_extract. }
      iIntros (?). type_bind (! _)%E.
      { iApply type_read; [solve_extract|exact read_mutref|exact _|done]. }
      iIntros (?). iApply type_in; [|by iApply IH]. iApply sub_leak_rest.
      solve_extract. }
    move=>/= ?[?[?[[??]?]]][->[->/=?]]. have ->: m - 0 = m by lia.
    have ->: n - 0 = n by lia. split; [lia|]=> ? _. (do 2 split=>//)=> ->.
    split; [lia|done].
  Qed.
End ack.
