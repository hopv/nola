(** * Ackermann function *)

From nola.examples.rust_halt Require Export num mutref core.

(** Ackermann function in Coq *)
Fixpoint ack (m n : nat) : nat :=
  match m with
  | 0 => S n
  | S m' =>
      (fix ack' n := match n with 0 => ack m' 1 | S n' => ack m' (ack' n') end)
      n
  end.

(** Ackermann function in λRust *)
Definition ackr : val := rec: "ack" ["m"; "n"] :=
  if: "m" = #0 then "n" + #1
  else if: "n" = #0 then "ack" ["m" - #1; #1]
  else "ack" ["m" - #1; "ack" ["m"; "n" - #1]].

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
      (λ post '(m', n', xl)', m' = m ∧ (n' = n ∧ post (ack m' n', xl)'))%type;
      last first.
    { move=> goal.
      iApply (type_real (X:=natₓ) (Yl':=natₓ::_) (Zl:=natₓ::_) q nat
        (λ post '(n, m, xl)', post (ack m n, xl)')
        (etcx_extract_tl etcx_extract_hd)).
      iIntros (n').
      iApply (type_real (X:=natₓ) (Yl':=natₓ::_) (Zl:=natₓ::_) p nat
        (λ post '(m, n, xl)', n = n' ∧ post (ack m n, xl)')
        (etcx_extract_tl etcx_extract_hd)).
      iIntros (m'). iApply goal. }
    clear p q Xl Γ. elim.
    { move=> n p q Xl Γ. iApply type_pre; last first.
      { type_path p as (?). type_path q (etcx_extract_tl _) as (?).
        iApply type_call. type_bind (_ = _)%E.
        { iApply type_eq_nat.
          apply: tcx_extract_cons; [exact: etcx_extract_tl|exact: _]. }
        iIntros (veq). iApply (type_if veq _); [|by iApply type_false].
        iApply type_add_nat. }
      move=>/= ?[?[??]][->[->/=]]. by have ->: n + Pos.to_nat 1 = S n by lia. }
    move=> m IH. elim.
    { move=> p q ??. iApply type_pre; last first.
      { type_path p as (v). type_path q (etcx_extract_tl _) as (?).
        iApply type_call. iApply (type_copy v (etcx_extract_tl _)).
        type_bind (_ = _)%E.
        { iApply type_eq_nat.
          apply: tcx_extract_cons; [exact: etcx_extract_tl|exact: _]. }
        iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
        type_bind (_ = _)%E.
        { iApply type_eq_nat.
          apply: tcx_extract_cons; [exact: etcx_extract_tl|exact: _]. }
        iIntros (veq'). iApply (type_if veq' _); [|by iApply type_false].
        type_bind (_ - _)%E; [by iApply type_sub_nat|]. iIntros (?).
        iApply type_in; [|by iApply IH]. iApply sub_leak_rest. }
      move=>/= ?[?[??]][->[->/=?]]. do 2 (split; [lia|]).
      by have ->: m - 0 = m by lia. }
    move=> n IH' p q ??. iApply type_pre; last first.
    { type_path p as (v). type_path q (etcx_extract_tl _) as (v').
      iApply type_call. iApply (type_copy v' _).
      iApply (type_copy v (etcx_extract_tl (etcx_extract_tl _))).
      type_bind (_ = _)%E.
      { iApply type_eq_nat. apply: tcx_extract_cons; exact: _. }
      iIntros (veq). iApply (type_if veq _); [by iApply type_false|].
      type_bind (_ = _)%E.
      { iApply type_eq_nat.
        apply: tcx_extract_cons; [exact: etcx_extract_tl|exact: _]. }
      iIntros (veq'). iApply (type_if veq' _); [by iApply type_false|].
      iApply (type_copy v _). type_bind (_ - _)%E.
      { iApply type_sub_nat. apply: tcx_extract_cons; exact: _. }
      iIntros (?). type_bind (_ - _)%E.
      { iApply type_sub_nat.
        apply: tcx_extract_cons;
          [exact (etcx_extract_tl (etcx_extract_tl _))|exact _]. }
      iIntros (?). type_bind (ackr [v; _])%E.
      { iApply type_in; [|by iApply IH']. iApply sub_leak_rest.
        apply: tcx_extract_cons; [exact (etcx_extract_tl (etcx_extract_tl _))|].
        exact _. }
      iIntros (?). iApply type_in; [|by iApply IH]. iApply sub_leak_rest.
      apply: tcx_extract_cons; [exact: etcx_extract_tl|exact _]. }
    move=>/= ?[?[??]][->[->/=?]]. do 2 (do 2 (split; [lia|]))=> _.
    have ->: m - 0 = m by lia. by have ->: n - 0 = n by lia.
  Qed.
End ack.
