(** * Weakest precondition *)

From nola.iris Require Export fupd.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.

(** ** What becomes [irisGS_gen] combined with an extra world satisfaction *)
Class irisGS'_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) := IrisG' {
  iris'_invGS :: invGS_gen hlc Σ;
  state_interp' : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  fork_post' : val Λ → iProp Σ;
  num_laters_per_step' : nat → nat;
  state_interp'_mono σ ns κs nt:
    state_interp' σ ns κs nt ⊢ |={∅}=> state_interp' σ (S ns) κs nt
}.

(** [irisGS_gen] made from [irisGS'_gen] and an extra world satisfaction *)
Program Definition IrisW `{!irisGS'_gen hlc Λ Σ}
  (W : iProp Σ) : irisGS_gen hlc Λ Σ := {|
  iris_invGS := iris'_invGS;
  state_interp σ ns ks nt := (W ∗ state_interp' σ ns ks nt)%I;
  fork_post := fork_post';
  num_laters_per_step := num_laters_per_step';
|}.
Next Obligation. iIntros "* [$ ?]". by iApply state_interp'_mono. Qed.

Local Transparent iris_invGS.
Local Notation wp_unseal := iris.program_logic.weakestpre.wp_aux.(seal_eq).
Local Notation twp_unseal :=
  iris.program_logic.total_weakestpre.twp_aux.(seal_eq).
Local Notation twp_pre' := iris.program_logic.total_weakestpre.twp_pre'.

(** ** [wpw]/[twpw]: [wp]/[twp] for [IrisW] *)
Notation wpw W := (@wp _ _ _ _ (@wp' _ _ _ (IrisW W))).
Notation twpw W := (@twp _ _ _ _ (@twp' _ _ _ (IrisW W))).

Section wpw.
  Context `{!irisGS'_gen hlc Λ Σ}.

  (** [wpw] is non-expansive over the world satisfaction *)
  Lemma wpw_ne {W W' n s E e Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ → wpw W s E e Φ ≡{n}≡ wpw W' s E e Ψ.
  Proof.
    move=> ? ΦΨ.
    enough (go : (wpw W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ wpw W').
    { etrans; [apply go|]. by f_equiv. }
    rewrite /wp/wp' wp_unseal=> ?. apply fixpoint_ne=> ????.
    rewrite /wp_pre/=. do 13 f_equiv; [done|]. do 12 f_equiv.
    apply step_fupdN_ne. by do 3 f_equiv.
  Qed.
  Lemma wpw_proper {W W' s E e Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ → wpw W s E e Φ ⊣⊢ wpw W' s E e Ψ.
  Proof. rewrite !equiv_dist=> ???. by apply wpw_ne. Qed.

  (** [twpw] is non-expansive over the world satisfaction *)
  Lemma twpw_ne {W W' n s E e Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ → twpw W s E e Φ ≡{n}≡ twpw W' s E e Ψ.
  Proof.
    move=> ? ΦΨ.
    enough (go : (twpw W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ twpw W').
    { etrans; [apply go|]. by f_equiv. }
    rewrite /twp/twp' twp_unseal=> ????.
    apply least_fixpoint_ne; [|done]=> ?[[??]?]. rewrite /twp_pre'/twp_pre/=.
    do 11 f_equiv; [done|]. by do 14 f_equiv.
  Qed.
  Lemma twpw_proper {W W' s E e Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ → twpw W s E e Φ ⊣⊢ twpw W' s E e Ψ.
  Proof. rewrite !equiv_dist=> ???. by apply twpw_ne. Qed.
End wpw.

(** Notation for [wpw]/[twpw] *)

Notation "WP[ W ] e @ s ; E {{ Φ } }" := (wpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E {{ Φ } }" := (wpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? {{ Φ } }" := (wpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e {{ Φ } }" := (wpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? {{ Φ } }" := (wpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "WP[ W ] e @ s ; E {{ v , Q } }" := (wpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E {{ v , Q } }" := (wpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? {{ v , Q } }" := (wpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e {{ v , Q } }" := (wpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "WP[ W ] e ? {{ v , Q } }" := (wpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E {{ Φ }})
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E {{ Φ }})
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?{{ Φ }})
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e {{ Φ }})
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?{{ Φ }})
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E {{ Φ }}) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E {{ Φ }}) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?{{ Φ }}) : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e {{ Φ }}) : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e ?{{ Φ }}) : stdpp_scope.

Notation "WP[ W ] e @ s ; E [{ Φ } ]" := (twpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E [{ Φ } ]" := (twpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? [{ Φ } ]" := (twpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e [{ Φ } ]" := (twpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? [{ Φ } ]" := (twpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "WP[ W ] e @ s ; E [{ v , Q } ]" := (twpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E [{ v , Q } ]" := (twpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? [{ v , Q } ]" := (twpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e [{ v , Q } ]" := (twpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "WP[ W ] e ? [{ v , Q } ]" := (twpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.

Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' ? [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' ? [[{  '[hv' x  ..  y ,   RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.

Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.

Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E [{ Φ }])
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E [{ Φ }])
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?[{ Φ }])
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e [{ Φ }])
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?[{ Φ }])
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E [{ Φ }]) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E [{ Φ }]) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?[{ Φ }]) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e [{ Φ }]) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e ?[{ Φ }]) : stdpp_scope.
