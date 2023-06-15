(** * Weakest precondition *)

From nola.iris Require Export upd.
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
Program Definition IrisW `{!irisGS'_gen hlc Λ Σ} (W : iProp Σ)
  : irisGS_gen hlc Λ Σ := {|
  iris_invGS := iris'_invGS;
  state_interp σ ns ks nt := (W ∗ state_interp' σ ns ks nt)%I;
  fork_post := fork_post';
  num_laters_per_step := num_laters_per_step';
|}.
Next Obligation. iIntros "* [$ ?]". by iApply state_interp'_mono. Qed.

Local Transparent iris_invGS.
Local Notation wp_unseal := weakestpre.wp_aux.(seal_eq).
Local Notation twp_unseal := total_weakestpre.twp_aux.(seal_eq).
Local Notation twp_pre' := total_weakestpre.twp_pre'.

(** ** [wpw]/[twpw]: [wp]/[twp] for [IrisW] *)
Notation wpw W := (@wp _ _ _ _ (@wp' _ _ _ (IrisW W))).
Notation twpw W := (@twp _ _ _ _ (@twp' _ _ _ (IrisW W))).

(** ** Notation for [wpw]/[twpw] *)

Notation "WP[ W ] e @ s ; E {{ Φ } }" := (wpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ s ; E [{ Φ } ]" := (twpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E {{ Φ } }" := (wpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E [{ Φ } ]" := (twpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? {{ Φ } }" := (wpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? [{ Φ } ]" := (twpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e {{ Φ } }" := (wpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e [{ Φ } ]" := (twpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? {{ Φ } }" := (wpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? [{ Φ } ]" := (twpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "WP[ W ] e @ s ; E {{ v , Q } }" := (wpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ s ; E [{ v , Q } ]" := (twpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E {{ v , Q } }" := (wpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E [{ v , Q } ]" := (twpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? {{ v , Q } }" := (wpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? [{ v , Q } ]" := (twpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e {{ v , Q } }" := (wpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "WP[ W ] e [{ v , Q } ]" := (twpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "WP[ W ] e ? {{ v , Q } }" := (wpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e ? [{ v , Q } ]" := (twpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' ? [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' ? [[{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' @  E  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' @  E  '/' ? [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.
Notation "{{{ P } } } [ W ] e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]  '/  ' e  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]  '/  ' e  '/' ? [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ] e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?[{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e ?[{ Φ }]) : stdpp_scope.

Section wpw.
  Context `{!irisGS'_gen hlc Λ Σ}.

  (** [wpw] is non-expansive over the world satisfaction *)
  Lemma wpw_ne {e s E W W' Φ Ψ n} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W] e @ s; E {{ Φ }})%I ≡{n}≡ (WP[W'] e @ s; E {{ Ψ }})%I.
  Proof.
    move=> ? ΦΨ.
    enough (go : (wpw W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ wpw W').
    { etrans; [apply go|]. by f_equiv. }
    rewrite /wp/wp' wp_unseal=> ?. apply fixpoint_ne=> ????.
    rewrite /wp_pre/=. do 13 f_equiv; [done|]. do 12 f_equiv.
    apply step_fupdN_ne. by do 3 f_equiv.
  Qed.
  Lemma wpw_proper {e s E W W' Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W] e @ s; E {{ Φ }} ⊣⊢ WP[W'] e @ s; E {{ Ψ }}.
  Proof. rewrite !equiv_dist=> ???. by apply wpw_ne. Qed.

  (** [twpw] is non-expansive over the world satisfaction *)
  Lemma twpw_ne {e s E W W' Φ Ψ n} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W] e @ s; E [{ Φ }])%I ≡{n}≡ (WP[W'] e @ s; E [{ Ψ }])%I.
  Proof.
    move=> ? ΦΨ.
    enough (go : (twpw W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ twpw W').
    { etrans; [apply go|]. by f_equiv. }
    rewrite /twp/twp' twp_unseal=> ????.
    apply least_fixpoint_ne; [|done]=> ?[[??]?]. rewrite /twp_pre'/twp_pre/=.
    do 11 f_equiv; [done|]. by do 14 f_equiv.
  Qed.
  Lemma twpw_proper {e s E W W' Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W] e @ s; E [{ Φ }] ⊣⊢ WP[W'] e @ s; E [{ Ψ }].
  Proof. rewrite !equiv_dist=> ???. by apply twpw_ne. Qed.

  (** Eliminate [fupdw] on [wpw] *)
  Lemma fupdw_wpw_nonval {e s E W Φ} : to_val e = None →
    (|=[W]{E}=> WP[W] e @ s; E {{ Φ }}) ⊢ WP[W] e @ s; E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre=>/= ->. iIntros "big" (?????) "[W st]".
    iMod ("big" with "W") as "[W big]". iApply "big". iFrame.
  Qed.
  Lemma fupdw_wpw_fupdw {e s E W Φ} :
    (|=[W]{E}=> WP[W] e @ s; E {{ Φ }}) ⊢
      WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }}.
  Proof.
    case eq: (to_val e)=>/=.
    - rewrite !wp_unfold /wp_pre eq. iIntros "Φ !>". by iMod "Φ" as ">$".
    - rewrite fupdw_wpw_nonval; [|done]. apply wp_mono. by iIntros.
  Qed.
  Lemma fupdw_wpw_fupdw' {e s E W Φ} :
    (|=[W]{E}=> WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }}) ⊢
      WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }}.
  Proof. rewrite fupdw_wpw_fupdw. apply wp_mono. iIntros (?) ">$". Qed.
  #[export] Instance elim_modal_fupdw_wpw_nonval {p e s E W P Φ} :
    ElimModal (to_val e = None) p false (|=[W]{E}=> P) P
      (WP[W] e @ s; E {{ Φ }}) (WP[W] e @ s; E {{ Φ }}).
  Proof.
    move=> ?. by rewrite /ElimModal bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r fupdw_wpw_nonval.
  Qed.
  #[export] Instance elim_modal_bupdw_wpw_nonval {p e s E W P Φ} :
    ElimModal (to_val e = None) p false (|=[W]=> P) P
      (WP[W] e @ s; E {{ Φ }}) (WP[W] e @ s; E {{ Φ }}).
  Proof. move=> ?. by rewrite (bupdw_fupdw E) elim_modal_fupdw_wpw_nonval. Qed.

  (** Eliminate [fupdw] on [twpw] *)
  Lemma fupdw_twpw_nonval {e s E W Φ} : to_val e = None →
    (|=[W]{E}=> WP[W] e @ s; E [{ Φ }]) ⊢ WP[W] e @ s; E [{ Φ }].
  Proof.
    rewrite twp_unfold /twp_pre=>/= ->. iIntros "big" (????) "[W st]".
    iMod ("big" with "W") as "[W big]". iApply "big". iFrame.
  Qed.
  Lemma fupdw_twpw_fupdw {e s E W Φ} :
    (|=[W]{E}=> WP[W] e @ s; E [{ Φ }]) ⊢
      WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }].
  Proof.
    case eq: (to_val e)=>/=.
    - rewrite !twp_unfold /twp_pre eq. iIntros "Φ !>". by iMod "Φ" as ">$".
    - rewrite fupdw_twpw_nonval; [|done]. apply twp_mono. by iIntros.
  Qed.
  Lemma fupdw_twpw_fupdw' {e s E W Φ} :
    (|=[W]{E}=> WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }]) ⊢
      WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }].
  Proof. rewrite fupdw_twpw_fupdw. apply twp_mono. iIntros (?) ">$". Qed.
  #[export] Instance elim_modal_fupdw_twpw_nonval {p e s E W P Φ} :
    ElimModal (to_val e = None) p false (|=[W]{E}=> P) P
      (WP[W] e @ s; E [{ Φ }]) (WP[W] e @ s; E [{ Φ }]).
  Proof.
    move=> ?. by rewrite /ElimModal bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r fupdw_twpw_nonval.
  Qed.
  #[export] Instance elim_modal_bupdw_twpw_nonval {p e s E W P Φ} :
    ElimModal (to_val e = None) p false (|=[W]=> P) P
      (WP[W] e @ s; E [{ Φ }]) (WP[W] e @ s; E [{ Φ }]).
  Proof. move=> ?. by rewrite (bupdw_fupdw E) elim_modal_fupdw_twpw_nonval. Qed.

  (** Mask-changing [fupdw] on atomic [wpw] *)
  Lemma wpw_atomic {e s E E' W Φ} `{!Atomic (stuckness_to_atomicity s) e} :
    to_val e = None →
    (|=[W]{E,E'}=> WP[W] e @ s; E' {{ v, |=[W]{E',E}=> Φ v }}) ⊢
      WP[W] e @ s; E {{ Φ }}.
  Proof.
    iIntros (nv) "wp". rewrite !wp_unfold /wp_pre nv /=.
    iIntros (?????) "[W st]". iMod ("wp" with "W") as "[W big]".
    iMod ("big" with "[$W $st]") as "[$ big]". iIntros "!>" (e2 ?? step) "£".
    iDestruct ("big" with "[//] £") as "big".
    iApply (step_fupdN_wand with "big"). iIntros "!> >[[W st] [wp $]]".
    destruct s.
    - rewrite !wp_unfold /wp_pre. case (to_val e2)=>/= >.
      { iFrame "st". by iMod ("wp" with "W") as ">[$$]". }
      iMod ("wp" $! _ _ [] with "[$W $st]") as "[%red big]".
      case red as (?&?&?&?&?). by edestruct (atomic _ _ _ _ _ step).
    - iFrame "st". destruct (atomic _ _ _ _ _ step) as [? <-%of_to_val].
      rewrite !wp_value_fupd'. by iMod ("wp" with "W") as ">[$$]".
  Qed.
  #[export] Instance elim_modal_fupdw_wpw_atomic {p e s E E' W P Φ}
    `{!Atomic (stuckness_to_atomicity s) e} :
    ElimModal (to_val e = None) p false (|=[W]{E,E'}=> P) P
      (WP[W] e @ s; E {{ Φ }}) (WP[W] e @ s; E' {{ v, |=[W]{E',E}=> Φ v }})%I
    | 100.
  Proof.
    move=> ?. by rewrite bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r wpw_atomic.
  Qed.

  (** Mask-changing [fupdw] on atomic [twpw] *)
  Lemma twpw_atomic {e E E' W Φ} `{!Atomic (stuckness_to_atomicity s) e} :
    to_val e = None →
    (|=[W]{E,E'}=> WP[W] e @ s; E' [{ v, |=[W]{E',E}=> Φ v }]) ⊢
      WP[W] e @ s; E [{ Φ }].
  Proof.
    iIntros (nv) "wp". rewrite !twp_unfold /twp_pre nv /=.
    iIntros (????) "[W st]". iMod ("wp" with "W") as "[W big]".
    iMod ("big" with "[$W $st]") as "[$ big]". iIntros "!>" (? e2 ?? step).
    iMod ("big" with "[//]") as "[$ [[W st] [wp $]]]". destruct s.
    - rewrite !twp_unfold /twp_pre. case (to_val e2)=>/= >.
      { iFrame "st". by iMod ("wp" with "W") as ">[$$]". }
      iMod ("wp" with "[$W $st]") as "[%red big]". case red as (?&?&?&?).
      by edestruct (atomic _ _ _ _ _ step).
    - iFrame "st". destruct (atomic _ _ _ _ _ step) as [? <-%of_to_val].
      rewrite !twp_value_fupd'. by iMod ("wp" with "W") as ">[$$]".
  Qed.
  #[export] Instance elim_modal_fupdw_twpw_atomic {p e s E E' W P Φ}
    `{!Atomic (stuckness_to_atomicity s) e} :
    ElimModal (to_val e = None) p false (|=[W]{E,E'}=> P) P
      (WP[W] e @ s; E [{ Φ }]) (WP[W] e @ s; E' [{ v, |=[W]{E',E}=> Φ v }])%I
    | 100.
  Proof.
    move=> ?. by rewrite bi.intuitionistically_if_elim fupdw_frame_r
      bi.wand_elim_r twpw_atomic.
  Qed.

  (** Eliminate [fupdw] in [wpw] *)
  Lemma wpw_fupdw_fupdw {e s E W Φ} :
    WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }} ⊢
      (|=[W]{E}=> WP[W] e @ s; E {{ Φ }}).
  Proof.
    iIntros "wp W". iLöb as "IH" forall (e E Φ).
    rewrite !wp_unfold /wp_pre/=. case (to_val e)=>/= >.
    { by iMod ("wp" with "W") as ">[$$]". }
    iFrame "W". iIntros "!>" (?????) "Wst".
    iMod ("wp" with "Wst") as "[$ big]". iIntros "!>" (?? efs ?) "£".
    iDestruct ("big" with "[%//] £") as "big".
    iApply (step_fupdN_wand with "big"). iIntros "!> >[[W $] [wp wps]]".
    iMod ("IH" with "wp W") as "[W $]". iInduction efs as [|??] "?"; by iFrame.
  Qed.
  Lemma wpw_fupdw_nonval {e s E W Φ} : to_val e = None →
    WP[W] e @ s; E {{ v, |=[W]{E}=> Φ v }} ⊢ WP[W] e @ s; E {{ Φ }}.
  Proof. move=> ?. by rewrite wpw_fupdw_fupdw fupdw_wpw_nonval. Qed.

  (** Eliminate [fupdw] in [twpw] *)
  Lemma twpw_fupdw_fupdw {e s E W Φ} :
    WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }] ⊢
      (|=[W]{E}=> WP[W] e @ s; E [{ Φ }]).
  Proof.
    enough (go : ∀ Ψ, WP[W] e @ s; E [{ Ψ }] -∗
      ∀ Φ, □ (∀ v, Ψ v =[W]{E}=∗ Φ v) =[W]{E}=∗ WP[W] e @ s; E [{ Φ }]).
    { iIntros "wp". iApply (go with "wp"). iIntros "!>" (?) "$". }
    iRevert (e E). iApply twp_ind; [solve_proper|]. iIntros "!>" (?? Ψ).
    iIntros "twp" (?) "#Ψto". rewrite twp_unfold /twp_pre. case (to_val e)=> >.
    { iIntros "W". by iMod ("Ψto" with "twp W") as ">[$$]". }
    iIntros "$ !>" (????) "Wst". iMod ("twp" with "[$Wst]") as "[$ big]".
    iIntros "!>" (?????).
    iMod ("big" with "[%//]") as "[$ [[W $] [[big _] bigs]]]".
    iMod ("big" with "[//] W") as "[$$]".
    by iDestruct (big_sepL_and with "bigs") as "[_ $]".
  Qed.
  Lemma twpw_fupdw_nonval {e s E W Φ} : to_val e = None →
    WP[W] e @ s; E [{ v, |=[W]{E}=> Φ v }] ⊢ WP[W] e @ s; E [{ Φ }].
  Proof. move=> ?. by rewrite twpw_fupdw_fupdw fupdw_twpw_nonval. Qed.

  (** Expand the world satisfaction of [wpw] *)
  Lemma wpw_expand_fupd {e s E F W W' Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W] e @ s; F {{ Φ }} -∗ WP[W'] e @ s; F {{ Φ }}.
  Proof.
    iIntros (EF) "#W'W wpW". iLöb as "IH" forall (F e Φ EF).
    rewrite !wp_unfold /wp_pre/=. case (to_val e); [done|].
    iIntros (?????) "[W' X]".
    iMod (fupd_mask_subseteq E) as "cl"; [done|].
    iMod ("W'W" with "W'") as "[W Wto]". iMod "cl" as "_".
    iMod ("wpW" with "[$W $X]") as "[% big]". iModIntro. iSplit; [done|].
    iIntros (????) "£". iDestruct ("big" with "[%//] £") as "big".
    iApply (step_fupdN_wand with "big"). iIntros "!> >[[W $] [wpW wpWs]]".
    iMod (fupd_mask_subseteq E) as "cl"; [done|].
    iMod ("Wto" with "W") as "$". iMod "cl" as "_". iModIntro.
    iSplitL "wpW"; [by iApply "IH"|]. iApply (big_sepL_impl with "wpWs").
    iIntros "!>" (???). by iApply "IH".
  Qed.
  Lemma wpw_expand {e s E W W' Φ} :
    □ (W' -∗ W ∗ (W -∗ W')) -∗
    WP[W] e @ s; E {{ Φ }} -∗ WP[W'] e @ s; E {{ Φ }}.
  Proof.
    iIntros "#W'W". iApply (wpw_expand_fupd (E:=E)); [done|]. iIntros "!> W'".
    iDestruct ("W'W" with "W'") as "[$ WW']". iIntros "!>?!>". by iApply "WW'".
  Qed.

  (** Expand the world satisfaction of [twpw] *)
  Lemma twpw_expand_fupd {e s E F W W' Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W] e @ s; F [{ Φ }] -∗ WP[W'] e @ s; F [{ Φ }].
  Proof.
    iIntros (EF) "#W'W twpW". iRevert (EF). iRevert (e F Φ) "twpW".
    iApply twp_ind; [solve_proper|]. iIntros "!>" (e F Φ) "twpW %".
    rewrite twp_unfold /twp_pre/=. case (to_val e); [done|].
    iIntros (????) "[W' X]". iMod (fupd_mask_subseteq E) as "cl"; [done|].
    iMod ("W'W" with "W'") as "[W Wto]". iMod "cl" as "_".
    iMod ("twpW" with "[$W $X]") as "[% big]". iModIntro. iSplit; [done|].
    iIntros (?????).
    iMod ("big" with "[%//]") as (?) "[[W $] [[twpW' _] twpW's]]".
    iDestruct ("twpW'" with "[%//]") as "$".
    iMod (fupd_mask_subseteq E) as "cl"; [done|]. iMod ("Wto" with "W") as "$".
    iMod "cl" as "_". iModIntro. iSplit; [done|].
    iApply (big_sepL_impl with "twpW's"). iIntros "!>" (???) "[to _]".
    by iApply "to".
  Qed.
  Lemma twpw_expand {e s E W W' Φ} :
    □ (W' -∗ W ∗ (W -∗ W')) -∗
    WP[W] e @ s; E [{ Φ }] -∗ WP[W'] e @ s; E [{ Φ }].
  Proof.
    iIntros "#W'W". iApply (twpw_expand_fupd (E:=E)); [done|]. iIntros "!> W'".
    iDestruct ("W'W" with "W'") as "[$ WW']". iIntros "!>?!>". by iApply "WW'".
  Qed.
End wpw.
