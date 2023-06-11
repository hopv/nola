(** * Weakest precondition *)

From nola.iris Require Export fupd.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.bi Require Import fixpoint.
From iris.proofmode Require Import proofmode.

(** ** What becomes [irisGS_gen] combined with an extra world satisfaction *)
Class irisGS'_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) := IrisG' {
  iris'_invGS :: invGS_gen hlc Σ;
  state_interp' : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  num_laters_per_step' : nat → nat;
  state_interp'_mono σ ns κs nt:
    state_interp' σ ns κs nt ⊢ |={∅}=> state_interp' σ (S ns) κs nt
}.

(** [irisGS_gen] made from [irisGS'_gen] and an extra world satisfaction *)
Program Definition IrisW `{!irisGS'_gen hlc Λ Σ}
  (W : iProp Σ) : irisGS_gen hlc Λ Σ := {|
  iris_invGS := iris'_invGS;
  state_interp σ ns ks nt := (W ∗ state_interp' σ ns ks nt)%I;
  fork_post v := True%I; (* TODO: Generalize this *)
  num_laters_per_step := num_laters_per_step';
|}.
Next Obligation. iIntros "* [$ ?]". by iApply state_interp'_mono. Qed.

Local Transparent iris_invGS.
Local Notation wp_unseal := weakestpre.wp_aux.(seal_eq).
Local Notation wp_def := weakestpre.wp_def.
Local Notation twp_unseal := total_weakestpre.twp_aux.(seal_eq).
Local Notation twp_pre' := total_weakestpre.twp_pre'.

(** ** [wpw]/[twpw]: [wp]/[twp] for [IrisW] *)
Notation wpw' W := (@wp _ _ _ _ (@wp' _ _ _ (IrisW W))) (only parsing).
Notation twpw' W := (@twp _ _ _ _ (@twp' _ _ _ (IrisW W))) (only parsing).
Notation wpw W s E e Φ :=
  (wpw' W%I%I%I%I s E%I%I%I%I e (λ v, |=[W]{E}=> Φ v)%I) (only parsing).
Notation twpw W s E e Φ :=
  (twpw' W%I%I%I%I s E%I%I%I%I e (λ v, |=[W]{E}=> Φ v)%I) (only parsing).

(** ** Rich notation for [wpw]/[twpw] *)

Notation "WP[ W ]' e @ s ; E {{ Φ } }" := (wpw' W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e @ s ; E [{ Φ } ]" := (twpw' W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ s ; E {{ Φ } }" := (wpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ s ; E [{ Φ } ]" := (twpw W s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e @ E {{ Φ } }" := (wpw' W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e @ E [{ Φ } ]" := (twpw' W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E {{ Φ } }" := (wpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E [{ Φ } ]" := (twpw W NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e @ E ? {{ Φ } }" := (wpw' W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e @ E ? [{ Φ } ]" := (twpw' W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? {{ Φ } }" := (wpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e @ E ? [{ Φ } ]" := (twpw W MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e {{ Φ } }" := (wpw' W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e [{ Φ } ]" := (twpw' W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e {{ Φ } }" := (wpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e [{ Φ } ]" := (twpw W NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e ? {{ Φ } }" := (wpw' W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ]' e ? [{ Φ } ]" := (twpw' W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? {{ Φ } }" := (wpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "WP[ W ] e ? [{ Φ } ]" := (twpw W MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "WP[ W ]' e @ s ; E {{ v , Q } }" := (wpw' W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ]' e @ s ; E [{ v , Q } ]" := (twpw' W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ s ; E {{ v , Q } }" := (wpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ s ; E [{ v , Q } ]" := (twpw W s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ]' e @ E {{ v , Q } }" := (wpw' W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ]' e @ E [{ v , Q } ]" := (twpw' W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E {{ v , Q } }" := (wpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E [{ v , Q } ]" := (twpw W NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ]' e @ E ? {{ v , Q } }" := (wpw' W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  E  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ]' e @ E ? [{ v , Q } ]" := (twpw' W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' @  E  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? {{ v , Q } }" := (wpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e @ E ? [{ v , Q } ]" := (twpw W MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' @  E  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ]' e {{ v , Q } }" := (wpw' W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "WP[ W ]' e [{ v , Q } ]" := (twpw' W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "WP[ W ] e {{ v , Q } }" := (wpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "WP[ W ] e [{ v , Q } ]" := (twpw W NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
Notation "WP[ W ]' e ? {{ v , Q } }" := (wpw' W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ]' e ? [{ v , Q } ]" := (twpw' W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]'  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.
Notation "WP[ W ] e ? {{ v , Q } }" := (wpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'")
  : bi_scope.
Notation "WP[ W ] e ? [{ v , Q } ]" := (twpw W MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' WP[ W ]  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'")
  : bi_scope.

Notation "{{{ P } } } [ W ]' e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ s; E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ s; E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  E  '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  E  '/' ? {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  E  '/' ? [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e {{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e [{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' [[{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e ?{{ Φ }})%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' ? {{{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e ?[{ Φ }])%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' ? [[{  '[' x  ..  y ,   RET  pat ;  '/' Q  ']' } ] ] ']'")
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

Notation "{{{ P } } } [ W ]' e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ s; E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ s; E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  E  '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' @  E  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' @  E  '/' ? [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e [{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
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
Notation "{{{ P } } } [ W ]' e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e ?{{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } } [ W ]'  '/  ' e  '/' ? {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'")
  : bi_scope.
Notation "[[{ P } ] ] [ W ]' e ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e ?[{ Φ }])%I
  (at level 20,
   format "'[hv' [[{  '[' P  ']' } ] ] [ W ]'  '/  ' e  '/' ? [[{  '[' RET  pat ;  '/' Q  ']' } ] ] ']'")
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

Notation "{{{ P } } } [ W ]' e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ s; E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ s; E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ s; E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ]' e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ]' e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e @ E ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e @ E ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ]' e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e {{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e [{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ]' e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W]' e ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?{{ Φ }})
  : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP[W] e ?[{ Φ }])
  : stdpp_scope.
Notation "{{{ P } } } [ W ]' e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ s; E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ s; E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ s; E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ]' e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ]' e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e @ E ?[{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e @ E ?[{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ]' e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e {{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e [{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ]' e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W]' e ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ]' e ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W]' e ?[{ Φ }]) : stdpp_scope.
Notation "{{{ P } } } [ W ] e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP[W] e ?{{ Φ }}) : stdpp_scope.
Notation "[[{ P } ] ] [ W ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WP[W] e ?[{ Φ }]) : stdpp_scope.

(** ** Lemmas for [wpw]/[twpw] *)
Section wpw.
  Context `{!irisGS'_gen hlc Λ Σ}.

  (** [wpw] is non-expansive over the world satisfaction *)
  Lemma wpw'_ne {W W' n e s E Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W]' e @ s; E {{ Φ }})%I ≡{n}≡ (WP[W']' e @ s; E {{ Ψ }})%I.
  Proof.
    move=> ??.
    enough (go : (wpw' W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ wpw' W').
    { etrans; [apply go|]. by do 2 f_equiv. }
    rewrite /wp/wp' wp_unseal=> ?. apply fixpoint_ne=> ????.
    rewrite /wp_pre/=. do 13 f_equiv; [done|]. do 12 f_equiv.
    apply step_fupdN_ne. by do 3 f_equiv.
  Qed.
  Lemma wpw_ne {W W' n e s E Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W] e @ s; E {{ Φ }})%I ≡{n}≡ (WP[W'] e @ s; E {{ Ψ }})%I.
  Proof.
    move=> ??. apply wpw'_ne; [done|]=> ?. by apply fupdpw_ne.
  Qed.
  Lemma wpw'_proper {W W' e s E Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W]' e @ s; E {{ Φ }} ⊣⊢ WP[W']' e @ s; E {{ Ψ }}.
  Proof. rewrite !equiv_dist=> ???. by apply wpw'_ne. Qed.
  Lemma wpw_proper {W W' e s E Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W] e @ s; E {{ Φ }} ⊣⊢ WP[W'] e @ s; E {{ Ψ }}.
  Proof. rewrite !equiv_dist=> ???. by apply wpw_ne. Qed.

  (** [twpw] is non-expansive over the world satisfaction *)
  Lemma twpw'_ne {W W' n e s E Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W]' e @ s; E [{ Φ }])%I ≡{n}≡ (WP[W']' e @ s; E [{ Ψ }])%I.
  Proof.
    move=> ??.
    enough (go : (twpw' W : _ -d> _ -d> _ -d> _ -d> _) ≡{n}≡ twpw' W').
    { etrans; [apply go|]. do 3 f_equiv. }
    rewrite /twp/twp' twp_unseal=> ????.
    apply least_fixpoint_ne; [|done]=> ?[[??]?]. rewrite /twp_pre'/twp_pre/=.
    do 11 f_equiv; [done|]. by do 14 f_equiv.
  Qed.
  Lemma twpw_ne {W W' n e s E Φ Ψ} :
    W ≡{n}≡ W' → (Φ : _ -d> _) ≡{n}≡ Ψ →
    (WP[W] e @ s; E [{ Φ }])%I ≡{n}≡ (WP[W'] e @ s; E [{ Ψ }])%I.
  Proof.
    move=> ??. apply twpw'_ne; [done|]=> ?. by apply fupdpw_ne.
  Qed.
  Lemma twpw'_proper {W W' e s E Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W]' e @ s; E [{ Φ }] ⊣⊢ WP[W']' e @ s; E [{ Ψ }].
  Proof. rewrite !equiv_dist=> ???. by apply twpw'_ne. Qed.
  Lemma twpw_proper {W W' e s E Φ Ψ} :
    W ⊣⊢ W' → (Φ : _ -d> _) ≡ Ψ →
    WP[W] e @ s; E [{ Φ }] ⊣⊢ WP[W'] e @ s; E [{ Ψ }].
  Proof. rewrite !equiv_dist=> ???. by apply twpw_ne. Qed.

  (** [wpw]/[twpw] absorbs the fancy update under the world satisfaction *)
  Lemma wpw_fupdw {W e s E Φ} :
    (WP[W] e @ s; E {{ v, |=[W]{E,E}=> Φ v }}) -∗ WP[W] e @ s; E {{ Φ }}.
  Proof.
    iIntros "wp". iApply (wp_wand with "wp"). iIntros (?) "toΦ W".
    iMod ("toΦ" with "W") as "[W toΦ]". by iMod ("toΦ" with "W").
  Qed.
  Lemma twpw_fupdw {W e s E Φ} :
    (WP[W] e @ s; E [{ v, |=[W]{E,E}=> Φ v }]) -∗ WP[W] e @ s; E [{ Φ }].
  Proof.
    iIntros "twp". iApply (twp_wand with "twp"). iIntros (?) "toΦ W".
    iMod ("toΦ" with "W") as "[W toΦ]". by iMod ("toΦ" with "W").
  Qed.
  Lemma fupdw_wpw {W e s E Φ} :
    (|=[W]{E}=> WP[W] e @ s; E {{ Φ }}) -∗ WP[W] e @ s; E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. case (to_val e)=>/=.
    { iIntros (?) "toΦ !> W". iMod ("toΦ" with "W") as "[W toΦ]".
      by iMod ("toΦ" with "W"). }
    iIntros "big" (?????) "[W st]". iMod ("big" with "W") as "[W big]".
    iApply "big". iFrame.
  Qed.
  Lemma fupdw_twpw {W e s E Φ} :
    (|=[W]{E}=> WP[W] e @ s; E [{ Φ }]) -∗ WP[W] e @ s; E [{ Φ }].
  Proof.
    rewrite twp_unfold /twp_pre. case (to_val e)=>/=.
    { iIntros (?) "toΦ !> W". iMod ("toΦ" with "W") as "[W toΦ]".
      by iMod ("toΦ" with "W"). }
    iIntros "big" (????) "[W st]". iMod ("big" with "W") as "[W big]".
    iApply "big". iFrame.
  Qed.

  (** Turn [wpw] into [wpw'] under the world satisfaction *)
  Lemma wpw_wpw' {W e s E Φ} :
    WP[W] e @ s; E {{ Φ }} =[W]{E}=∗ WP[W]' e @ s; E {{ Φ }}.
  Proof.
    iIntros "wp W". iLöb as "IH" forall (e E Φ).
    rewrite !wp_unfold /wp_pre/=. case (to_val e)=>/= >.
    { by iMod ("wp" with "W") as ">[$$]". }
    iFrame "W". iIntros "!>" (?????) "Wst".
    iMod ("wp" with "Wst") as "[$ big]". iIntros "!>" (?? efs ?) "£".
    iMod ("big" with "[%//] £") as "big". iModIntro. iNext.
    iApply (step_fupdN_wand with "big"). iIntros ">[[W $] [wp wps]]".
    iMod ("IH" with "wp W") as "[W $]". iInduction efs as [|??] "?"; by iFrame.
  Qed.

  (** Turn [twpw] into [twpw'] under the world satisfaction *)
  Lemma twpw_twpw' {W e s E Φ} :
    WP[W] e @ s; E [{ Φ }] =[W]{E}=∗ WP[W]' e @ s; E [{ Φ }].
  Proof.
    enough (go : ∀ Ψ, WP[W]' e @ s; E [{ Ψ }] -∗
      ∀ Φ, □ (∀ v, Ψ v =[W]{E}=∗ Φ v) =[W]{E}=∗ WP[W]' e @ s; E [{ Φ }]).
    { iIntros "wp". iApply (go with "wp"). iIntros "!>" (?) "$". }
    iRevert (e E). iApply twp_ind; [solve_proper|]. iIntros "!>" (?? Ψ).
    iIntros "twp" (?) "#Ψto". rewrite twp_unfold /twp_pre. case (to_val e)=> >.
    { iIntros "W". by iMod ("Ψto" with "twp W") as ">[$$]". }
    iIntros "$ !>" (????) "Wst". iMod ("twp" with "[$Wst]") as "[$ big]".
    iIntros "!>" (??? efs ?).
    iMod ("big" with "[%//]") as "[$ [[W $] [[big _] bigs]]]".
    iMod ("big" with "[//] W") as "[W $]". clear.
    iInduction efs as [|??] "IH"; [by iFrame|].
    iDestruct "bigs" as "[[_ $] bigs]". iApply ("IH" with "bigs W").
  Qed.

  (** Expand the world satisfaction of [wpw] *)
  Lemma wpw'_expand_fupd {W W' e s E F Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W]' e @ s; F {{ Φ }} -∗ WP[W']' e @ s; F {{ Φ }}.
  Proof.
    iIntros (EF) "#W'W wpW". iLöb as "IH" forall (e F Φ EF).
    rewrite !wp_unfold /wp_pre/=. case (to_val e); [done|].
    iIntros (?????) "[W' X]". iMod (fupd_mask_subseteq E) as "Cl"; [done|].
    iMod ("W'W" with "W'") as "[W Wto]". iMod "Cl" as "_".
    iMod ("wpW" with "[$W $X]") as "[$ big]". iIntros "!>" (????) "£".
    iMod ("big" with "[%//] £") as "big". iModIntro. iNext.
    iApply (step_fupdN_wand with "big"). iIntros ">[[W $] [wpW wpWs]]".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|].
    iMod ("Wto" with "W") as "$". iMod "Cl" as "_". iModIntro.
    iSplitL "wpW"; [by iApply "IH"|]. iApply (big_sepL_impl with "wpWs").
    iIntros "!#" (? e' ?) "wpW". by iApply "IH".
  Qed.
  Lemma wpw_expand_fupd {W W' e s E F Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W] e @ s; F {{ Φ }} -∗ WP[W'] e @ s; F {{ Φ }}.
  Proof.
    iIntros (EF) "#W'W wpW".
    iDestruct (wpw'_expand_fupd with "[] wpW") as "wpW'"; [done..|].
    iApply (wp_wand with "wpW'"). iIntros (?) "toΨ W'".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|].
    iMod ("W'W" with "W'") as "[W WW']". iMod "Cl" as "_".
    iMod ("toΨ" with "W") as "[W $]".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|]. iMod ("WW'" with "W").
    by iMod "Cl" as "_".
  Qed.
  Lemma wpw_expand {W W' e s E Φ} :
    □ (W' -∗ W ∗ (W -∗ W')) -∗
    WP[W] e @ s; E {{ Φ }} -∗ WP[W'] e @ s; E {{ Φ }}.
  Proof.
    iIntros "#W'W". iApply (wpw_expand_fupd (E:=E)); [done|]. iIntros "!> W'".
    iDestruct ("W'W" with "W'") as "[$ WW']". iIntros "!>?!>". by iApply "WW'".
  Qed.

  (** Expand the world satisfaction of [twpw] *)
  Lemma twpw'_expand_fupd {W W' e s E F Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W]' e @ s; F [{ Φ }] -∗ WP[W']' e @ s; F [{ Φ }].
  Proof.
    iIntros (EF) "#W'W twpW". iRevert (EF). iRevert (e F Φ) "twpW".
    iApply twp_ind; [solve_proper|]. iIntros "!#" (e F Φ) "twpW %".
    rewrite twp_unfold /twp_pre/=. case (to_val e); [done|].
    iIntros (????) "[W' X]". iMod (fupd_mask_subseteq E) as "Cl"; [done|].
    iMod ("W'W" with "W'") as "[W Wto]". iMod "Cl" as "_".
    iMod ("twpW" with "[$W $X]") as "[$ big]". iIntros "!>" (?????).
    iMod ("big" with "[%//]") as (?) "[[W $] [[twpW' _] twpW's]]".
    iDestruct ("twpW'" with "[%//]") as "$".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|]. iMod ("Wto" with "W") as "$".
    iMod "Cl" as "_". iModIntro. iSplit; [done|].
    iApply (big_sepL_impl with "twpW's"). iIntros "!#" (???) "[to _]".
    by iApply "to".
  Qed.
  Lemma twpw_expand_fupd {W W' e s E F Φ} :
    E ⊆ F → □ (W' ={E}=∗ W ∗ (W ={E}=∗ W')) -∗
    WP[W] e @ s; F [{ Φ }] -∗ WP[W'] e @ s; F [{ Φ }].
  Proof.
    iIntros (EF) "#W'W twpW".
    iDestruct (twpw'_expand_fupd with "[] twpW") as "twpW'"; [done..|].
    iApply (twp_wand with "twpW'"). iIntros (?) "toΨ W'".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|].
    iMod ("W'W" with "W'") as "[W WW']". iMod "Cl" as "_".
    iMod ("toΨ" with "W") as "[W $]".
    iMod (fupd_mask_subseteq E) as "Cl"; [done|]. iMod ("WW'" with "W").
    by iMod "Cl" as "_".
  Qed.
  Lemma twpw_expand {W W' e s E Φ} :
    □ (W' -∗ W ∗ (W -∗ W')) -∗
    WP[W] e @ s; E [{ Φ }] -∗ WP[W'] e @ s; E [{ Φ }].
  Proof.
    iIntros "#W'W". iApply (twpw_expand_fupd (E:=E)); [done|]. iIntros "!> W'".
    iDestruct ("W'W" with "W'") as "[$ WW']". iIntros "!>?!>". by iApply "WW'".
  Qed.

  (** Turn [twpw] into [wpw] *)
  Lemma twpw_wpw_step {W e s E P Φ} : TCEq (to_val e) None →
    ▷ P -∗ WP[W] e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP[W] e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "P twp". iApply (twp_wp_step with "P").
    iApply (twp_wand with "twp"). iIntros (?) "toΦ P !> W".
    iMod ("toΦ" with "W") as "[$ toΦ]". by iApply "toΦ".
  Qed.

  (** Bind over [wpw]/[twpw] *)
  Lemma wpw_bind `{!LanguageCtx K} {W e s E Φ} :
    WP[W] e @ s; E {{ v, WP[W] K (of_val v) @ s; E {{ Φ }} }} -∗
    WP[W] K e @ s; E {{ Φ }}.
  Proof.
    iIntros "wpe". iApply wp_bind. iApply (wp_wand with "wpe").
    iIntros (?). iApply fupdw_wpw.
  Qed.
  Lemma twpw_bind `{!LanguageCtx K} {W e s E Φ} :
    WP[W] e @ s; E [{ v, WP[W] K (of_val v) @ s; E [{ Φ }] }] -∗
    WP[W] K e @ s; E [{ Φ }].
  Proof.
    iIntros "twpe". iApply twp_bind. iApply (twp_wand with "twpe").
    iIntros (?). iApply fupdw_twpw.
  Qed.
End wpw.
