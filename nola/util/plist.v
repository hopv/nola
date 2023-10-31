(** * Product list *)

From nola Require Export prod.
From stdpp Require Import vector.

(** Product list *)
Fixpoint plist {A} (F : A → Type) (al : list A) : Type :=
  match al with [] => unit | a :: al => F a *' plist F al end.

(** [plist] as [list] *)
Fixpoint of_plist {A} {F : A → Type} {B} (f : ∀ a, F a → B) {al}
  : plist F al → list B :=
  match al with [] => λ _, [] | _ :: _ =>
    λ '(x, xl)', f _ x :: of_plist f xl end.

(** [fmap] over [of_plist] *)
Lemma of_plist_fmap {A} {F : A → Type} {B C} (f : ∀ a, F a → B) (g : B → C)
  {al} {xl : plist F al} :
  g <$> (of_plist f xl) = of_plist (λ a x, g (f a x)) xl.
Proof. elim: al xl; [done|]=>/= ???[??]. by f_equiv. Qed.

(** Map [plist] *)
Fixpoint plist_map {A} {F G : A → Type} (f : ∀ a, F a → G a) {al : list A}
  : plist F al → plist G al :=
  match al with [] => λ _, () | _ :: _ =>
    λ '(x, xl)', (f _ x, plist_map f xl)' end.

(** Zip [plist]s *)
Fixpoint plist_zip {A} {F G : A → Type} {al : list A}
  : plist F al → plist G al → plist (λ a, F a *' G a) al :=
  match al with [] => λ _ _, () | _ :: _ =>
    λ '(x, xl)' '(y, yl)', ((x, y)', plist_zip xl yl)' end.

(** [fst']/[snd'] over [plist_zip] *)
Lemma plist_zip_fst {A} {F G : A → Type} {al}
  {xl : plist F al} {yl : plist G al} :
  plist_map (λ _, fst') (plist_zip xl yl) = xl.
Proof. elim: al xl yl; [by case|]=>/= ?? IH [??][??]. by rewrite IH. Qed.
Lemma plist_zip_snd {A} {F G : A → Type} {al}
  {xl : plist F al} {yl : plist G al} :
  plist_map (λ _, snd') (plist_zip xl yl) = yl.
Proof. elim: al xl yl; [case; by case|]=>/= ?? IH [??][??]. by rewrite IH. Qed.

(** [plist] over [repeat] as [vec] *)
Fixpoint of_plist_repeat {A} {F : A → Type} {a : A} {n}
  : plist F (repeat a n) → vec (F a) n :=
  match n with 0 => λ _, [#] | S _ =>
    λ '(x, xl)', x ::: of_plist_repeat xl end.
Fixpoint to_plist_repeat {A} {F : A → Type} {a : A} {n} (xl : vec (F a) n)
  : plist F (repeat a n) :=
  match xl with [#] => () | b ::: xl => (b, to_plist_repeat xl)' end.

(** [of_plist_repeat] and [to_plist_repeat] are mutually inverse *)
Lemma to_of_plist_repeat {A F} {a : A} {n} {xl : plist F (repeat a n)} :
  to_plist_repeat (of_plist_repeat xl) = xl.
Proof. elim: n xl; [by case|]=>/= ? IH [??]. by rewrite IH. Qed.
Lemma of_to_plist_repeat {A F} {a : A} {n} {xl : vec (F a) n} :
  of_plist_repeat (to_plist_repeat xl) = xl.
Proof. by elim: xl=>/=; [done|]=> ???->. Qed.

(** [plist] over [++] *)
Fixpoint plist_app {A} {F : A → Type} {al bl}
  : plist F al → plist F bl → plist F (al ++ bl) :=
  match al with [] => λ _, id | _ :: _ =>
    λ '(x, xl)' yl, (x, plist_app xl yl)' end.
Fixpoint plist_sep {A} {F : A → Type} {al bl}
  : plist F (al ++ bl) → plist F al *' plist F bl :=
  match al with [] => λ xl, ((), xl)' | _ :: _ =>
    λ '(x, xl)', let '(yl, zl)' := plist_sep xl in ((x, yl)', zl)' end.

(** [plist_app] and [plist_sep] are mutually inverse *)
Lemma plist_app_sep {A} {F : A → Type} {al bl}
  {xl : plist F al} {yl : plist F bl} :
  plist_sep (plist_app xl yl) = (xl, yl)'.
Proof. elim: al xl yl; [by case|]=>/= ?? IH [??]?. by rewrite IH. Qed.
Lemma plist_sep_app {A} {F : A → Type} {al bl}
  {xl : plist F (al ++ bl)} :
  plist_app (plist_sep xl).1' (plist_sep xl).2' = xl.
Proof. elim: al xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.
