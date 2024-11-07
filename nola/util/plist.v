(** * Product list *)

From nola Require Export prod.
From stdpp Require Import vector.
Import ProdNotation.

(** Product list *)
Section plist.
  Context {A} (F : A → Type).
  Fixpoint plist (al : list A) : Type :=
    match al with [] => unit | a :: al => F a *' plist al end.
End plist.

(** Cons and nil for [plist] *)
Definition pcons {A F a al} : F a → @plist A F al → plist F (a :: al) :=
  pair'.
Definition pnil {A F} : @plist A F [] := ().
Module PlistNotation.
  Infix "ᵖ::" := pcons (at level 60, right associativity).
  Infix "ᵖ::@{ F }" := (pcons (F:=F))
    (at level 60, right associativity, only parsing).
  Notation "ᵖ[ ]" := pnil (at level 1, format "ᵖ[ ]").
  Notation "ᵖ[ ]@{ F }" := (pnil (F:=F)) (at level 1, only parsing).
  Notation "ᵖ[ x ; .. ; z ]" := (x ᵖ:: .. (z ᵖ:: ᵖ[]) ..)
    (at level 1, format "ᵖ[ x ;  .. ;  z ]").
  Notation "ᵖ[ x ; .. ; z ]@{ F }" := (x ᵖ::@{F} .. (z ᵖ::@{F} ᵖ[]@{F}) ..)
    (at level 1, only parsing).
End PlistNotation.
Import PlistNotation.

(** [plist] as [list] *)
Section of_plist.
  Context {A} {F : A → Type} {B} (f : ∀ a, F a → B).
  Fixpoint of_plist {al} : plist F al → list B :=
    match al with [] => λ _, [] | _ :: _ =>
      λ '(x, xl)', f _ x :: of_plist xl end.
End of_plist.

(** [fmap] over [of_plist] *)
Lemma of_plist_fmap {A} {F : A → Type} {B C} (f : ∀ a, F a → B) (g : B → C)
  {al} {xl : plist F al} :
  g <$> (of_plist f xl) = of_plist (λ a x, g (f a x)) xl.
Proof. elim: al xl; [done|]=>/= ???[??]. by f_equiv. Qed.

(** Map [plist] *)
Section plist_map.
  Context {A} {F G : A → Type} (f : ∀ a, F a → G a).
  Fixpoint plist_map {al : list A} : plist F al → plist G al :=
    match al with [] => λ _, ᵖ[] | _ :: _ =>
      λ '(x, xl)', f _ x ᵖ:: plist_map xl end.
End plist_map.

(** Zip [plist]s *)
Section plist_zip.
  Context {A} {F G : A → Type}.
  Fixpoint plist_zip {al : list A}
    : plist F al → plist G al → plist (λ a, F a *' G a) al :=
    match al with [] => λ _ _, ᵖ[] | _ :: _ =>
      λ '(x, xl)' '(y, yl)', (x, y)' ᵖ:: plist_zip xl yl end.
End plist_zip.

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
Section plist_repeat.
  Context {A} {F : A → Type} {a : A}.
  Fixpoint of_plist_repeat {n}
    : plist F (repeat a n) → vec (F a) n :=
    match n with 0 => λ _, [#] | S _ =>
      λ '(x, xl)', x ::: of_plist_repeat xl end.
  Fixpoint to_plist_repeat {n} (xl : vec (F a) n) : plist F (repeat a n) :=
    match xl with [#] => ᵖ[] | b ::: xl => b ᵖ:: to_plist_repeat xl end.
End plist_repeat.

(** [of_plist_repeat] and [to_plist_repeat] are mutually inverse *)
Lemma to_of_plist_repeat {A F} {a : A} {n} {xl : plist F (repeat a n)} :
  to_plist_repeat (of_plist_repeat xl) = xl.
Proof. elim: n xl; [by case|]=>/= ? IH [??]. by rewrite IH. Qed.
Lemma of_to_plist_repeat {A F} {a : A} {n} {xl : vec (F a) n} :
  of_plist_repeat (to_plist_repeat xl) = xl.
Proof. by elim: xl=>/=; [done|]=> ???->. Qed.

(** [plist] over [++] *)
Section plist_app_sep.
  Context {A} {F : A → Type}.
  Fixpoint plist_app {al bl}
    : plist F al → plist F bl → plist F (al ++ bl) :=
    match al with [] => λ _, id | _ :: _ =>
      λ '(x, xl)' yl, (x, plist_app xl yl)' end.
  Fixpoint plist_sep {al bl}
    : plist F (al ++ bl) → plist F al *' plist F bl :=
    match al with [] => λ xl, (ᵖ[], xl)' | _ :: _ =>
      λ '(x, xl)', let '(yl, zl)' := plist_sep xl in (x ᵖ:: yl, zl)' end.
End plist_app_sep.

(** [plist_app] and [plist_sep] are mutually inverse *)
Lemma plist_app_sep {A} {F : A → Type} {al bl}
  {xl : plist F al} {yl : plist F bl} :
  plist_sep (plist_app xl yl) = (xl, yl)'.
Proof. elim: al xl yl; [by case|]=>/= ?? IH [??]?. by rewrite IH. Qed.
Lemma plist_sep_app {A} {F : A → Type} {al bl}
  {xl : plist F (al ++ bl)} :
  plist_app (plist_sep xl).1' (plist_sep xl).2' = xl.
Proof. elim: al xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

(** Map and fold over [plist] *)
Section plist_foldmap.
  Context {R} (e : R) (op : R → R → R) {A} {F : A → Type} (f : ∀ a, F a → R).
  Fixpoint plist_foldmap {al : list A} : plist F al → R :=
    match al with [] => λ _, e | _ :: _ =>
      λ '(x, xl)', op (f _ x) (plist_foldmap xl) end.
End plist_foldmap.

(** Split a function to [plist] into a [plist] of functions *)
Section plist_funsplit.
  Context {B A : Type} {F : A → Type}.
  Fixpoint plist_funsplit {al}
    : (B → plist F al) → plist (λ a, B → F a) al :=
    match al with [] => λ _, ᵖ[] |
      a :: al => λ f, (fst' ∘ f) ᵖ:: plist_funsplit (snd' ∘ f) end.
End plist_funsplit.

(** [plist_funsplit] and [plist_map] over application are mutually inverse *)
Lemma plist_map_app_funsplit {B A F al f b} :
  plist_map (λ _, (.$ b)) (@plist_funsplit B A F al f) = f b.
Proof.
  move: f. elim: al=>/=. { move=> f. by case (f b). }
  move=> ?? IH ?. by rewrite IH.
Qed.
Lemma plist_funsplit_map_app {B A F al gl} :
  @plist_funsplit B A F al (λ b, plist_map (λ _, (.$ b)) gl) = gl.
Proof. move: gl. elim: al=>/=; [by case|]=> ?? IH [??]. by rewrite IH. Qed.

(** Universal quantification over [plist] *)
Definition plist_forall {A F} (Φ : ∀ a, F a → Prop) {al} : plist F al → Prop :=
  plist_foldmap True (∧) (A:=A) Φ (al:=al).

(** [plist_forall] is monotone *)
#[export] Instance plist_forall_mono {A F} :
  Proper (forall_relation (λ _, pointwise_relation _ impl) ==>
    forall_relation (λ _, pointwise_relation _ impl)) (@plist_forall A F).
Proof.
  move=> ?? impl. elim=>//= ?? IH ?[??]. split; by [apply impl|apply IH].
Qed.

(** Type class universal quantification over [plist] *)
Definition TCPlistForall {A F} (Φ : ∀ a, F a → Prop) {al} : plist F al → Prop :=
  plist_foldmap TCTrue TCAnd (A:=A) Φ (al:=al).

(** [TCPlistForall] is monotone *)
#[export] Instance TCPlistForall_mono {A F} :
  Proper (forall_relation (λ _, pointwise_relation _ impl) ==>
    forall_relation (λ _, pointwise_relation _ impl)) (@TCPlistForall A F).
Proof.
  move=> ?? impl. elim=>//= ?? IH ?[??]. split; by [apply impl|apply IH].
Qed.
