(** * Utility for [list] *)

From nola Require Export prelude.

(** ** Lemmas for [list], defined directly for computation *)

(** Reduce [++ []] *)
Fixpoint app_nil_d {A} {xs : list A} : xs ++ [] = xs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_nil_d
  end.
Definition app_nil'_d {A} {xs : list A} : xs = xs ++ [] := eq_sym app_nil_d.
Definition app_eq_nil_d {A} {xs ys : list A} (eq : ys = []) : xs ++ ys = xs :=
  eq_trans (f_equal (_ ++.) eq) app_nil_d.

(** Associativity of [++] *)
Fixpoint app_assoc_d {A} {xs ys zs : list A}
  : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
  match xs with
  | [] => eq_refl
  | _ :: _ => f_equal _ app_assoc_d
  end.

(** ** [schoice]: Variant choosing an element of [list] with a value *)

Inductive schoice {A} {F : A → Type} : list A → Type :=
| sbyhd {x} : F x → ∀ xs, schoice (x :: xs)
| sbytl {xs} : ∀ x, schoice xs → schoice (x :: xs).
Arguments schoice {A} F xs.

(** Utility patterns for [schoice] *)
Notation "!0 v" := (sbyhd v _) (at level 20, right associativity) : nola_scope.
Notation "+! s" := (sbytl _ s) (at level 20, right associativity) : nola_scope.
Notation "!1 v" := (+! !0 v) (at level 20, right associativity) : nola_scope.
Notation "!2 v" := (+! !1 v) (at level 20, right associativity) : nola_scope.
Notation "!3 v" := (+! !2 v) (at level 20, right associativity) : nola_scope.
Notation "!4 v" := (+! !3 v) (at level 20, right associativity) : nola_scope.
Notation "!5 v" := (+! !4 v) (at level 20, right associativity) : nola_scope.
Notation "!6 v" := (+! !5 v) (at level 20, right associativity) : nola_scope.
Notation "!7 v" := (+! !6 v) (at level 20, right associativity) : nola_scope.
Notation "!8 v" := (+! !7 v) (at level 20, right associativity) : nola_scope.
Notation "!9 v" := (+! !8 v) (at level 20, right associativity) : nola_scope.

(** Turn the type function of [schoice] *)
Fixpoint strans {A F G} (f : ∀ x, F x → G x)
  {xs : list A} (s : schoice F xs) : schoice G xs :=
  match s with !0 v => !0 f _ v | +! s => +! strans f s end.

(** Congruence of [strans] *)
Lemma strans_cong {A F G} {f g : ∀ x, F x → G x} {xs : list A} {s : _ xs} :
  (∀ x a, f x a = g x a) → strans f s = strans g s.
Proof. move=> eq. elim s=>/= >; [f_equal; apply eq|move=> <-//]. Qed.

(** [strans] composes *)
Lemma strans_strans {A F G H f g} {xs : list A} {s : _ xs} :
  strans (G:=H) g (strans (F:=F) (G:=G) f s) = strans (λ x, g x ∘ f x) s.
Proof. by elim s; [done|]=>/= ???->. Qed.

(** Destruct [schoice F xs] with [xs = []] *)
Definition seqnil {A F R} {xs : list A} (s : schoice F xs) : xs = [] → R :=
  match s with
  | !0 _ => λ eq, match eq with end
  | +! _ => λ eq, match eq with end
  end.

(** Turn [schoice F xs] into [schoice F (xs ++ ys)] *)
Fixpoint sbylapp {A F} {xs : list A} (s : schoice F xs) ys
  : schoice F (xs ++ ys) :=
  match s with
  | !0 v => !0 v
  | +! s => +! sbylapp s ys
  end.

(** Turn [schoice F ys] into [schoice F (xs ++ ys)] *)
Fixpoint sbyrapp {A F} xs {ys : list A} (s : schoice F ys)
  : schoice F (xs ++ ys) :=
  match xs with
  | [] => s
  | _ :: xs => +! sbyrapp xs s
  end.

(** Type function for [option] *)
Definition tf_option {A} (F : A → Type) (o : option A) : Type :=
  from_option F Empty_set o.
Definition tf_option_map {A F G} (f : ∀ x, F x → G x)
  {o : option A} : tf_option F o → tf_option G o
  := match o with Some _ => f _ | None => id end.

(** Decompose [schoice F (x :: xs)] *)
Definition suncons' {A F} {xs : list A} (s : schoice F xs) :
  tf_option F (head xs) + schoice F (tail xs) :=
  match s with !0 v => inl v | +! s => inr s end.
Definition suncons {A F x} {xs : list A} (s : schoice F (x :: xs)) :
  F x + schoice F xs := suncons' s.

(** [suncons] commutes with [strans] *)
Lemma suncons'_strans {A F G xs} {f : ∀ x : A, F x → G x} {s : _ xs} :
  suncons' (strans f s) = sum_map (tf_option_map f) (strans f) (suncons' s).
Proof. by case s. Qed.
Lemma suncons_strans {A F G x xs} {f : ∀ x : A, F x → G x} {s : _ (x :: xs)} :
  suncons (strans f s) = sum_map (f x) (strans f) (suncons s).
Proof. exact (suncons'_strans (xs:=_::_)). Qed.

(** Decompose [schoice F [x]] *)
Definition sunsingl {A F} {x : A} (s : schoice F [x]) : F x :=
  match suncons s with inl v => v | inr s => match s with end end.

(** Decompose [schoice F (xs ++ ys)] *)
Fixpoint sunapp {A F} {xs ys : list A}
  : schoice F (xs ++ ys) → schoice F xs + schoice F ys :=
  match xs with
  | [] => λ s, inr s
  | _ :: _ => λ s, match suncons s with inl v => inl (!0 v) | inr s =>
      match sunapp s with inl s => inl (+! s) | inr s => inr s end end
  end.

(** [strans] commutes with [strans] *)
Lemma sunapp_strans {A F G xs ys} {f : ∀ x : A, F x → G x} {s : _ (xs ++ ys)} :
  sunapp (strans f s) = sum_map (strans f) (strans f) (sunapp s).
Proof.
  elim: xs s=>//= x xs IH s. rewrite suncons_strans. case: (suncons s)=>//= s'.
  rewrite IH. by case (sunapp s').
Qed.
