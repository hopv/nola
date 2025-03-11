(** * Utility for [csum] *)

From nola Require Export prelude.
From iris.algebra Require Export csum.

(** Unfold [≡] over [csum] *)
Lemma csum_equiv' {A B : ofe} {s s' : csum A B} :
  s ≡ s' ↔
    match s, s' with
    | Cinl a, Cinl a' => a ≡ a'
    | Cinr b, Cinr b' => b ≡ b'
    | CsumInvalid, CsumInvalid => True
    | _, _ => False
    end.
Proof. split; [by case|]. case: s; case: s'=>//= *; by f_equiv. Qed.
(** Unfold [dist] over [csum] *)
Lemma csum_dist' {A B : ofe} {n} {s s' : csum A B} :
  s ≡{n}≡ s' ↔
    match s, s' with
    | Cinl a, Cinl a' => a ≡{n}≡ a'
    | Cinr b, Cinr b' => b ≡{n}≡ b'
    | CsumInvalid, CsumInvalid => True
    | _, _ => False
    end.
Proof. split; [by case|]. case: s; case: s'=>//= *; by f_equiv. Qed.

(** Unfold [≼] over [csum] *)
Lemma csum_included' {A B : cmra} {s s' : csum A B} :
  s ≼ s' ↔
    match s, s' with
    | _, CsumInvalid => True
    | Cinl a, Cinl a' => a ≼ a'
    | Cinr b, Cinr b' => b ≼ b'
    | _, _ => False
    end.
Proof. rewrite csum_included. case: s; case: s'; naive_solver. Qed.
(** Unfold [≼{_}] over [csum] *)
Lemma csum_includedN {A B : cmra} {s s' : csum A B} {n} :
  s ≼{n} s' ↔
    match s, s' with
    | _, CsumInvalid => True
    | Cinl a, Cinl a' => a ≼{n} a'
    | Cinr b, Cinr b' => b ≼{n} b'
    | _, _ => False
    end.
Proof. rewrite csum_includedN. case: s; case: s'; naive_solver. Qed.
