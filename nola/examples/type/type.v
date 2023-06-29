(** * [type]: Syntactic type *)

From nola.util Require Export ctx nat.

(** ** [tcon0]: Nullary type constructor *)
Variant tcon0 : Set :=
| (* Natural-number type *) tc_nat
| (* Boolean type *) tc_bool
| (* Unit type *) tc_unit
| (* Trivial type *) tc_any.

(** ** [tcon2]: Binary type constructor *)
Variant tcon2 : Set :=
| (* Intersection type *) tc_and
| (* Pair type *) tc_pair.

(** ** [type]: Syntactic type *)
Inductive type : nat → ctx nat → Set :=
(** Nullary type *)
| t_0 {i Γ} (c : tcon0) : type i Γ
(** Binary type *)
| t_2 {i Γ} (c : tcon2) (T U : type i Γ) : type i Γ
(** Terminating function type *)
| t_fun {i Γ} (j : nat) `{ji : ! j ≤ⁿ i} (T U : type i Γ) : type i Γ
(** Guard type *)
| t_guard {i j Γᵘ Γᵍ} (T : type j (;ᵞ Γᵘ ++ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ)
(** Reference type with an offset [o] *)
| t_ref {i j Γᵘ Γᵍ} (o : Z) (T : type j (;ᵞ Γᵘ ++ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ)
(** Universal and existential type *)
| t_forall j {i Γᵘ Γᵍ} (T : type i (j :: Γᵘ;ᵞ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ)
| t_exist j {i Γᵘ Γᵍ} (T : type i (j :: Γᵘ;ᵞ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ)
(** Recursive type *)
| t_rec j {i Γᵘ Γᵍ} `{ji : ! j ≤ⁿ i}
    (T : type j (j :: Γᵘ;ᵞ Γᵍ)) : type i (Γᵘ;ᵞ Γᵍ)
(** Ignore the first unguarded/guarded variable *)
| t_constu {i j Γᵘ Γᵍ} (T : type i (Γᵘ;ᵞ Γᵍ)) : type i (j :: Γᵘ;ᵞ Γᵍ)
| t_constg {i j Γᵘ Γᵍ} (T : type i (Γᵘ;ᵞ Γᵍ)) : type i (Γᵘ;ᵞ j :: Γᵍ)
(** Guarded variable *)
| t_varg {i Γᵘ Γᵍ} (s : schoice ((.≤ⁿ i)) Γᵍ) : type i (Γᵘ;ᵞ Γᵍ)
(** Unguarded variable *)
| t_varu {i Γᵘ Γᵍ} (s : schoice ((.<ⁿ i)) Γᵘ) : type i (Γᵘ;ᵞ Γᵍ)
(** Substituted [t_varu] *)
| t_subu {i j Γ} `{ji : ! j <ⁿ i} (T : type j (;ᵞ)) : type i Γ.

Notation "⟨ℕ⟩" := tc_nat : nola_scope.
Notation ℕ := (t_0 ⟨ℕ⟩).
Notation "⟨𝔹⟩" := tc_bool : nola_scope.
Notation 𝔹 := (t_0 ⟨𝔹⟩).
Notation "⟨𝟙⟩" := tc_unit : nola_scope.
Notation "𝟙" := (t_0 ⟨𝟙⟩) : nola_scope.
Notation "⟨⊤ᵗ⟩" := tc_any : nola_scope.
Notation "⊤ᵗ" :=  (t_0 ⟨⊤ᵗ⟩) : nola_scope.
Notation "⟨∧ᵗ⟩" := tc_and : nola_scope.
Infix "∧ᵗ" := (t_2 ⟨∧ᵗ⟩) (at level 55, right associativity) : nola_scope.
Notation "⟨×⟩" := tc_pair : nola_scope.
Infix "×" := (t_2 ⟨×⟩) (at level 50, left associativity) : nola_scope.
Notation "T →( j ) U" := (t_fun j T U)
  (at level 55, right associativity, format "T  →( j )  U") : nola_scope.
Notation "T →{ ji } ( j ) U" := (t_fun j (ji:=ji) T U)
  (at level 55, right associativity, only parsing) : nola_scope.
Notation "▽{ j , Γᵘ } T" := (t_guard (j:=j) (Γᵘ:=Γᵘ) T)
  (at level 20, right associativity, only parsing) : nola_scope.
Notation "▽ T" := (t_guard T) (at level 20, right associativity) : nola_scope.
Notation "ref{ j , Γᵘ } [ o ] T" := (t_ref o (j:=j) (Γᵘ:=Γᵘ) T)
  (at level 20, right associativity, only parsing) : nola_scope.
Notation "ref[ o ] T" := (t_ref o T)
  (at level 20, right associativity, format "ref[ o ]  T")
  : nola_scope.
Notation "ref{ j , Γᵘ } : T" := (t_ref 0 (j:=j) (Γᵘ:=Γᵘ) T)
  (at level 20, right associativity, only parsing) : nola_scope.
Notation "ref: T" := (t_ref 0 T) (at level 20, right associativity)
  : nola_scope.
Notation "∀: j , T" := (t_forall j T) (at level 100, right associativity)
  : nola_scope.
Notation "∃: j , T" := (t_exist j T) (at level 100, right associativity)
  : nola_scope.
Notation "recᵗ: j , T" := (t_rec j T) (at level 100, right associativity)
  : nola_scope.
Notation "recᵗ:{ ji } j , T" := (t_rec j (ji:=ji) T)
  (at level 100, right associativity, only parsing) : nola_scope.
Notation "¢ᵘ{ Γᵘ } T" := (t_constu (Γᵘ:=Γᵘ) T)
  (at level 20, right associativity, only parsing) : nola_scope.
Notation "¢ᵘ T" := (t_constu T) (at level 20, right associativity)
  : nola_scope.
Notation "¢ᵍ{ Γᵍ } T" := (t_constg (Γᵍ:=Γᵍ) T)
  (at level 20, right associativity, only parsing) : nola_scope.
Notation "¢ᵍ T" := (t_constg T) (at level 20, right associativity)
  : nola_scope.
Notation "%ᵍ s" := (t_varg s) (at level 20, right associativity) : nola_scope.
Notation "%ᵘ s" := (t_varu s) (at level 20, right associativity) : nola_scope.
Notation "!ᵘ T" := (t_subu T) (at level 20, right associativity) : nola_scope.
Notation "!ᵘ{ ji } T" := (t_subu (ji:=ji) T)
  (at level 20, right associativity, only parsing) : nola_scope.

(** ** [↑ᵗ T]: Bump the level [i] of a type [T] *)
Reserved Notation "↑ᵗ T" (at level 20, right associativity).
Fixpoint tbump {i j Γ} (T : type i Γ) : i ≤ⁿ j → type j Γ :=
  match T with
  | t_0 c => λ _, t_0 c | t_2 c T U => λ _, t_2 c (↑ᵗ T) (↑ᵗ U)
  | T →(j) U => λ ij, let _ := nle_trans _ ij in ↑ᵗ T →(j) ↑ᵗ U
  | ▽ T => λ _, ▽ T | ref[o] T => λ _, ref[o] T
  | ∀: j, T => λ _, ∀: j, ↑ᵗ T | ∃: j, T => λ _, ∃: j, ↑ᵗ T
  | recᵗ: j, T => λ ij, recᵗ:{nle_trans _ ij} j, T
  | ¢ᵘ T => λ _, ¢ᵘ ↑ᵗ T | ¢ᵍ T => λ _, ¢ᵍ ↑ᵗ T
  | %ᵍ s => λ ij, %ᵍ (strans (λ _ ki, nle_trans ki ij) s)
  | %ᵘ s => λ ij, %ᵘ (strans (λ _ ki, nlt_nle_trans ki ij) s)
  | !ᵘ T => λ ij, !ᵘ{nlt_nle_trans _ ij} T
  end
where "↑ᵗ T" := (tbump T _) (format "↑ᵗ  T") : nola_scope.

Notation "↑ᵗ{ ij } T" := (tbump T ij)
  (at level 20, right associativity, only parsing) : nola_scope.

(** [↑ᵗ] is idempotent *)
Lemma tbump_tbump `{ij : ! i ≤ⁿ j, jk : ! j ≤ⁿ k, ik : ! i ≤ⁿ k}
  {Γ} {T : type i Γ} : ↑ᵗ{jk} ↑ᵗ{ij} T = ↑ᵗ{ik} T.
Proof.
  move: i j k Γ T ij jk ik. fix FIX 5=> i j k Γ.
  case=>//=; intros; f_equal; try apply FIX;
    try (rewrite strans_strans; apply strans_cong=>/= >); apply proof_irrel.
Qed.
