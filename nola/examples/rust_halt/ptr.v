(** * Utility for pointer types *)

From nola.examples.rust_halt Require Export type.

Implicit Type l : loc.

(** ** Function *)

(** Memory copy *)
Definition memcpy : val := rec: "memcpy" ["tgt"; "len"; "src"] :=
  if: "len" ≤ #0 then #☠ else
    "tgt" <- !"src";; "memcpy" ["tgt" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].
Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Section twp.
  Context `{!lrustGS_gen hlc Σ}.

  (** [twp] over [memcpy] *)
  Lemma twp_memcpy vls vlt {W E ls lt  q n} :
    length vls = n → length vlt = n →
    [[{ ls ↦∗{q} vls ∗ lt ↦∗ vlt }]][W]
      #lt <-{n} !#ls @ E
    [[{ RET #☠; ls ↦∗{q} vls ∗ lt ↦∗ vls }]].
  Proof.
    move: ls vls lt vlt. elim: n=>/=.
    { move=> ?[|//]?[|//]_ _. iIntros (?) "[??] →Φ".
      rewrite heap_pointsto_vec_nil. wp_rec. wp_op. wp_case. iApply "→Φ".
      iFrame. }
    move=> n IH ?[//|? vls]?[//|? vlt]/=[?][?]. iIntros (?).
    rewrite !heap_pointsto_vec_cons. iIntros "[[↦s ↦sl] [↦t ↦tl]] →Φ". wp_rec.
    wp_op. wp_case. wp_read. wp_write. do 3 wp_op.
    have -> : (S n - 1)%Z = n by lia.
    wp_apply (IH _ vls _ vlt with "[$↦sl $↦tl]")=>//. iIntros "[??]".
    iApply "→Φ". iFrame.
  Qed.
End twp.

(** ** Read and write *)

Section read_write.
  Context `{!rust_haltGS CON Σ, rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ)}.

  (** [read]: Read from a pointer type *)
  Definition read_def {X Y X'} (α : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (T' : ty CON Σ X') (get : X → Y) (set : X → X') : iProp Σ :=
    □ ∀ q t d xπ v, q.[α] -∗ na_own t ⊤ -∗ ⟦ T.1 t d xπ [v] ⟧ᶜ
      =[rust_halt_wsat]{⊤}=∗ ∃ l wl du r,
        ⌜v = # l⌝ ∗ l ↦∗{r} wl ∗ ⟦ U.1 t du (get ∘ xπ) wl ⟧ᶜ ∗
        (l ↦∗{r} wl =[rust_halt_wsat]{⊤}=∗ ∃ d',
          q.[α] ∗ na_own t ⊤ ∗ ⟦ T'.1 t d' (set ∘ xπ) [v] ⟧ᶜ).
  Lemma read_aux : seal (@read_def). Proof. by eexists _. Qed.
  Definition read {X Y X'} := read_aux.(unseal) X Y X'.
  Lemma read_unseal : @read = @read_def. Proof. by exact: seal_eq. Qed.

  (** [read] is persistent *)
  #[export] Instance read_persistent {X Y X' α T U T' get set} :
    Persistent (@read X Y X' α T U T' get set).
  Proof. rewrite read_unseal. exact _. Qed.

  (** [write]: Write to a pointer type *)
  Definition write_def {X Y Y' X'} (α : lft) (T : ty CON Σ X) (U : ty CON Σ Y)
    (U' : ty CON Σ Y') (T' : ty CON Σ X') (get : X → Y) (set : X → Y' → X')
    : iProp Σ :=
    □ ∀ q t d xπ v, q.[α] -∗ ⟦ T.1 t d xπ [v] ⟧ᶜ
      =[rust_halt_wsat]{⊤}=∗ ∃ l wl du,
        ⌜v = # l⌝ ∗ l ↦∗ wl ∗ ⟦ U.1 t du (get ∘ xπ) wl ⟧ᶜ ∗
        (∀ du' yπ' wl', l ↦∗ wl' -∗ ⟦ U'.1 t du' yπ' wl' ⟧ᶜ
          =[rust_halt_wsat]{⊤}=∗ ∃ d',
          q.[α] ∗ ⟦ T'.1 t d' (λ π, set (xπ π) (yπ' π)) [v] ⟧ᶜ).
  Lemma write_aux : seal (@write_def). Proof. by eexists _. Qed.
  Definition write {X Y Y' X'} := write_aux.(unseal) X Y Y' X'.
  Lemma write_unseal : @write = @write_def. Proof. by exact: seal_eq. Qed.

  (** [write] is persistent *)
  #[export] Instance write_persistent {X Y Y' X' α T U U' T' get set} :
    Persistent (@write X Y Y' X' α T U U' T' get set).
  Proof. rewrite write_unseal. exact _. Qed.

  (** Reading a value from a pointer *)
  Lemma type_read
    `{!EtcxExtract (X:=X) (Yl:=Zl) (Zl:=Zl') (v ◁ T) Γ Γr get' getr}
    `{!Ty (X:=Y) U 1} {X' T' get set α} :
    read (X':=X') α T U T' get set ⊢
      type α Γ (!v) (λ r, r ◁ U ᵖ:: v ◁ T' ᵖ:: Γr)
        (λ post zl, let x := get' zl in post (get x, set x, getr zl)').
  Proof.
    rewrite read_unseal type_unseal. iIntros "#read !>" (????) "α t pre".
    rewrite etcx_extract /=. iIntros "[[% T] Γr]".
    iMod ("read" with "α t T") as (? wl ?? ->) "(↦ & U & →T')".
    iDestruct (ty_own_size with "U") as %?. destruct wl as [|w[|??]]=>//.
    rewrite heap_pointsto_vec_singleton. wp_read.
    iMod ("→T'" with "↦") as (?) "($ & $ & T')". iModIntro. iFrame "pre".
    iFrame.
  Qed.

  (** Writing a value to a pointer *)
  Lemma type_write
    `{!TcxExtract (Xl:=[X;Y]) (Yl:=Zl) (Zl:=Zl') ᵖ[v ◁ T; w ◁ U] Γ Γr get' getr}
    `{!Ty (X:=Y') U' 1} {X' T' get set α} :
    write (Y:=Y') (X':=X') α T U' U T' get set ⊢
      type α Γ (v <- w) (λ _, v ◁ T' ᵖ:: Γr)
        (λ post zl, let '(x, y, _)' := get' zl in post (set x y, getr zl)').
  Proof.
    rewrite write_unseal type_unseal.
    iIntros "#write !>" (????) "α $ pre". rewrite tcx_extract /=.
    iIntros "[([% T] & [% U] & _) Γr]".
    iMod ("write" with "α T") as (? wl ? ->) "(↦ & U' & →T')".
    iDestruct (ty_own_size with "U'") as %?. destruct wl as [|?[|??]]=>//.
    rewrite heap_pointsto_vec_singleton. wp_write.
    rewrite -heap_pointsto_vec_singleton.
    iMod ("→T'" with "↦ U") as (?) "($ & Tt')". iModIntro. iFrame "pre". iFrame.
  Qed.

  (** Memory copy *)
  Lemma type_memcopy
    `{!TcxExtract (Xl:=[Xs; Xt]) (Yl:=Zl) (Zl:=Zl') ᵖ[vs ◁ Ts; vt ◁ Tt] Γ Γr
        get getr, !Ty (X:=Y) U sz, !Ty (X:=Y') U' sz}
    {Xs' Ts' gets sets Xt' Tt' gett sett α} :
    read (Y:=Y) (X':=Xs') α Ts U Ts' gets sets -∗
    write (Y:=Y') (X':=Xt') α Tt U' U Tt' gett sett -∗
      type α Γ (vt <-{sz} !vs)%E (λ _, vs ◁ Ts' ᵖ:: vt ◁ Tt' ᵖ:: Γr)
        (λ post zl, let '(xs, xt, _)' := get zl in
          post (sets xs, sett xt (gets xs), getr zl)').
  Proof.
    rewrite read_unseal write_unseal type_unseal.
    iIntros "#read #write !>" (????) "[α α'] t pre". rewrite tcx_extract /=.
    iIntros "[([% Ts] & [% Tt] & _) Γr]".
    iMod ("read" with "α t Ts") as (? wls ?? ->) "(↦s & U & →Ts')".
    iMod ("write" with "α' Tt") as (? wlt ? ->) "(↦t & U' & →Tt')".
    iDestruct (ty_own_size with "U") as %?.
    iDestruct (ty_own_size with "U'") as %?.
    wp_apply (twp_memcpy wls wlt with "[$↦s $↦t]")=>//. iIntros "[↦s ↦t]".
    iMod ("→Ts'" with "↦s") as (?) "($ & $ & Ts')".
    iMod ("→Tt'" with "↦t U") as (?) "($ & Tt')". iModIntro. iFrame "pre".
    iFrame.
  Qed.
End read_write.
