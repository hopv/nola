(** * Main logic *)

From nola.util Require Import tagged.
From nola.iris Require Export cif inv pborrow.
From nola.bi Require Import util.
From nola.heap_lang Require Export notation proofmode.
From nola.examples Require Export nsynty.
Import ProdNotation FunNPNotation UpdwNotation WpwNotation iPropAppNotation
  ProphNotation LftNotation NsyntyNotation FunPRNotation DsemNotation.

Implicit Type (Σ : gFunctors) (N : namespace) (TY : synty) (dq : dfrac)
  (l : loc) (b : bool) (α β : lft) (q : Qp).

(** ** Invariant *)
(** [invCC]: Constructor *)
Variant invCC_id := .
Definition invCC :=
  Cifcon invCC_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [InvCon]: [invCC] registered *)
Notation InvCon CON := (Ecifcon invCC CON).
Section cif_inv.
  Context `{!InvCon CON} {Σ}.
  (** [cif_inv]: Formula *)
  Definition cif_inv N (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom invCC N nullary (unary Px) ().
  (** [cif_inv] is non-expansive *)
  #[export] Instance cif_inv_ne {N} : NonExpansive (cif_inv N).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_inv_proper {N} : Proper ((≡) ==> (≡)) (cif_inv N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv] is productive *)
  #[export] Instance cif_inv_productive {N} : Productive (cif_inv N).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.
  Context `{!inv'GS (cifOF CON) Σ}.
  (** Semantics of [invCC] *)
  #[export] Program Instance inv_sem_ecifcon {JUDG}
    : SemEcifcon JUDG invCC CON Σ :=
    SEM_ECIFCON (λ _ _ N _ Φx _, inv_tok N (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_inv.
(** [invCC] semantics registered *)
Notation InvSem JUDG CON Σ := (EsemEcifcon JUDG invCC CON Σ).

(** ** Borrow *)
(** [borCC]: Constructor *)
Variant borCC_id := .
Definition borCC :=
  Cifcon borCC_id lft (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [BorCon]: [borCC] registered *)
Notation BorCon CON := (Ecifcon borCC CON).
Section cif_bor.
  Context `{!BorCon CON} {Σ}.
  (** [cif_bor]: Formula *)
  Definition cif_bor α (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom borCC α nullary (unary Px) ().
  (** [cif_bor] is non-expansive *)
  #[export] Instance cif_bor_ne {α} : NonExpansive (cif_bor α).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_bor_proper {α} : Proper ((≡) ==> (≡)) (cif_bor α).
  Proof. apply ne_proper, _. Qed.
  (** [cif_bor] is productive *)
  #[export] Instance cif_bor_productive {α} : Productive (cif_bor α).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.
  Context `{!pborrowGS TY (cifOF CON) Σ}.
  (** Semantics of [borCC] *)
  #[export] Program Instance bor_sem_ecifcon {JUDG}
    : SemEcifcon JUDG borCC CON Σ :=
    SEM_ECIFCON (λ _ _ α _ Φx _, nbor_tok α (Φx ())) _.
  Next Obligation. move=>/= ???*???*?? eqv ???. f_equiv. apply eqv. Qed.
End cif_bor.
(** [borCC] semantics registered *)
Notation BorSem JUDG CON Σ := (EsemEcifcon JUDG borCC CON Σ).

(** ** Prophetic borrow *)
(** [pborCC]: Constructor *)
Variant pborCC_id := .
Definition pborCC TY :=
  Cifcon pborCC_id (lft *' TY) (λ _, Empty_set) (λ '(_, X)', X)
    (λ '(_, X)', leibnizO (X *' prvar X)) _.
(** [PborCon]: [pborCC] registered *)
Notation PborCon TY CON := (Ecifcon (pborCC TY) CON).
Section cif_pbor.
  Context `{!PborCon TY CON} {Σ}.
  Implicit Type X : TY.
  (** [cif_pbor]: Formula *)
  Definition cif_pbor {X} α (x : X) (ξ : prvar X) (Φx : X -pr> cif CON Σ)
    : cif CON Σ :=
    cif_ecustom (pborCC TY) (α, X)' nullary Φx (x, ξ)'.
  (** [cif_pbor] is non-expansive *)
  #[export] Instance cif_pbor_ne {X α x ξ} : NonExpansive (@cif_pbor X α x ξ).
  Proof. solve_proper. Qed.
  #[export] Instance cif_pbor_proper {X α x ξ} :
    Proper ((≡) ==> (≡)) (@cif_pbor X α x ξ).
  Proof. apply ne_proper, _. Qed.
  (** [cif_pbor] is productive *)
  #[export] Instance cif_pbor_productive {X α x ξ} :
    Productive (@cif_pbor X α x ξ).
  Proof. solve_proper. Qed.
  Context `{!pborrowGS TY (cifOF CON) Σ}.
  (** Semantics of [pborCC] *)
  #[export] Program Instance pbor_sem_ecifcon {JUDG}
    : SemEcifcon JUDG (pborCC TY) CON Σ :=
    SEM_ECIFCON (λ _ _ '(α, X)' _ Φx '(x, ξ)', pbor_tok α x ξ Φx) _.
  Next Obligation. move=>/= ???*???*?*?? /leibniz_equiv_iff. solve_proper. Qed.
End cif_pbor.
(** [pborCC] semantics registered *)
Notation PborSem TY JUDG CON Σ := (EsemEcifcon JUDG (pborCC TY) CON Σ).

(** ** Judgment *)
Variant iff_judg_id := .
Definition iff_judgty (FM : ofe) : ofe := tagged iff_judg_id (FM * FM).
Notation IffJudg FM JUDG := (Ejudg (iff_judgty FM) JUDG).
Section iff_judg.
  Context `{iff_judg : !IffJudg FM JUDG}.
  Definition jiff (Px Qx : FM) : JUDG := iff_judg (Tagged (Px, Qx)).
  #[export] Instance jiff_ne : NonExpansive2 jiff.
  Proof. solve_proper. Qed.

  Context `{!Dsem JUDG FM (iProp Σ)}.
  (** ** [iff_judg_sem]: Semantics of [iff_judgty] *)
  Definition iff_judg_sem δ (PQx : iff_judgty FM) : iProp Σ :=
    □ (⟦ PQx.(untag).1 ⟧(δ) ∗-∗ ⟦ PQx.(untag).2 ⟧(δ)).
  (** [iff_judg_sem] is non-expansive *)
  #[export] Instance iff_judg_sem_ne {δ} : NonExpansive (iff_judg_sem δ).
  Proof. solve_proper. Qed.
  (** [Dsem] over [iff_judgty] *)
  #[export] Instance iff_judg_dsem
    : Dsem JUDG (iff_judgty FM) (iProp Σ) := DSEM iff_judg_sem _.
End iff_judg.
(** ** [IffJsem]: Judgment semantics for [iff] *)
Notation IffJsem FM Σ JUDG := (Ejsem (iff_judgty FM) JUDG (iProp Σ)).

Section iff_judg.
  Context `{!Jsem JUDG (iProp Σ), !Dsem JUDG FM (iProp Σ), !IffJudg FM JUDG,
    !IffJsem FM Σ JUDG}.

  (** Derivability of [jiff] is persistent *)
  #[export] Instance Deriv_jiff_persistent `{!Deriv (JUDG:=JUDG) ih δ} {Px Qx} :
    Persistent (δ (jiff Px Qx)).
  Proof. apply: Deriv_persistent=> ????. rewrite sem_ejudg. exact _. Qed.
End iff_judg.

(** ** Relaxed invariant *)
(** [inv']: Proposition *)
Section inv'.
  Context `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG}.
  Implicit Type δ : JUDG -n> iProp Σ.
  (** [inv']: Relaxed invariant *)
  Definition inv' δ N Px : iProp Σ := ∃ Qx, δ (jiff Px Qx) ∗ inv_tok N Qx.
  (** [inv'] is non-expansive *)
  #[export] Instance inv'_ne {δ N} : NonExpansive (inv' δ N).
  Proof. solve_proper. Qed.
  #[export] Instance inv'_proper {δ N} :
    Proper ((≡) ==> (⊣⊢)) (inv' δ N).
  Proof. apply ne_proper, _. Qed.
End inv'.
(** Notation *)
Notation invd := (inv' der).
(** [inv'CC]: Constructor *)
Variant inv'CC_id := .
Definition inv'CC :=
  Cifcon inv'CC_id namespace (λ _, Empty_set) (λ _, unit) (λ _, unitO) _.
(** [Inv'Con]: [inv'CC] registered *)
Notation Inv'Con CON := (Ecifcon inv'CC CON).
Section cif_inv'.
  Context `{!Inv'Con CON} {Σ}.
  (** [cif_inv']: Formula *)
  Definition cif_inv' N (Px : cif CON Σ) : cif CON Σ :=
    cif_ecustom inv'CC N nullary (unary Px) ().
  (** [cif_inv'] is non-expansive *)
  #[export] Instance cif_inv'_ne {N} : NonExpansive (cif_inv' N).
  Proof. move=> ????. apply cif_ecustom_ne; solve_proper. Qed.
  #[export] Instance cif_inv'_proper {N} : Proper ((≡) ==> (≡)) (cif_inv' N).
  Proof. apply ne_proper, _. Qed.
  (** [cif_inv'] is productive *)
  #[export] Instance cif_inv'_productive {N} : Productive (cif_inv' N).
  Proof.
    move=> ????. apply cif_ecustom_preserv_productive=>//.
    by apply fun_proeq_later.
  Qed.

  Context `{!inv'GS (cifOF CON) Σ, !IffJudg (cifO CON Σ) JUDG}.
  (** Semantics of [invCC] *)
  #[export] Program Instance inv'_sem_ecifcon
    : SemEcifcon JUDG inv'CC CON Σ :=
    SEM_ECIFCON (λ _ δ N _ Φx _, inv' δ N (Φx ())) _.
  Next Obligation. move=> ??*???*?? eqv ?*. f_equiv. apply eqv. Qed.
End cif_inv'.
(** [inv'CC] semantics registered *)
Notation Inv'Sem JUDG CON Σ := (EsemEcifcon JUDG inv'CC CON Σ).

Section verify.
  Context `{!heapGS_gen hlc Σ, !SemCifcon JUDG CON Σ, !Jsem JUDG (iProp Σ)}.
  Context `{!inv'GS (cifOF CON) Σ, !InvCon CON, !InvSem JUDG CON Σ}.
  Implicit Type (Px Qx : cif CON Σ) (Φx Ψx : loc → cif CON Σ).

  (** ** Linked list *)

  (** [cif_ilist]: Formula for a list *)
  Definition cif_ilist_gen N (Φx : loc -pr> cif CON Σ)
    (Ilist : loc -pr> cif CON Σ) : loc -pr> cif CON Σ :=
    λ l, (cif_inv N (Φx l) ∗ cif_inv N (∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ Ilist l'))%cif.
  #[export] Instance ilist_gen_productive {n N} :
    Proper (proeq_later n ==> proeq_later n ==> proeq n) (cif_ilist_gen N).
  Proof.
    move=>/= ?? eq ?? eq' ?. unfold cif_ilist_gen.
    f_equiv; apply cif_inv_productive; (destruct n as [|n]; [done|]);
      [apply eq|]=>/=.
    f_equiv=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_productive' {N Φx} :
    Productive (cif_ilist_gen N Φx).
  Proof. move=> ?. by apply ilist_gen_productive. Qed.
  Definition cif_ilist N (Φx : loc -pr> cif CON Σ) : loc -pr> cif CON Σ :=
    profix (cif_ilist_gen N Φx).
  (** Unfold [cif_ilist] *)
  Lemma cif_ilist_unfold {N Φx l} :
    cif_ilist N Φx l ≡ cif_ilist_gen N Φx (cif_ilist N Φx) l.
  Proof. by rewrite /cif_ilist (profix_unfold (f:=cif_ilist_gen _ _) l). Qed.
  (** Semantics *)
  Definition ilist N Φx l : iProp Σ := inv_tok N (Φx l) ∗
    inv_tok N (∃ l', ▷ (l +ₗ 1) ↦ #l' ∗ cif_ilist N Φx l')%cif.
  (** Unfold semantics over [cif_ilist] *)
  Lemma sem_ilist {δ N Φx l} :
    cif_sem δ (cif_ilist N Φx l) ⊣⊢ ilist N Φx l.
  Proof. by rewrite cif_ilist_unfold /= !sem_ecustom /=. Qed.

  (** [cif_ilist] is productive *)
  #[export] Instance cif_ilist_productive {N} : Productive (cif_ilist N).
  Proof. move=> ????. apply profix_preserv=> ?. by f_equiv. Qed.

  (** [cif_ilist_gen] is non-expansive *)
  #[export] Instance cif_ilist_gen_ne {N} : NonExpansive2 (cif_ilist_gen N).
  Proof.
    unfold cif_ilist_gen=> ????????. (do 3 f_equiv=>//)=> ?. by f_equiv.
  Qed.
  #[export] Instance cif_ilist_gen_proper {N} :
    Proper ((≡) ==> (≡) ==> (≡)) (cif_ilist_gen N).
  Proof. apply ne_proper_2, _. Qed.
  (** [cif_ilist] is non-expansive *)
  #[export] Instance cif_ilist_ne {N} : NonExpansive (cif_ilist N).
  Proof. move=> ????. apply profix_ne=> ???. by f_equiv. Qed.
  #[export] Instance cif_ilist_proper {N} :
    Proper ((≡) ==> (≡)) (cif_ilist N).
  Proof. apply ne_proper, _. Qed.

  (** Access the tail of a list *)
  Definition tail_ilist : val := λ: "l", !("l" +ₗ #1).
  Lemma twp_tail_list {N E Φx l} : ↑N ⊆ E →
    [[{ ilist N Φx l }]][inv_wsat ⟦⟧]
      tail_ilist #l @ E
    [[{ l', RET #l'; ilist N Φx l' }]].
  Proof.
    iIntros (? Ψ) "/= [_ #itl] →Ψ". wp_rec. wp_pure.
    iMod (inv_tok_acc with "itl") as "/=[(%l' & >↦l' & ltl) cl]"; [done|].
    rewrite sem_ilist. iDestruct "ltl" as "#ltl".
    wp_load. iModIntro. iMod ("cl" with "[$↦l']") as "_".
    { by rewrite sem_ilist. }
    iModIntro. iApply ("→Ψ" with "ltl").
  Qed.

  (** Iterate over a list *)
  Definition iter_ilist : val := rec: "self" "f" "c" "l" :=
    if: !"c" ≤ #0 then #() else
      "f" "l";; "c" <- !"c" - #1;; "self" "f" "c" (tail_ilist "l").
  Lemma twp_iter_list {N E Φx c l} {f : val} {n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      iter_ilist f #c #l @ E
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "% #f /=" (Ψ) "!> [c↦ #l] →Ψ".
    iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply "f".
    { iDestruct "l" as "[$ _]". }
    iIntros "_". wp_load. wp_store. have -> : (S m - 1)%Z = m by lia.
    wp_apply twp_tail_list; [done..|]. iIntros (l') "#ltl".
    iApply ("IH" with "c↦ →Ψ ltl").
  Qed.

  (** Iterate over a list with two threads *)
  Lemma twp_fork_iter_list {N E Φx c' c l} {f : val} {m n : nat} : ↑N ⊆ E →
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l' @ E
      [[{ RET #(); True }]]) -∗
    [[{ c' ↦ #m ∗ c ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      Fork (iter_ilist f #c' #l);; iter_ilist f #c #l @ E
    [[{ RET #(); c ↦ #0 }]].
  Proof.
    iIntros "% #f" (Ψ) "!> (↦' & ↦ & #l) →Ψ". wp_apply (twp_fork with "[↦']").
    { iApply (twp_mask_mono _ E); [done|].
      wp_apply (twp_iter_list with "f [$↦' $l //]"); [done|]. by iIntros. }
    wp_pures. by wp_apply (twp_iter_list with "f [$↦ $l //]").
  Qed.

  (** Iterate over an unbounded number of elements of a list with an unbounded
    number of threads *)
  Definition forks_iter_list : val := rec: "self" "f" "k" "l" :=
    if: !"k" ≤ #0 then #() else
      Fork (let: "c" := ref Ndnat in iter_ilist "f" "c" "l");;
      "k" <- !"k" - #1;; "self" "f" "k" "l".
  Lemma twp_forks_iter_list {N E Φx k l} {f : val} {n : nat} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l'
      [[{ RET #(); True }]]) -∗
    [[{ k ↦ #n ∗ ilist N Φx l }]][inv_wsat ⟦⟧]
      forks_iter_list f #k #l @ E
    [[{ RET #(); k ↦ #0 }]].
  Proof.
    iIntros "#f" (Ψ) "!> [↦ #l] →Ψ". iInduction n as [|m] "IH" forall (l) "l".
    { wp_rec. wp_load. wp_pures. by iApply "→Ψ". }
    wp_rec. wp_load. wp_pures. wp_apply twp_fork.
    { wp_apply twp_ndnat; [done|]. iIntros (?) "_". wp_alloc c as "↦".
      wp_pures. wp_apply (twp_iter_list with "f [$↦ $l //]"); by [|iIntros]. }
    wp_load. wp_op. have -> : (S m - 1)%Z = m by lia. wp_store.
    iApply ("IH" with "↦ →Ψ l").
  Qed.
  Lemma twp_nd_forks_iter_list {N E Φx l} {f : val} :
    (∀ l', [[{ inv_tok N (Φx l') }]][inv_wsat ⟦⟧] f #l'
      [[{ RET #(); True }]]) -∗
    [[{ ilist N Φx l }]][inv_wsat ⟦⟧]
      let: "k" := ref Ndnat in forks_iter_list f "k" #l @ E
    [[{ RET #(); True }]].
  Proof.
    iIntros "#f" (Ψ) "!> #l →Ψ". wp_apply twp_ndnat; [done|]. iIntros (?) "_".
    wp_alloc k as "↦". wp_pures.
    wp_apply (twp_forks_iter_list with "f [$↦ $l //]"). iIntros "_".
    by iApply "→Ψ".
  Qed.

  (** ** Mutex operations *)
  (** Try to acquire the lock on the mutex *)
  Definition try_acquire_mutex : val := λ: "l", CAS "l" #false #true.
  (** Try to acquire the lock on the mutex repeatedly with a timeout *)
  Definition try_acquire_loop_mutex : val :=
    rec: "self" "n" "l" :=
      if: "n" = #0 then #false else
      if: try_acquire_mutex "l" then #true else "self" ("n" - #1) "l".
  (** Release the lock on the mutex *)
  Definition release_mutex : val := λ: "l", "l" <- #false.

  Context `{!pborrowGS nsynty (cifOF CON) Σ, !BorCon CON, !BorSem JUDG CON Σ}.

  (** ** On borrows *)

  (** Dereference a nested mutable reference *)
  Lemma bor_bor_deref {α β l Φx q} :
    [[{ β ⊑□ α ∗ q.[β] ∗
      nbor_tok β (∃ l', ▷ l ↦ #l' ∗ cif_bor α (Φx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l'; q.[β] ∗ nbor_tok β (Φx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (nbor_tok_open (M:=bupd) with "β b") as "/=[o [%l'[>↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    rewrite sem_ecustom /=.
    iMod (nbor_tok_reborrow (M:=bupd) with "⊑ α b'") as "(α & →b' & b')".
    iDestruct ("→β'" with "α") as "β'".
    iMod (nobor_tok_subdiv (M:=bupd) [] with "[] o [] [↦ →b']") as "[β _]"=>/=.
    { iApply lft_sincl_refl. } { done. }
    { iIntros "† _". iModIntro. iExists _. iFrame "↦". rewrite sem_ecustom /=.
      by iApply "→b'". }
    iModIntro. iApply "→Ψ". iFrame.
  Qed.

  Context `{!PborCon nsynty CON, !PborSem nsynty JUDG CON Σ}.
  Implicit Type X : nsynty.

  (** Dereference a nested prophetic mutable reference *)
  Lemma pbor_pbor_deref {X η ξ α β l Φxx q} {x : X} :
    [[{ β ⊑□ α ∗ q.[β] ∗
        pbor_tok β ((x, ξ)' : _ *'ₛ prvarₛ _) η
          (λ '(x', ξ')', ∃ l', ▷ l ↦ #l' ∗ cif_pbor α x' ξ' (Φxx l'))%cif }]]
      [pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ l', RET #l';
        q.[β] ∗ ∃ ξ' : prvar X,
          ⟨π, π η = (π ξ', ξ)'⟩ ∗ pbor_tok β x ξ' (Φxx l') }]].
  Proof.
    iIntros (Ψ) "(#⊑ & [β β'] & b) →Ψ".
    iMod (pbor_tok_open (M:=bupd) with "β b") as "/=[o[%l'[>↦ b']]]".
    iApply twpw_fupdw_nonval; [done|]. wp_load. iModIntro.
    iMod (lft_sincl_live_acc with "⊑ β'") as (?) "[α →β']".
    rewrite sem_ecustom /=.
    iMod (pobor_pbor_tok_reborrow (TY:=nsynty) (M:=bupd)
      (λ _, (_,_)' : _ *'ₛ _) with "⊑ o α b' [↦]") as (?) "(β & α & obs & b)".
    { iIntros "/=% _ ? !>". iExists _. iFrame "↦". by rewrite sem_ecustom /=. }
    iModIntro. iApply "→Ψ". iDestruct ("→β'" with "α") as "$". iFrame.
  Qed.

  (** Load from an immutable shared borrow *)
  Lemma imbor_load {l α q} {n : Z} :
    [[{ q.[α] ∗ inv_tok nroot (cif_bor α (▷ l ↦ #n)) }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      !#l
    [[{ RET #n; q.[α] }]].
  Proof.
    iIntros (Φ) "[α #i] →Φ". iMod (inv_tok_acc with "i") as "/=[b cl]"; [done|].
    rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd) with "α b") as "/=[o >↦]". wp_load. iModIntro.
    iMod (nobor_tok_close (M:=bupd) with "o [↦]") as "[α b]"=>/=; [done|].
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Shared borrow of a mutex *)
  Definition cif_mutex_bor' α l Px :=
    cif_bor α ((▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true).
  Definition mutex_bor α l Px := inv_tok nroot (cif_mutex_bor' α l Px).
  Definition cif_mutex_bor α l Px := cif_inv nroot (cif_mutex_bor' α l Px).
  (** [cif_mutex_bor'] is productive *)
  #[export] Instance cif_mutex_bor'_productive {α l} :
    Productive (cif_mutex_bor' α l).
  Proof.
    unfold cif_mutex_bor'=> n ?? eq. f_equiv. destruct n as [|n]=>//=.
    do 3 f_equiv. move: eq. apply proeq_later_anti. lia.
  Qed.
  #[export] Instance cif_mutex_bor_productive {α l} :
    Productive (cif_mutex_bor α l).
  Proof.
    unfold cif_mutex_bor=> n ?? eq. f_equiv. destruct n as [|n]=>//=. f_equiv.
    move: eq. apply proeq_later_anti. lia.
  Qed.
  (** [cif_mutex_bor'] is non-expansive *)
  #[export] Instance cif_mutex_bor'_ne {α l} :
    NonExpansive (cif_mutex_bor' α l).
  Proof. solve_proper. Qed.
  #[export] Instance cif_mutex_bor'_proper {α l} :
    Proper ((≡) ==> (≡)) (cif_mutex_bor' α l).
  Proof. apply ne_proper, _. Qed.
  #[export] Instance cif_mutex_bor_ne {α l} : NonExpansive (cif_mutex_bor α l).
  Proof. solve_proper. Qed.
  #[export] Instance cif_mutex_bor_proper {α l} :
    Proper ((≡) ==> (≡)) (cif_mutex_bor α l).
  Proof. apply ne_proper, _. Qed.

  (** Try to acquire a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_try_acquire {α l Px q} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      try_acquire_mutex #l
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#m [α α']] →Φ". wp_lam. wp_bind (CmpXchg _ _ _).
    iMod (inv_tok_acc with "m") as "/=[b cl]"; [done|]. rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd) with "α b") as "[o big]".
    rewrite /= sem_ecustom.
    iDestruct "big" as "[[>↦ b']|>↦]"; [wp_cmpxchg_suc|wp_cmpxchg_fail];
      iModIntro;
      (iMod (nobor_tok_close (M:=bupd) with "o [↦]") as "[α b]"=>/=;
        [by iFrame|]);
      iMod ("cl" with "b") as "_"; iModIntro; wp_pure; iApply "→Φ"; by iFrame.
  Qed.
  (** [mutex_bor_try_acquire], repeatedly with a timeout *)
  Lemma mutex_bor_try_acquire_loop {α l Px q} {n : nat} :
    [[{ mutex_bor α l Px ∗ q.[α] }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      try_acquire_loop_mutex #n #l
    [[{ b, RET #b; (if b then nbor_tok α Px else True) ∗ q.[α] }]].
  Proof.
    iIntros (Φ) "[#l α] →Φ". iInduction n as [|n] "IH".
    { wp_lam. wp_pures. iApply "→Φ". by iFrame. }
    wp_lam. wp_pures. wp_apply (mutex_bor_try_acquire with "[$l $α //]").
    iIntros ([|]).
    - iIntros "?". wp_pures. iModIntro. by iApply "→Φ".
    - iIntros "[_ α]". wp_pures. have ->: (S n - 1)%Z = n by lia.
      iApply ("IH" with "α →Φ").
  Qed.

  (** Release a lock from a shared borrow over a mutex *)
  Lemma mutex_bor_release {α l Px q} :
    [[{ mutex_bor α l Px ∗ nbor_tok α Px ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      release_mutex #l
    [[{ RET #(); q.[α] }]].
  Proof.
    iIntros (Φ) "(#m & b' & α) →Φ". wp_lam.
    iMod (inv_tok_acc with "m") as "/=[b cl]"; [done|].
    rewrite sem_ecustom /=.
    iMod (nbor_tok_open (M:=bupd) with "α b") as "[o big]"=>/=.
    iAssert (∃ b, ▷ l ↦ #b)%I with "[big]" as (?) ">↦".
    { iDestruct "big" as "[[$ _]|$]". }
    wp_store. iModIntro.
    iMod (nobor_tok_close (M:=bupd) with "o [b' ↦]") as "[α b]"=>/=.
    { iLeft. rewrite sem_ecustom /=. iFrame. }
    iMod ("cl" with "b") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** Create a shared borrow and a lender of a mutex *)
  Lemma mutex_bor_lend_new {α l Px b q} :
    l ↦ #b -∗ ⟦ Px ⟧ -∗ q.[α] =[inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]=∗
      mutex_bor α l Px ∗ nlend_tok α (∃ b', ▷ l ↦ #b' ∗ Px)%cif ∗ q.[α].
  Proof.
    iIntros "↦ Px α".
    iMod (nbor_nlend_tok_new (M:=bupd) with "[↦ Px]") as "[b $]"; [by iFrame|].
    iMod (nbor_tok_open (M:=bupd) with "α b") as "/=[o[%b'[↦ Px]]]".
    iMod (nobor_tok_subdiv (FML:=cifOF CON) (M:=bupd)
      [∃ b', ▷ l ↦ #b'; Px]%cif with "[] o [↦ Px] []")
      as "(α & _ & (b & b' & _))"=>/=.
    { iApply lft_sincl_refl. } { iSplitL "↦"; iFrame. }
    { by iIntros "_ [[% $][$ _]]". }
    iMod (nbor_tok_open (M:=bupd) with "α b") as "/=[o ↦]".
    iMod (nobor_tok_subdiv (FML:=cifOF CON) (M:=bupd)
      [(▷ l ↦ #false ∗ cif_bor α Px) ∨ ▷ l ↦ #true]%cif with "[] o [↦ b'] []")
      as "($ & _ & [b _])"=>/=. { iApply lft_sincl_refl. }
    { iSplit; [|done]. rewrite sem_ecustom /=.
      iDestruct "↦" as ([|]) "↦"; [|iLeft]; iFrame. }
    { by iIntros "_ [[[$ _]|$]_]". }
    iMod (inv_tok_alloc with "[b]") as "$"=>//=. by rewrite sem_ecustom.
  Qed.

  (** ** Linked list with a shared borrow over a mutex *)

  (** [cif_mblist]: Formula for a list with a shared borrow over a mutex *)
  Definition cif_mblist_gen α (Φx : loc -pr> cif CON Σ)
    (Mblist : loc -pr> cif CON Σ) : loc -pr> cif CON Σ :=
    λ l, cif_mutex_bor α l (Φx (l +ₗ 1) ∗ ∃ l', ▷ (l +ₗ 2) ↦ #l' ∗ Mblist l').
  #[export] Instance cif_mblist_gen_productive {α Φx} :
    Productive (cif_mblist_gen α Φx).
  Proof.
    move=>/= n ?? eq ?. unfold cif_mblist_gen. apply cif_mutex_bor_productive.
    destruct n as [|n]=>//=. (do 2 f_equiv)=> ?. f_equiv. apply eq.
  Qed.
  Definition cif_mblist α Φx : loc → cif CON Σ :=
    profix (cif_mblist_gen α Φx).
  (** Unfold [cif_mblist] *)
  Lemma cif_mblist_unfold {α Φx l} :
    cif_mblist α Φx l ≡ cif_mblist_gen α Φx (cif_mblist α Φx) l.
  Proof. by rewrite /cif_mblist (profix_unfold (f:=cif_mblist_gen _ _) l). Qed.
  (** Semantics *)
  Definition mblist α Φx l : iProp Σ :=
    mutex_bor α l (Φx (l +ₗ 1) ∗ ∃ l', ▷ (l +ₗ 2) ↦ #l' ∗ cif_mblist α Φx l').
  (** Unfold semantics over [cif_ilist] *)
  Lemma sem_mblist {δ α Φx l} :
    cif_sem δ (cif_mblist α Φx l) ⊣⊢ mblist α Φx l.
  Proof. by rewrite cif_mblist_unfold !sem_ecustom /=. Qed.

  (** Iterate over [cif_mblist] *)
  Definition iter_mblist : val := rec: "self" "f" "k" "c" "l" :=
    if: !"c" ≤ #0 then #true else
      if: try_acquire_loop_mutex "k" "l" then
        "f" ("l" +ₗ #1);; let: "l'" := !("l" +ₗ #2) in release_mutex "l";;
        "c" <- !"c" - #1;; "self" "f" "k" "c" "l'"
      else #false.
  Lemma twp_iter_mblist {α Φx c l q} {f : val} {k n : nat} :
    (∀ l', [[{ ⟦ Φx (l' +ₗ 1) ⟧ }]][inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
        f #(l' +ₗ 1) [[{ RET #(); ⟦ Φx (l' +ₗ 1) ⟧ }]]) -∗
    [[{ c ↦ #n ∗ mblist α Φx l ∗ q.[α] }]]
      [inv_wsat ⟦⟧ ∗ pborrow_wsat bupd ⟦⟧]
      iter_mblist f #k #c #l
    [[{ b, RET #b; (if b then c ↦ #0 else ∃ n', c ↦ #n') ∗ q.[α] }]].
  Proof.
    iIntros "#f" (Ψ) "!> (c↦ & #m & α) →Ψ".
    iInduction n as [|m] "IH" forall (l) "m"=>/=.
    { wp_rec. wp_load. wp_pures. iApply "→Ψ". by iFrame. }
    wp_rec. wp_load. wp_pures.
    wp_apply (mutex_bor_try_acquire_loop with "[$m $α //]").
    iIntros ([|])=>/=; last first.
    { iIntros "[_ α]". wp_pure. iModIntro. iApply "→Ψ". iFrame. }
    iIntros "[b α]". wp_pures.
    iMod (nbor_tok_open (M:=bupd) with "α b") as "/=[o (Φx & %l' & >↦ & mtl)]".
    rewrite sem_mblist. iDestruct "mtl" as "#mtl". wp_apply ("f" with "Φx").
    iIntros "Φx". wp_load. wp_pures.
    iMod (nobor_tok_close (M:=bupd) with "o [Φx ↦]") as "[α b]"=>/=.
    { iFrame. by rewrite sem_mblist. }
    wp_apply (mutex_bor_release with "[$b $α //]"). iIntros "α". wp_load.
    wp_store. have -> : (S m - 1)%Z = m by lia.
    iApply ("IH" with "c↦ α →Ψ mtl").
  Qed.

  Context `{!Inv'Con CON, !IffJudg (cifO CON Σ) JUDG, !Inv'Sem JUDG CON Σ,
    !IffJsem (cifO CON Σ) Σ JUDG}.

  (** ** On derivability *)

  (** [inv'] is persistent *)
  #[export] Instance inv'_persistent `{!Deriv ih δ} {N Px} :
    Persistent (inv' δ N Px).
  Proof. exact _. Qed.

  (** Turn [inv_tok] into [inv'] *)
  Lemma inv_tok_inv' `{!Deriv ih δ} {N Px} : inv_tok N Px ⊢ inv' δ N Px.
  Proof.
    iIntros "$". iApply Deriv_factor. iIntros. rewrite sem_ejudg. iModIntro.
    iSplit; by iIntros.
  Qed.

  (** Access using [invd] *)
  Lemma invd_acc {N Px E} : ↑N ⊆ E →
    invd N Px =[inv_wsat ⟦⟧]{E,E∖↑N}=∗
      ⟦ Px ⟧ ∗ (⟦ Px ⟧ =[inv_wsat ⟦⟧]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "[%Qx[#PQ i]]". iDestruct (der_sound with "PQ") as "{PQ}PQ".
    iMod (inv_tok_acc with "i") as "[Qx cl]"; [done|]. rewrite sem_ejudg /=.
    iDestruct ("PQ" with "Qx") as "$". iIntros "!> Px". iApply "cl".
    by iApply "PQ".
  Qed.
  (** Access using [invd] via view shift *)
  Lemma invd_acc_vs {N Px E Q R} : ↑N ⊆ E →
    □ (⟦ Px ⟧ -∗ Q =[inv_wsat ⟦⟧]{E∖↑N}=∗ ⟦ Px ⟧ ∗ R) -∗
      □ (invd N Px -∗ Q =[inv_wsat ⟦⟧]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (invd_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.
  (** Access using [invd] via [twp] *)
  Lemma invd_acc_twp {N Px E Q Ψ} `{!Atomic (stuckness_to_atomicity s) e} :
    ↑N ⊆ E → to_val e = None →
    [[{ ⟦ Px ⟧ ∗ Q }]][inv_wsat ⟦⟧] e @ s; E∖↑N [[{ v, RET v; ⟦ Px ⟧ ∗ Ψ v }]]
      -∗
      [[{ invd N Px ∗ Q }]][inv_wsat ⟦⟧] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (invd_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ".
  Qed.

  (** General rule for semantic alteration *)
  Lemma inv'_iff `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    iIntros "#iff [%Rx[PR i]]". iExists Rx. iFrame "i".
    iApply Deriv_map; [|done]. iIntros (????). rewrite !sem_ejudg /=.
    iIntros "#[PR RP] !>". iSplit.
    - iIntros "Qx". iApply "PR". by iApply "iff".
    - iIntros "Rx". iApply "iff"; [done..|]. by iApply "RP".
  Qed.
  Lemma inv'_iff' `{!Deriv ih δ} {N Px Qx} :
    □ (∀ δ', ⌜Deriv ih δ'⌝ → ⌜ih δ'⌝ → ⌜dinto δ δ'⌝ →
      ⟦ Px ⟧(δ') ∗-∗ ⟦ Qx ⟧(δ')) -∗
      inv' δ N Px ∗-∗ inv' δ N Qx.
  Proof.
    iIntros "#iff". iSplit; iApply inv'_iff; [done|]. iIntros "!>" (????).
    rewrite bi.wand_iff_sym. by iApply "iff".
  Qed.

  (** Derived semantic alteration *)
  Local Lemma inv'_sep_comm' `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite bi.sep_comm.
    iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_sep_comm `{!Deriv ih δ} {N Px Qx} :
    inv' δ N (Px ∗ Qx)%cif ⊣⊢ inv' δ N (Qx ∗ Px)%cif.
  Proof. apply bi.equiv_entails. split; exact inv'_sep_comm'. Qed.
  Local Lemma inv'_inv'_sep_comm' `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv' N' (Px ∗ Qx)) ⊢ inv' δ N (cif_inv' N' (Qx ∗ Px)).
  Proof.
    iApply inv'_iff. iIntros "!> /=" (????). rewrite !sem_ecustom /=.
    rewrite inv'_sep_comm. iApply bi.wand_iff_refl.
  Qed.
  Lemma inv'_inv'_sep_comm `{!Deriv ih δ} {N N' Px Qx} :
    inv' δ N (cif_inv' N' (Px ∗ Qx)) ⊣⊢ inv' δ N (cif_inv' N' (Qx ∗ Px)).
  Proof. apply bi.equiv_entails. split; exact inv'_inv'_sep_comm'. Qed.
  Local Lemma inv'_bor_lft' `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) -∗ inv' δ N (cif_bor β Px).
  Proof.
    iIntros "#? #?". iApply inv'_iff. iIntros "!>" (????).
    rewrite /= !sem_ecustom /=. iSplit; by iApply nbor_tok_lft.
  Qed.
  Lemma inv'_bor_lft `{!Deriv ih δ} {N α β Px} :
    α ⊑□ β -∗ β ⊑□ α -∗ inv' δ N (cif_bor α Px) ∗-∗ inv' δ N (cif_bor β Px).
  Proof. iIntros "#? #?". iSplit; by iApply inv'_bor_lft'. Qed.
End verify.
