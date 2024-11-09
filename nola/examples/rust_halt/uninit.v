(** * Uninitialized data type *)

From nola.examples.rust_halt Require Export type.

Section uninit.
  Context `{!rust_haltGS CON Σ, !rust_haltC CON, !Csem CON JUDG Σ,
    !Jsem JUDG (iProp Σ), !rust_haltJ CON JUDG Σ, !rust_haltCS CON JUDG Σ}.

  (** ** [ty_uninit]: Universal type *)
  Definition pty_uninit sz : pty CON Σ unitₓ :=
    pair sz (λ _ vl, ⌜length vl = sz⌝%cif).
  Definition ty_uninit sz : ty CON Σ unitₓ := ty_pty (pty_uninit sz).
  (** [pty_uninit] satisfies [Pty] *)
  #[export] Instance pty_uninit_pty {sz} : Pty (pty_uninit sz).
  Proof. split=>//= *. exact _. Qed.
End uninit.
