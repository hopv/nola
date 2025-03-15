(** * Binary trees *)

From nola Require Export prelude.

(** [bin A] : Binary tree of the element type [A] *)
Inductive bin A := BinLeaf | BinNode (a : A) (tl tr : bin A).
Arguments BinLeaf {_}. Arguments BinNode {_} _ _ _.

(** [bin] is inhabited *)
#[export] Instance bin_inhabited {A} : Inhabited (bin A) := populate BinLeaf.

(** Size of [bin] *)
Fixpoint bin_size {A} (t : bin A) : nat :=
  match t with BinLeaf => 0 |
    BinNode a tl tr => S (bin_size tl + bin_size tr) end.

(** Left spine of [bin] *)
Fixpoint bin_lspine {A} (t : bin A) : list A :=
  match t with BinLeaf => [] | BinNode a tl _ => a :: bin_lspine tl end.
(** Right spine of [bin] *)
Fixpoint bin_rspine {A} (t : bin A) : list A :=
  match t with BinLeaf => [] | BinNode a _ tr => a :: bin_rspine tr end.

(** [fmap] over [bin] *)
#[export] Instance bin_fmap : FMap bin := λ A B f,
  fix go (t : bin A) := match t with
    BinLeaf => BinLeaf | BinNode a tl tr => BinNode (f a) (go tl) (go tr) end.

(** [bin_size] over [fmap] *)
Lemma bin_size_fmap {A B f t} : @bin_size B (f <$> t) = @bin_size A t.
Proof. by elim t=>//= _ ? -> ? ->. Qed.

(** [bin_lspine] over [fmap] *)
Lemma bin_lspine_fmap {A B f t} :
  @bin_lspine B (f <$> t) = f <$> @bin_lspine A t.
Proof. by elim t=>//= ?? ->. Qed.
(** [bin_rspine] over [fmap] *)
Lemma bin_rspine_fmap {A B f t} :
  @bin_rspine B (f <$> t) = f <$> @bin_rspine A t.
Proof. by elim t=>//= ?? _ ? ->. Qed.

(** Universal quantification over [bin] *)
Inductive ForallBin {A} (Φ : A → Prop) : bin A → Prop :=
| ForallBin_leaf : ForallBin Φ BinLeaf
| ForallBin_node {a tl tr} :
    Φ a → ForallBin Φ tl → ForallBin Φ tr → ForallBin Φ (BinNode a tl tr).
