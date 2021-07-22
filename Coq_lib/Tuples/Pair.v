(** * The homogeneous pair type constructor *)

Require Import Spreadable.
Require Import Tuple.

(** ** The Pair type constructor *)
Definition Pair (A : Type) : Type := Tuple 1 A.

(** ** Pair is spreadable because tuples are spreadable *)
Definition pair_spreadable : Spreadable Pair := tuple_spreadable 1.

Definition pair_map     := map     _ pair_spreadable.
Definition pair_cng_map := map     _ pair_spreadable.
Definition pair_cmp_map := map     _ pair_spreadable.
Definition pair_foldr   := foldr   _ pair_spreadable.
Definition pair_foldl   := foldl   _ pair_spreadable.
Definition pair_any     := any     _ pair_spreadable.
Definition pair_dec_any := decAny  _ pair_spreadable.
Definition pair_all     := all     _ pair_spreadable.
Definition pair_dec_all := decAll  _ pair_spreadable.
Definition pair_dec_eq  := decEq   _ pair_spreadable.
Definition pair_size    := size    _ pair_spreadable.
Definition pair_in_prop := in_prop _ pair_spreadable.

Eval compute in (foldr _ pair_spreadable).

(** ** The size of a pair will always be 2 *)
Definition size_pair {A : Type}  : Pair A -> nat :=
(foldr _ pair_spreadable) A _ (fun x => fun _ => x + 1) 0.

Lemma size_pair_is_2 : forall A (p : Pair A), size_pair p = 2.
Proof. auto. Qed.

Lemma size_is_2 : forall A (p : Pair A), pair_size _ p = 2.
Proof. auto. Qed.

