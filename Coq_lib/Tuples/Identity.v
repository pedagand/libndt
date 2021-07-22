(** * The Identity type constructor *)
Require Import Spreadable.
Require Import Tuple.

(** ** The Identity type constructor *)
Definition Id (A : Type) : Type := Tuple 0 A.

(** ** Identity is spreadable because tuples are spreadable *)
Definition id_spreadable : Spreadable Id := tuple_spreadable 0.

Definition id_map     := map     _ id_spreadable.
Definition id_cng_map := map     _ id_spreadable.
Definition id_cmp_map := map     _ id_spreadable.
Definition id_foldr   := foldr   _ id_spreadable.
Definition id_foldl   := foldl   _ id_spreadable.
Definition id_any     := any     _ id_spreadable.
Definition id_dec_any := decAny  _ id_spreadable.
Definition id_all     := all     _ id_spreadable.
Definition id_dec_all := decAll  _ id_spreadable.
Definition id_dec_eq  := decEq   _ id_spreadable.
Definition id_size    := size    _ id_spreadable.
Definition id_in_prop := in_prop _ id_spreadable.

(** ** The size of an Identity will always be 1 *)
Lemma size_is_1 : forall A (p : Id A), id_size _ p = 1.
Proof. auto. Qed.
