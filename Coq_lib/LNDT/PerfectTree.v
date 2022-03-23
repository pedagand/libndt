(** * The family of type constructors for n-ary perfectly balanced trees *)

Require Import LNDT.
Require Import Spreadable.
Require Import Tuple.
Require Import Lia.

Definition PerfectTree n : TT := LNDT (Tuple n).

Definition pt_spreadable n : SpreadAble (PerfectTree n) := 
  lndt_spreadable (tuple_spreadable n).

Definition pt_map         n := map         _ (map_able _ (pt_spreadable n)).
Definition pt_cng_map     n := map_congru  _ (map_able _ (pt_spreadable n)).
Definition pt_cmp_map     n := map_compo   _ (map_able _ (pt_spreadable n)).
Definition pt_foldr       n := foldr       _ (fold_able _ (pt_spreadable n)).
Definition pt_foldl       n := foldl       _ (fold_able _ (pt_spreadable n)).
Definition pt_size        n := size        _ (fold_able _ (pt_spreadable n)).
Definition pt_flatten     n := flatten     _ (fold_able _ (pt_spreadable n)).
(* Definition pt_show       n := show        _ (fold_able _ (pt_spreadable n)). *)
Definition pt_any         n := any         _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_any     n := dec_any     _ (any_all_able _ (pt_spreadable n)).
Definition pt_all         n := all         _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_all     n := dec_all     _ (any_all_able _ (pt_spreadable n)).
Definition pt_in_prop     n := in_prop     _ (any_all_able _ (pt_spreadable n)).
Definition pt_empty       n := empty       _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_in_prop n := dec_in_prop _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_eq      n := dec_eq      _ (eq_able _ (pt_spreadable n)).