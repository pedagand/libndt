(** * Bush *)

Require Import LNDT.
Require Import Spreadable.

(* DOESN'T WORK

Definition Bush : TT := LNDT Bush.
Fixpoint Bush : TT := LNDT Bush.

Definition bush_spreadable : SpreadAble Bush := 
  lndt_spreadable bush_spreadable.

Definition bush_map         n := map         _ (map_able _ bush_spreadable).
Definition bush_cng_map     n := map_congru  _ (map_able _ bush_spreadable).
Definition bush_cmp_map     n := map_compo   _ (map_able _ bush_spreadable).
Definition bush_foldr       n := foldr       _ (fold_able _ bush_spreadable).
Definition bush_foldl       n := foldl       _ (fold_able _ bush_spreadable).
Definition bush_size        n := size        _ (fold_able _ bush_spreadable).
Definition bush_flatten     n := flatten     _ (fold_able _ bush_spreadable).
Definition bush_show        n := show        _ (fold_able _ bush_spreadable).
Definition bush_any         n := any         _ (any_all_able _ bush_spreadable).
Definition bush_dec_any     n := dec_any     _ (any_all_able _ bush_spreadable).
Definition bush_all         n := all         _ (any_all_able _ bush_spreadable).
Definition bush_dec_all     n := dec_all     _ (any_all_able _ bush_spreadable).
Definition bush_in_prop     n := in_prop     _ (any_all_able _ bush_spreadable).
Definition bush_empty       n := empty       _ (any_all_able _ bush_spreadable).
Definition bush_dec_in_prop n := dec_in_prop _ (any_all_able _ bush_spreadable).
Definition bush_dec_eq      n := dec_eq      _ (eq_able _ bush_spreadable). *)