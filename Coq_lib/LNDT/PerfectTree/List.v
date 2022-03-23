(** * List as an instance of LNDT *)

Require Import Spreadable.
Require Import PerfectTree.
Require Import LNDT.
Require Import Tuple.
Require Import Lia.

Open Scope list_scope.

Definition List : TT := PerfectTree 0.

(** ** List is spread-able because PerfectTree is spread-able *)
Definition list_spreadable : SpreadAble (List) := pt_spreadable 0.

Definition list_map         := pt_map         0.
Definition list_cng_map     := pt_cng_map     0.
Definition list_cmp_map     := pt_cmp_map     0.
Definition list_foldr       := pt_foldr       0.
Definition list_foldl       := pt_foldl       0.
Definition list_size        := pt_size        0.
Definition list_flatten     := pt_flatten     0.
(* Definition list_any     := pt_show        0. *)
Definition list_any         := pt_any         0.
Definition list_dec_any     := pt_dec_any     0.
Definition list_all         := pt_all         0.
Definition list_dec_all     := pt_dec_all     0.
Definition list_in_prop     := pt_in_prop     0.
Definition list_empty       := pt_empty       0.
Definition list_dec_in_prop := pt_dec_in_prop 0.
Definition list_dec_eq      := pt_dec_eq      0.

(** ** Example of inhabitant of List nat *)
Definition example : List nat :=
  nest _ _ 3 (nest _ _ 5
    (nest _ _ 12 (nest _ _ 3 (nest _ _ 5
       (nest _ _ 12 (empty id nat)))))).
(* equivalent to 3 :: 5 :: 12 :: 3 :: 5 :: 12 :: nil *)

(** ** Examples of function calls over this example *)
Definition exampleMap : List nat :=
  list_map _ _ (fun x => x + 3) example.
Eval compute in exampleMap.

Definition exampleFoldr : nat :=
  list_foldr _ _ (fun x y => x + y) 0 example.
Eval compute in exampleFoldr.
(* = 40 : nat *)

Definition exampleFoldl : nat :=
  list_foldl _ _ (fun x y => x + y) 0 example.
Eval compute in exampleFoldl.
(* = 40 : nat *)

Definition exampleSize : nat := list_size _ example.
Eval compute in exampleSize.
(* = 6 : nat *)

(** ** Examples of predications over these examples *)
Lemma exampleAny : list_any _ (fun x => x = 12) example.
Proof. unfold example, list_any, pt_any. simpl. tauto. Defined.

Lemma exampleAll : list_all _ (fun x => x <= 12) example.
Proof. unfold example, list_all, pt_all. simpl. lia. Defined.