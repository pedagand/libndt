(** * Nest as an instance of LNDT *)

Require Import Spreadable.
Require Import LNDT.
Require Import PerfectTree.
Require Import Lia.

Definition Nest : TT := PerfectTree 1.

(** ** Nest is spread-able because PerfectTree is spread-able *)
Definition nest_spreadable : SpreadAble (Nest) := pt_spreadable 1.

Definition nest_map         := pt_map         1.
Definition nest_cng_map     := pt_cng_map     1.
Definition nest_cmp_map     := pt_cmp_map     1.
Definition nest_foldr       := pt_foldr       1.
Definition nest_foldl       := pt_foldl       1.
Definition nest_size        := pt_size        1.
Definition nest_flatten     := pt_flatten     1.
(* Definition nest_any     := pt_show        1. *)
Definition nest_any         := pt_any         1.
Definition nest_dec_any     := pt_dec_any     1.
Definition nest_all         := pt_all         1.
Definition nest_dec_all     := pt_dec_all     1.
Definition nest_in_prop     := pt_in_prop     1.
Definition nest_empty       := pt_empty       1.
Definition nest_dec_in_prop := pt_dec_in_prop 1.
Definition nest_dec_eq      := pt_dec_eq      1.

Require Import Tuple.

(** ** Example of inhabitant of Nest nat *)

Definition example : Nest nat :=
  nest _ _ 7 
   (nest _ _ (1, 2)
     (nest _ _ ((6, 7), (7, 4))
       (nest _ _ (((2, 5), (7, 1)), ((3, 8), (9, 3)))
         (empty _ _)))).
(* equivalent to
    7 ∷ (1 , 2) ∷ ((6 , 7) , (7 , 4))
       ∷ (((2 , 5) , (7 , 1)) , ((3 , 8) , (9 , 3))) ∷ [] *)

(** ** Examples of function calls over this example *)

Definition exampleMap : Nest nat :=
  nest_map _ _ (fun x => x + 3) example.

Eval compute in exampleMap.

Definition exampleFoldr : nat :=
  nest_foldr _ _ (fun x y => x + y) 0 example.

Eval compute in exampleFoldr.

Definition exampleFoldl : nat :=
  nest_foldl _ _ (fun x y => x + y) 0 example.

Eval compute in exampleFoldl.

Definition exampleSize : nat := nest_size _ example.

Eval compute in exampleSize.

(** ** Examples of predications over these examples *)

Lemma exampleAny : nest_any _ (fun x => x > 8) example.
Proof. unfold nest_any, example, pt_any. simpl. lia. Defined.

Lemma exampleAll : nest_all _ (fun x => x >= 1) example.
Proof. unfold nest_all, example, pt_all. simpl. repeat split;lia. Defined.