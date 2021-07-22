(** * The List data type as an instance of a nested data type *)

Require Import Spreadable.
Require Import Identity.
Require Import LNDT.
Require Import Lia.

Open Scope list_scope.

(** ** The List nested datatype *)
Definition List : Type -> Type := Nested Id.

(** ** List is regular because the Identity is regular *)
Definition listRegular : Regular List := nestedRegular _ idRegular.

Definition listMap     := map     _ listRegular.
Definition listCngMap  := cngMap  _ listRegular.
Definition listCmpMap  := cmpMap  _ listRegular.
Definition listFoldr   := foldr   _ listRegular.
Definition listFoldl   := foldl   _ listRegular.
Definition listAny     := any     _ listRegular.
Definition listDecAny  := decAny  _ listRegular.
Definition listAll     := all     _ listRegular.
Definition listDecAll  := decAll  _ listRegular.
Definition listDecEq   := decEq   _ listRegular.
Definition listSize    := size    _ listRegular.
Definition listIn_prop := in_prop _ listRegular.

(** ** Example of inhabitant of List nat *)
Definition example : List nat :=
  nest _ _ 3 (nest _ _ 5
    (nest _ _ 12 (nest _ _ 3 (nest _ _ 5
       (nest _ _ 12 (empty Id nat)))))).
(* equivalent to 3 :: 5 :: 12 :: 3 :: 5 :: 12 :: nil *)

(** ** Examples of function calls over this example *)
Definition exampleMap : List nat :=
  listMap _ _ (fun x => x + 3) example.
Eval compute in exampleMap.

Definition exampleFoldr : nat :=
  listFoldr _ _ (fun x y => x + y) 0 example.
Eval compute in exampleFoldr.
(* = 40 : nat *)

Definition exampleFoldl : nat :=
  listFoldl _ _ (fun x y => x + y) 0 example.
Eval compute in exampleFoldl.
(* = 40 : nat *)

Definition exampleSize : nat := listSize _ example.
Eval compute in exampleSize.
(* = 6 : nat *)

(** ** Examples of predications over these examples *)
Lemma exampleAny : listAny _ (fun x => x = 12) example.
Proof. unfold example, listAny. simpl. tauto. Defined.

Lemma exampleAll : listAll _ (fun x => x <= 12) example.
Proof. unfold example, listAll. simpl. lia. Defined.
