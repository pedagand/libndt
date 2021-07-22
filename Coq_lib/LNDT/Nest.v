(** * The Nest data type as an instance of a nested data type *)

Require Import Spreadable.
Require Import Pair.
Require Import LNDT.

(** ** The "Nest" nested datatype *)
Definition Nest : Type -> Type := Nested Pair.

(** ** Nest is regular because Pair is regular *)
Definition nestRegular : Regular Nest := nestedRegular _ pairRegular.

Definition nestMap     := map     _ nestRegular.
Definition nestCngMap  := cngMap  _ nestRegular.
Definition nestCmpMap  := cmpMap  _ nestRegular.
Definition nestFoldr   := foldr   _ nestRegular.
Definition nestFoldl   := foldl   _ nestRegular.
Definition nestAny     := any     _  nestRegular.
Definition nestDecAny  := decAny  _ nestRegular.
Definition nestAll     := all     _ nestRegular.
Definition nestDecAll  := decAll  _ nestRegular.
Definition nestDecEq   := decEq   _ nestRegular.
Definition nestSize    := size    _ nestRegular.
Definition nestIn_prop := in_prop _ nestRegular.

(** ** Example of inhabitant of Nest nat *)
Definition example : Nest nat :=
  nest _ _ 7 (nest _ _ (1, 2)
    (nest _ _ ((6, 7), 7, 4)
       (nest _ _ (((2, 5), 7, 1), (3, 8), (9, 3)) (empty _ _)))).
(* equivalent to
    7 ∷ (1 , 2) ∷ ((6 , 7) , 7 , 4)
       ∷ ((2 , 5) , 7 , 1) , (3 , 8) , (9 , 3) ∷ [] *)

(** ** Examples of function calls over this example *)

Definition exampleMap : Nest nat :=
  nestMap _ (fun x => x + 3) example.

Definition exampleFoldr : nat :=
  nestFoldr _ (fun x y => x + y) 0 example.

Definition exampleFoldl : nat :=
  nestFoldl _ (fun x y => x + y) 0 example.

Definition exampleSize : nat := nestSize example.

Eval compute in exampleSize.

(** ** Examples of predications over these examples *)

Lemma exampleAny : nestAny _ (fun x => x > 8) example.
Proof. Defined.

Lemma exampleAll : nestAll _ (fun x => X >= 1) example.
Proof. Defined.
