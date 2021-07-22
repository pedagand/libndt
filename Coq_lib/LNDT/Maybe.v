(** * The Maybe data type as an instance of a nested data type *)

Require Import LNDT.
Require Import Spreadable.
Require Import Null.
Require Import Lia.

(** ** The Maybe datatype can be constructed as a specific nested type *)
Definition Maybe : Type -> Type := Nested Null.

(** ** Patterns to match the usual notations of the inhabitants of Maybe *)
Definition nothing F A : Nested F A := empty F A.
Definition just  F A x : Nested F A := nest _ _ x (empty _ _).

(** ** A proof that nothing and (just x) are the only two
       possible inhabitants of Maybe *)
Lemma complete : forall (A : Type) (x : Maybe A),
    x = nothing _ _ \/ exists y, x = just _ _ y.
Proof.
intros A x.
induction x.
 + unfold nothing. tauto.
 + unfold just.
   destruct IHx;right.
    - rewrite H. exists a. reflexivity.
    - destruct H. contradiction.
Defined.

(** ** Maybe is regular because Null and Nested are regular. *)

Definition maybeRegular : Regular Maybe := nestedRegular _ nullRegular.

Definition maybeMap     := map     _ maybeRegular.
Definition maybeCngMap  := cngMap  _ maybeRegular.
Definition maybeCmpMap  := cmpMap  _ maybeRegular.
Definition maybeFoldr   := foldr   _ maybeRegular.
Definition maybeFoldl   := foldl   _ maybeRegular.
Definition maybeAny     := any     _ maybeRegular.
Definition maybeDecAny  := decAny  _ maybeRegular.
Definition maybeAll     := all     _ maybeRegular.
Definition maybeDecAll  := decAll  _ maybeRegular.
Definition maybeDecEq   := decEq   _ maybeRegular.
Definition maybeSize    := size    _ maybeRegular.
Definition maybeIn_prop := in_prop _ maybeRegular.

(** ** Example of inhabitants of Maybe ℕ *)
Definition example1 : Maybe nat := just _ _ 10.
Definition example2 : Maybe nat := nothing _ _.

(** ** Examples of function calls over these examples *)
Definition example1Map : Maybe nat :=
  maybeMap _ _ (fun x => x + 3) example1.

Definition example1Foldr : nat :=
  maybeFoldr _ _ (fun x y => x + y) 0 example1.

Definition example1Foldl : nat :=
  maybeFoldl _ _ (fun x y => x + y) 0 example1.

Definition example1Size : nat := maybeSize _ example1.

Eval compute in example1Size.
(* = 1 : nat *)

Definition example2Map : Maybe nat :=
  maybeMap _ _ (fun x => x + 3) example2.

Eval compute in example2Map.

Definition example2Foldr : nat :=
  maybeFoldr _ _ (fun x y => x + y) 0 example2.

Definition example2Foldl : nat :=
  maybeFoldl _ _ (fun x y => x + y) 0 example2.

Definition example2Size : nat := maybeSize _ example2.

Eval compute in example2Size.
(* = 0 : nat *)

(** ** Examples of predications over these examples *)

Lemma example1Any : maybeAny _ (fun x => x > 3) example1.
Proof. unfold maybeAny. simpl. lia. Defined.

Lemma example1All : maybeAll _ (fun x => x < 12) example1.
Proof. unfold maybeAll. simpl. lia. Defined.

Lemma example2Any : forall (P : nat -> Prop), ~ maybeAny _ P example2.
Proof. unfold example2. intros P Hmaybe. contradiction. Defined.

Lemma example2All : forall (P : nat -> Prop), maybeAll _ P example2.
Proof. unfold example2, maybeAll. intro P.  simpl. auto. Defined.
