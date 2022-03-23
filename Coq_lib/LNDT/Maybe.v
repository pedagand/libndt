(** * Maybe seen as an instance of LNDT *)

Require Import LNDT.
Require Import Spreadable.
Require Import Null.
Require Import Lia.

Definition Maybe : TT := LNDT Null.

(** ** Patterns to match the usual notations of the inhabitants of Maybe *)
Definition nothing F A : LNDT F A := LNDT.empty F A.
Definition just  F A x : LNDT F A := nest _ _ x (LNDT.empty _ _).

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

(** ** Maybe is spread-able because Null and LNDT are spread-able. *)

Definition maybe_spreadable : SpreadAble Maybe := lndt_spreadable null_spreadable.

Definition maybe_map         := map         _ (map_able _ maybe_spreadable).
Definition maybe_cng_map     := map_congru  _ (map_able _ maybe_spreadable).
Definition maybe_cmp_map     := map_compo   _ (map_able _ maybe_spreadable).
Definition maybe_foldr       := foldr       _ (fold_able _ maybe_spreadable).
Definition maybe_foldl       := foldl       _ (fold_able _ maybe_spreadable).
Definition maybe_size        := size        _ (fold_able _ maybe_spreadable).
Definition maybe_flatten     := flatten     _ (fold_able _ maybe_spreadable).
(* Definition maybe_show        := show        _ (fold_able _ maybe_spreadable). *)
Definition maybe_any         := any         _ (any_all_able _ maybe_spreadable).
Definition maybe_dec_any     := dec_any     _ (any_all_able _ maybe_spreadable).
Definition maybe_all         := all         _ (any_all_able _ maybe_spreadable).
Definition maybe_dec_all     := dec_all     _ (any_all_able _ maybe_spreadable).
Definition maybe_in_prop     := in_prop     _ (any_all_able _ maybe_spreadable).
Definition maybe_empty       := empty       _ (any_all_able _ maybe_spreadable).
Definition maybe_dec_in_prop := dec_in_prop _ (any_all_able _ maybe_spreadable).
Definition maybe_dec_eq      := dec_eq      _ (eq_able _ maybe_spreadable).

(** ** Example of inhabitants of Maybe ℕ *)
Definition example1 : Maybe nat := just _ _ 10.
Definition example2 : Maybe nat := nothing _ _.

(** ** Examples of function calls over these examples *)
Definition example1Map : Maybe nat :=
  maybe_map _ _ (fun x => x + 3) example1.

Definition example1Foldr : nat :=
  maybe_foldr _ _ (fun x y => x + y) 0 example1.

Definition example1Foldl : nat :=
  maybe_foldl _ _ (fun x y => x + y) 0 example1.

Definition example1Size : nat := maybe_size _ example1.

Eval compute in example1Size.
(* = 1 : nat *)

Definition example2Map : Maybe nat :=
  maybe_map _ _ (fun x => x + 3) example2.

Eval compute in example2Map.

Definition example2Foldr : nat :=
  maybe_foldr _ _ (fun x y => x + y) 0 example2.

Definition example2Foldl : nat :=
  maybe_foldl _ _ (fun x y => x + y) 0 example2.

Definition example2Size : nat := maybe_size _ example2.

Eval compute in example2Size.
(* = 0 : nat *)

(** ** Examples of predications over these examples *)

Lemma example1Any : maybe_any _ (fun x => x > 3) example1.
Proof. unfold maybe_any. simpl. lia. Defined.

Lemma example1All : maybe_all _ (fun x => x < 12) example1.
Proof. unfold maybe_all. simpl. lia. Defined.

Lemma example2Any : forall (P : nat -> Prop), ~ maybe_any _ P example2.
Proof. unfold example2. intros P Hmaybe. contradiction. Defined.

Lemma example2All : forall (P : nat -> Prop), maybe_all _ P example2.
Proof. unfold example2, maybe_all. intro P.  simpl. auto. Defined.