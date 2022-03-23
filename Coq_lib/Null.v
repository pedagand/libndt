(** * The Null type constructor *)

Require Import Spreadable.

(** ** A leveled empty type *)
Inductive False : Prop := . (* Already in the Standard Library *)

(** ** The Null type constructor *)
Definition Null : TT := fun _ => False.

(** ** Null is spread-able *)
Definition SnullMap : Map Null := fun A B _ (H :False) => H.

Lemma SnullCngMap : MapCongruence SnullMap.
Proof. unfold MapCongruence. reflexivity. Defined.

Print SnullCngMap.

Lemma SnullCmpMap : MapComposition SnullMap.
Proof. unfold MapComposition, SnullMap. tauto. Defined.

Print SnullCmpMap.

Lemma SnullFold : Fold Null.
Proof. unfold Fold. tauto. Defined.

Print SnullFold.

Lemma SnullAny : TransPred Null.
Proof. unfold TransPred, Null. tauto. Defined.

Print SnullAny.

Lemma SnullDecAny : TransDec SnullAny.
Proof. unfold TransDec, Null, SnullAny, Dec. tauto. Defined.

Print SnullDecAny.

Lemma SnullDecEq : DecEq Null.
Proof. unfold DecEq, Null, Decidable. tauto. Defined.

Print SnullDecEq.

Definition SnullIn  
:= fun A x => SnullAny A (fun y => x = y ) .

Lemma SnullIn_map : forall (A B : Type) (f : A -> B) l (x : A),
SnullIn _ x l -> SnullIn _ (f x) (SnullMap _ _ f l).
Proof.  simpl; compute; intros.  tauto. Defined.

Definition null_spreadable : SpreadAble Null :=
  mkSpread Null
    (mkFold Null SnullFold SnullFold)
    (mkMap Null SnullMap SnullCngMap SnullCmpMap)
    (mkAnyAll Null SnullAny SnullDecAny
              SnullAny SnullDecAny)
    (mkEq Null SnullDecEq). (* SnullIn_map. *)

Definition null_map         := map        _ (map_able _ null_spreadable).
Definition null_cng_map     := map_congru _ (map_able _ null_spreadable).
Definition null_cmp_map     := map_compo  _ (map_able _ null_spreadable).
Definition null_foldr       := foldr      _ (fold_able _ null_spreadable).
Definition null_foldl       := foldl      _ (fold_able _ null_spreadable).
(** ** A size of Null can be defined, but can never be called
       However, it is useful in the definition of Maybe *)
Definition null_size        := size        _ (fold_able _ null_spreadable).
Definition null_flatten     := flatten     _ (fold_able _ null_spreadable).
(* Definition null_show        := show        _ (fold_able _ null_spreadable). *)
Definition null_any         := any         _ (any_all_able _ null_spreadable).
Definition null_dec_any     := dec_any     _ (any_all_able _ null_spreadable).
Definition null_all         := all         _ (any_all_able _ null_spreadable).
Definition null_dec_all     := dec_all     _ (any_all_able _ null_spreadable).
Definition null_in_prop     := in_prop     _ (any_all_able _ null_spreadable).
Definition null_empty       := empty       _ (any_all_able _ null_spreadable).
Definition null_dec_in_prop := dec_in_prop _ (any_all_able _ null_spreadable).
Definition null_dec_eq      := dec_eq      _ (eq_able _ null_spreadable).