Require Import Spreadable.
Require Import Tuple.
Require Import Lia.

Open Scope list_scope.

(** * The specification for nested data types **)
Inductive LNDT (F : TT) (A : Type) : Type :=
 | empty : LNDT F A
 | nest : A -> LNDT F (F A) -> LNDT F A.

(** * Some examples *)

Eval compute in (LNDT list).

Lemma ex1 : LNDT list nat.
apply (nest list nat 1).
apply (nest list (list nat) (cons 1 (cons 2 (cons 3 nil)))).
constructor.
Defined.

Definition nested1 : LNDT list nat :=
nest list nat 1
  (nest list (list nat)
     (1 :: 2 :: 3 :: nil)
     (empty list
        (list (list nat)))).
(* Proof. 
apply (nest list nat 1).
apply 
  (nest list (list nat)
     (1 :: 2 :: 3 :: nil)).
constructor.
Defined.
*)


Definition nested2 : LNDT list nat.
Proof. 
apply (nest list nat 1).
apply 
  (nest list (list nat)
     (1 :: 2 :: 3 :: nil)).
apply (nest list (list (list nat))
     ((1::2::nil)::(2::nil) :: nil)).
apply empty.
Defined.
(*
nest list nat 1
  (nesOpen Scope list_scope.t list (list nat)
     (1 :: 2 :: 3 :: nil)
     (nest list
        (list (list nat))
        ((1 :: 2 :: nil)
         :: (2 :: nil)
            :: nil)
        (empty list
           (list
              (list
                 (list nat))))))
                 
ou plus lisiblement sans les infos de type
(nest 1
  (nest [1 ; 2; 3]
    (nest [[1;2] ; [2]]
      empty)))
*)
   
      
Definition nested3 : LNDT (Tuple 2) nat.
Proof.
apply (nest (Tuple 2) nat
      1).
apply 
  (nest (Tuple 2) (Tuple 2 nat)
     (1, (2, 3))).
apply (nest (Tuple 2) (Tuple 2 (Tuple 2 nat))
     ( (1, (1, 1)), ( (2, (2, 2)), (3, (3, 3))))).
apply empty.
Defined.

Print nested3.

(** * Induction principle over nested data types *)
Check LNDT_ind.

(** * A very simple property on equality *)
Lemma eq_nest : forall {F : TT} {A : Type} {x y} {l m : LNDT F (F A)},
    x = y -> l = m -> (nest F A x l) = (nest F A y m).
Proof.
  intros F A x y l m Heq_A Heq_Nested.
  rewrite Heq_A, Heq_Nested. reflexivity.
Defined.

(** * Regularity of a type constructor F can be propagated to (Nested F) *)

(** ** Map function *)
Fixpoint lndt_map {F : TT} (map : Map F) A B (f : A -> B) (t : LNDT F A) :=
match t with
 |empty _ _     => empty _ _
 |nest  _ _ x e => nest F B (f x) (lndt_map map _ _ (map _ _ f) e)
end.

Definition ff (n : nat) := match n with
  0 => false
| _ => true
end.
(* @TODO mv
Eval compute in (nestedMap list maplist nat bool ff nested1).
*)
(** ** Congruence function *)
Require Import FunctionalExtensionality.

Lemma lndt_cng_map : forall {F : TT} {map : Map F}
  (cgMap : MapCongruence map), MapCongruence (lndt_map map).
Proof.
  unfold MapCongruence, Map. intros F map Hmap A B f g x Heq.
  extensionality in Heq. rewrite Heq. reflexivity.
Defined.

(** ** Composition function *)
Lemma lndt_cmp_map : forall {F : TT} {map : Map F} (cgMap : MapCongruence map)
  (cpMap : MapComposition map), MapComposition (lndt_map map).
Proof.
  unfold MapComposition, MapCongruence. intros F map Hyp1 Hyp2 A B C f g x.
  induction x.
   + reflexivity.
   + simpl in *. specialize (Hyp2 A B C f g). (* rewrite Hyp2. rewrite Hyp1.
  intros F map A B C f g x.
induction x.
 + reflexivity.
 + simpl in *. unfold Map in map.
*)
Admitted.

Definition lndt_mapable {F : TT} (mp : MapAble F) : MapAble (LNDT F) :=
  mkMap (LNDT F)
        (lndt_map (map F mp))
        (lndt_cng_map (map_congru F mp))
        (lndt_cmp_map (map_congru F mp) (map_compo F mp)).

(** ** Fold functions *)
Fixpoint lndt_foldr (F : TT) (foldr : Fold F) A B (f : B -> A -> B) (b0 : B) (t : LNDT F A) :=
match t with
 |empty _ _ => b0
 |nest _ _ x v  => f (lndt_foldr _ foldr _ _ (foldr _ _ f) b0 v) x
end.

Definition foldlist  : Fold list  := fun A B f b l => @List.fold_left B A f l b.

Eval compute in (lndt_foldr _ foldlist nat nat Nat.add 0 nested1).
(* = 7 : nat *)

Eval compute in (lndt_foldr _ foldlist nat nat Nat.add 0 nested2).
(* = 12 : nat *)

Eval compute in (lndt_foldr _ (tuple_foldr 2) nat nat Nat.add 0 nested3).
(* = 25 : nat *)

Definition lndt_sum F (foldr : Fold F) (t : LNDT F nat) :=
lndt_foldr _ foldr nat nat Nat.add 0 t.

Eval compute in (lndt_sum (Tuple 2) (tuple_foldr 2) nested3).
(* = 25 : nat *)

Fixpoint lndt_foldl {F : TT} (foldl : Fold F) A B (f : B -> A -> B) (b0 : B) (t : LNDT F A) :=
match t with
 |empty _ _     => b0
 |nest  _ _ x e => lndt_foldl foldl _ _ (foldl _ _ f) (f b0 x) e
end.

Definition lndt_foldable {F : TT} (fp : FoldAble F) : FoldAble (LNDT F) :=
  mkFold (LNDT F)
        (lndt_foldl (foldl F fp))
        (lndt_foldr F (foldr F fp)).

(** ** Size function *)
Definition lndt_size F fold A := lndt_foldr F fold A nat (fun x => fun y => S x) 0.

Eval compute in (lndt_size list foldlist nat nested2).
(* = 7 : nat *)

Eval compute in (lndt_size (Tuple 2) (tuple_foldr 2) nat nested3).
(* = 13 : nat *)

(** ** Any predicate transformer *)
Fixpoint lndt_any {F : TT} (T : TransPred F) A (P : A -> Prop) (t : LNDT F A) :=
match t with
 |empty _ _ => False
 |nest _ _ x e  => (P x) \/ (lndt_any T _ (T _ P) e)
end.

Lemma lndt_any_ex1 : lndt_any (tuple_any 2) nat (fun x => x > 2) nested3.
Proof. compute. lia. Qed.

Lemma lndt_any_ex2 : not(lndt_any (tuple_any 2) nat (fun x => x > 3) nested3).
Proof. compute. lia. Qed.

Lemma lndt_dec_any : forall {F : TT} (T : TransPred F),
    TransDec T -> TransDec (lndt_any T).
Proof.
unfold TransDec, Dec, TransPred. intros F T Hyp A P HdecA x.
induction x.
  + intuition.
  + simpl. specialize (Hyp A P).
    specialize (IHx (T A P) (Hyp HdecA)). destruct IHx.
     { tauto. }
     { destruct (HdecA a).
        - tauto.
        - right. intro Hfalse. destruct Hfalse; contradiction. }
Defined.

(** ** All predicate transformer *)
Fixpoint lndt_all {F : TT} (T : TransPred F) A (P : A -> Prop) (t : LNDT F A) :=
match t with
 |empty _ _ => True
 |nest _ _ x e  => (P x) /\ (lndt_all T _ (T _ P) e)
end.

Lemma lndt_all_ex1:
 not(lndt_all (tuple_all 2) nat (fun x => x > 2) nested3).
Proof. compute. lia. Qed.

Lemma lndt_all_ex2:
 lndt_any (tuple_any 2) nat (fun x => x < 4) nested3.
Proof. compute. lia. Qed.

Lemma lndt_dec_all : forall {F : TT} (T : TransPred F),
    TransDec T -> TransDec (lndt_all T).
Proof.
unfold TransDec, Dec, TransPred. intros F T Hyp A P HdecA x.
induction x.
  + simpl. tauto.
  + simpl. specialize (Hyp A P).
    specialize (IHx (T A P) (Hyp HdecA)). destruct IHx.
     { destruct (HdecA a).
        - tauto.
        - right. intro Hfalse. tauto. }
     { right. intro Hfalse. tauto.    }
Defined.

Definition lndt_any_all_able {F : TT} (aa : AnyAllAble F) : AnyAllAble (LNDT F) :=
  mkAnyAll (LNDT F)
           (lndt_any (any F aa))
           (lndt_dec_any _ (dec_any F aa))
           (lndt_all (all F aa))
           (lndt_dec_all _ (dec_all F aa)).

(** ** Decidability of equality *)
Lemma lndt_dec_eq {F : TT} : DecEq F -> DecEq (LNDT F).
Proof.
unfold DecEq. intros Hyp A HdecA.
(* @TODO Fix problem
induction x ; destruct y.
 + intuition.
 + right ; intro H ; inversion H.
 + right ; intro H ; inversion H.
 + specialize (Hyp A HdecA).
   specialize (IHx Hyp).  elim (HdecA a a0) ; intro HypeqA.
    - subst.  elim (IHx y) ; intro Hypeqy.
       * left; subst; auto.
       * right ; intro Hpb. inversion Hpb; contradiction.
    - right; intro Hpb ; inversion Hpb; contradiction.
Defined.
*)
  Admitted.

Definition lndt_eq_able {F : TT} (eq : EqAble F) : EqAble (LNDT F) :=
  mkEq (LNDT F) (lndt_dec_eq (dec_eq F eq)).

(** * Nested is spreadable. *)
Definition lndt_spreadable {F : TT} (sp : SpreadAble F) : SpreadAble (LNDT F) :=
  mkSpread (LNDT F)
    (lndt_foldable (fold_able F sp))
    (lndt_mapable (map_able F sp))
    (lndt_any_all_able (any_all_able F sp))
    (lndt_eq_able (eq_able F sp)).

Definition size_lndt {F : TT} (sp : SpreadAble F) A : LNDT F A -> nat :=
 (lndt_foldr _ (foldr _ (fold_able _ sp)) A nat (fun (x : nat) (_ : A) => x + 1) 0).
 
Eval compute in (size_lndt (tuple_spreadable 2) _ nested3).
(* = 13 : nat *)
