(* @TODO Which one? Elements ? Types ? *)
(** * Definitions of types that are preserved when nested *)
(** * Elements that can be spread for a certain TT F to LNDT F *)

Require Import Nat Coq.Lists.List.

(** ** Type Transformers *)
Definition TT := Type -> Type.

(** ** Mapable type constructors *)
Definition Map (F : TT) : Type :=
  forall A B  : Type, (A -> B) -> (F A -> F B).

(** ** Properties of Mapables : congruence and composition *)
Definition MapCongruence {F : TT} (map : Map F) : Type :=
  forall (A B : Type) (f : A -> B) (g : A -> B) (x : F A),
    (forall x, f x = g x) -> map A B f x = map A B g x.

Definition MapComposition {F : TT} (map : Map F) : Type :=
  forall (A B C : Type) (f : A -> B) (g : B -> C) x,
  map A C (fun x => g (f x)) x = map B C g ((map A B f) x).

Record MapAble (F : TT) : Type := mkMap
  { map        : Map F
  ; map_congru : MapCongruence  map
  ; map_compo  : MapComposition map }.

(** ** Foldable type constructors *)
Definition Fold (F : TT) : Type :=
  forall (A B : Type), (B -> A -> B) -> B -> F A -> B.

Definition flip {A B C : Type} f (a : A) (b : B) : C := f b a.

Record FoldAble (F : Type -> Type) : Type := mkFold
  { foldr   : Fold F ;
    foldl   : Fold F ;
    size    : forall {A : Type}, F A -> nat
      := fun A => foldl _ _ (fun x y => succ x) 0 ;
    flatten : forall {A : Type}, F A -> list A
      := fun A => foldl _ _ (flip cons) nil
  }.

(** ** A transformation of predicate over a type constructor
       (used later for Any and All) *)
Definition TransPred (F : TT) : Type :=
  forall (A : Type), (A -> Prop) -> ((F A) -> Prop).

(** ** The preservation of decidability through TransPred *)
(* @TODO dec in lib ? Pas trouvé... *)
Definition Dec (A:Type) (P:A -> Prop) :=
  forall (x:A), {P x} + {~ (P x)}.

Definition TransDec {F : TT} (TransPF : TransPred F) : Type :=
  forall (A : Type) (P : A -> Prop), Dec A P -> Dec (F A) (TransPF _ P).

(* @TODO correcte ? *)
Definition Decidable {A B : Type} (f : A -> B -> Prop) : Type :=
  forall (x:A) (y:B), {f x y} + {~(f x y)}.

Record AnyAllAble (F : TT) : Type := mkAnyAll
  { any     : TransPred F ;
    dec_any : TransDec any ;
    all     : TransPred F ;
    dec_all : TransDec all ;

    in_prop : forall (A : Type), A -> F A -> Prop
      := fun A x => any A (fun y => x = y ) ;
    empty : forall (A : Type), F A -> Prop
      := fun _ l => forall x, ~ in_prop _ x l ;
    dec_in_prop : forall (A : Type),
      Decidable eq -> Decidable (in_prop A)
      := fun A dec_equiv x y => dec_any A _ (dec_equiv x) y
  }.

(* @TODO MapMap - marche aussi avec in_prop --> empty *)
Definition MapSpec {F : TT}
           (mappable : MapAble F) (anyAllAble : AnyAllAble F) : Type :=
  forall (A : Type) (B : Type) x l (f : A -> B),
  (in_prop F anyAllAble) _ x l ->
  (in_prop F anyAllAble) _ (f x) (map F mappable _ _ f l).
(*
Lemma nested_map_spec :

Proof.
*)
(* @TODO FAIL
Lemma tuplesMapMap :
  forall (F : Type -> Type) (mappable : Mappable F) anyAllAble, Foldable F -> MapMap mappable anyAllAble.
Proof.
  unfold MapMap.
  intros.  induction ((size F X) l).
  + admit.
  + unfold in_prop in *. apply IHn.
  simpl in H.
  unfold in_prop in *.
  unfold any in *.

  simpl.
 - intros A B x l f Hyp. rewrite Hyp. reflexivity.
 - intros A B x l f Hyp. destruct Hyp.
    + left. rewrite H. reflexivity.
    + right. simpl in IHn. apply IHn. exact H.
Defined.
 *)

(** ** Type constructors that preserve decidability of equality *)
Definition DecEq (F : TT) : Type := forall (A: Type),
  @Decidable A A eq ->
  @Decidable (F A) (F A) eq.

Record EqAble (F : TT) : Type := mkEq
  { dec_eq : DecEq F }.

(* @TODO delete? *)
(** ** We call a type constructor regular when it provides everything
       that is preserved thought the nesting operation *)
(** ** All spread-able properties in a single record *)
Record SpreadAble (F : TT) : Type := mkSpread
  { fold_able    : FoldAble F ;
    map_able     : MapAble F ;
    any_all_able : AnyAllAble F ;
    eq_able      : EqAble F ;
    (*Lemma all_to_any : forall {A : Type} {P : F A -> Prop} {l},
      (all F anyAllAble) _ P l -> (any F anyAllAble) _ P l \/ (empty F anyAllAble _ l). ;
    all_to_forall : forall {A : Type} {P : F A -> Prop} {l},
      (all F anyAllAble) _ P l -> forall {x}, (in_prop F anyAllAble) _ x l -> P x ;
    any_to_exist : forall {A : Type} {P : F A -> Prop} {l},
      (any F anyAllAble) _ P l -> exists x, (in_prop F anyAllAble) _ x l /\ P x ;*)
    (* map ne change pas la taille *)
    (* mapMap : MapSpec map_able any_all_able ; *) (* @TODO delete? *)
    (* REDONDANT in_map  : forall (A B : Type) (f : A -> B) l (x : A),
      (in_prop F anyAllAble) x l ->
      (in_prop F anyAllAble) (f x) (map F mappable _ _ f l) *)
  }.
(*)
Lemma any_to_exist : forall {F : Type -> Type} {A : Type} {P : F A -> Prop} {l} anyAllAble,
      (any F anyAllAble) _ P l -> exists x, (in_prop F anyAllAble) _ x l /\ P x.
Proof.
  intros F A. generalize P, anyAllAble0. eexists. unfold in_prop. split.
  -  unfold any in *.  simpl in H. exact H.
    - H.
*)
(* TRASH )
Lemma all_to_forall : forall {F : Type -> Type} {A : Type} {P : F A -> Prop} {l} anyAllAble,
      (all F anyAllAble) _ P l -> forall {x}, (in_prop F anyAllAble) _ x l -> P x.
Proof.
intros.
unfold in_prop in *.
Admitted.

Lemma all_to_any : forall {F : Type -> Type} {A : Type} {P : F A -> Prop} {l}
  {anyAllAble},
      (all F anyAllAble) _ P l -> (any F anyAllAble) _ P l \/ (empty F anyAllAble _ l).
Proof.
  intros.
  assert(forall {x}, (in_prop F anyAllAble0) _ x l -> P x).
  apply (all_to_forall anyAllAble0). assumption.
  unfold all in *.
*)
  (*List.in_map:
  forall (A B : Type) (f : A -> B)
    (l : list A) (x : A),
  In x l -> In (f x) (map f l)*)
