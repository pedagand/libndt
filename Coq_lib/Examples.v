Require Import Nat Coq.Lists.List.

(* @TODO structure Require ? Section ? Module ? *)

Require Spreadable.

Eval compute in (Spreadable.Map list).
(* Le map des listes a le type Map list *)
Definition maplist : Spreadable.Map list := Coq.Lists.List.map.

Eval compute in (Spreadable.Fold list).

Eval compute in (Spreadable.TransPred list).

Eval compute in (Spreadable.DecEq list).


Require Tuple.

Eval compute in (Map (Tuple 3)).
(* forall A B : Type,
       (A -> B) ->
       A * (A * (A * A)) -> B * (B * (B * B))*)

Eval compute in (Fold (Tuple 2)).

Check (flatten (Tuple 4) (tuple_foldable 4)).
