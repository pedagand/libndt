module LNDT.BalancedTree.Nest where

open import LNDT.BalancedTree 1 public
  hiding (
    bt-spread-able)
  renaming (
    BalancedTree  to Nest ;
    bt-map        to nest-map ;
    bt-map-cong   to nest-map-cong ;
    bt-map-comp   to nest-map-comp ;
    bt-foldr      to nest-foldr ;
    bt-foldl      to nest-foldl ;
    bt-size       to nest-size ;
    bt-flatten    to nest-flatten ;
    bt-show       to nest-show ;
    bt-any        to nest-any ;
    bt-dec-any    to nest-dec-any ;
    bt-all        to nest-all ;
    bt-dec-all    to nest-dec-all ;
    bt-∈          to nest-∈ ; 
    bt-empty      to nest-empty ;
    bt-dec-∈      to nest-dec-∈ ;
    bt-dec-eq     to nest-dec-eq ;
    bt-depth      to nest-depth)
