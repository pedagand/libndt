module LNDT.BalancedTree.List where

open import LNDT.BalancedTree 0 public
  hiding (
    bt-spread-able)
  renaming (
    BalancedTree  to List ;
    bt-map        to list-map ;
    bt-map-cong   to list-map-cong ;
    bt-map-comp   to list-map-comp ;
    bt-foldr      to list-foldr ;
    bt-foldl      to list-foldl ;
    bt-size       to list-size ;
    bt-flatten    to list-flatten ;
    bt-show       to list-show ;
    bt-any        to list-any ;
    bt-dec-any    to list-dec-any ;
    bt-all        to list-all ;
    bt-dec-all    to list-dec-all ;
    bt-∈          to list-∈ ; 
    bt-empty      to list-empty ;
    bt-dec-∈      to list-dec-∈ ;
    bt-dec-eq     to list-dec-eq ;
    bt-depth      to list-depth)
