-- The family of type constructors for n-ary perfectly balanced trees

open import Dependencies.Imports
open import SpreadAble
open import LNDT
open import Tuple

module LNDT.BalancedTree (n : ℕ) where

BalancedTree : TT
BalancedTree = LNDT (Tuple n)

bt-spread-able : SpreadAble BalancedTree
bt-spread-able = lndt-spread-able (tuple-spread-able n)

bt-map      = map      (map-able     bt-spread-able)
bt-map-cong = map-cong (map-able     bt-spread-able)
bt-map-comp = map-comp (map-able     bt-spread-able)
bt-foldr    = foldr    (fold-able    bt-spread-able)
bt-foldl    = foldl    (fold-able    bt-spread-able)
bt-size     = size     (fold-able    bt-spread-able)
bt-flatten  = flatten  (fold-able    bt-spread-able)
bt-show     = show     (fold-able    bt-spread-able)
bt-any      = any      (any-all-able bt-spread-able)
bt-dec-any  = dec-any  (any-all-able bt-spread-able)
bt-all      = all      (any-all-able bt-spread-able)
bt-dec-all  = dec-all  (any-all-able bt-spread-able)
bt-∈        = _∈_      (any-all-able bt-spread-able)
bt-empty    = empty    (any-all-able bt-spread-able)
bt-dec-∈    = dec-∈    (any-all-able bt-spread-able)
bt-dec-eq   = dec-eq   (eq-able      bt-spread-able)
bt-depth    = depth

