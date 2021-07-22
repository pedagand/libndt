-- The Bush lndt datatype

open import Dependencies.Imports
open import SpreadAble
open import LNDT

module LNDT.Bush where

{-# TERMINATING #-}
Bush : TT
Bush = LNDT (Bush)

{-# TERMINATING #-}
bush-spread-able : SpreadAble Bush
bush-spread-able = lndt-spread-able bush-spread-able

bush-map      = map      (map-able     bush-spread-able)
bush-map-cong = map-cong (map-able     bush-spread-able)
bush-map-comp = map-comp (map-able     bush-spread-able)
bush-foldr    = foldr    (fold-able    bush-spread-able)
bush-foldl    = foldl    (fold-able    bush-spread-able)
bush-size     = size     (fold-able    bush-spread-able)
bush-flatten  = flatten  (fold-able    bush-spread-able)
bush-show     = show     (fold-able    bush-spread-able)
bush-any      = any      (any-all-able bush-spread-able)
bush-dec-any  = dec-any  (any-all-able bush-spread-able)
bush-all      = all      (any-all-able bush-spread-able)
bush-dec-all  = dec-all  (any-all-able bush-spread-able)
bush-∈        = _∈_      (any-all-able bush-spread-able)
bush-empty    = empty    (any-all-able bush-spread-able)
bush-dec-∈    = dec-∈    (any-all-able bush-spread-able)
bush-dec-eq   = dec-eq   (eq-able      bush-spread-able)
