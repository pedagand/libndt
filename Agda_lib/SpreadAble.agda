-- Elements that can be spread for a certain TT F to LNDT F

module SpreadAble where

open import Dependencies.Imports

-- Type Transformers

TT : Setω
TT = ∀ {a} → Set a → Set a

-- MapAble type constructors

Map : TT → Setω
Map F = ∀ {a b} {A : Set a} {B : Set b} → (A → B) → F A → F B

-- Properties of MapAbles : congruence and composition

MapCongruence : ∀ {F : TT} → Map F → Setω
MapCongruence map = ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) x →
  (∀ x → f x ≡ g x) → map f x ≡ map g x

MapComposition : ∀ {F : TT} → Map F → Setω
MapComposition map = ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B) (g : B → C) x
  → map (g ∘ f) x ≡ (map g ∘ map f) x

record MapAble (F : TT) : Setω where
  constructor M⟨_,_,_⟩
  field
    map      : Map F
    map-cong : MapCongruence map
    map-comp : MapComposition map

open MapAble public

-- FoldAble type constructors

Fold : TT → Setω
Fold F = ∀ {a b} {A : Set a} {B : Set b} → (B → A → B) → B → F A → B

record FoldAble (F : TT) : Setω where
  constructor F⟨_,_⟩
  field
    foldl : Fold F
    foldr : Fold F

  size : ∀ {a} {A : Set a} → F A → ℕ
  size = foldr (const ∘ suc) 0

  flatten : ∀ {a} {A : Set a} → F A → Listₗ A
  flatten = foldr (flip _∷ₗ_) []ₗ

  show : ∀ {a} {A : Set a} → (A → String) → (F A → String)
  show showA = (_++ " ]") ∘ (foldl (λ s → ((s ++ " ") ++_) ∘ showA) "[")
  
open FoldAble public

-- A transformation of predicate over a type constructor (used later for Any and All)

TransPred : TT → Setω
TransPred F = ∀ {a b} {A : Set a} → Pred A b → Pred (F A) b

-- The preservation of decidability through TransPred

TransDec : ∀ {F : TT} → TransPred F → Setω
TransDec TransPF = ∀ {a b} {A : Set a} {P : Pred A b} → Decidableₚ P → Decidableₚ (TransPF P)

record AnyAllAble (F : TT) : Setω where
  constructor A⟨_,_,_,_⟩
  field
    any     : TransPred F
    dec-any : TransDec  any
    all     : TransPred F
    dec-all : TransDec  all
    
  _∈_ : ∀ {a} {A : Set a} → REL A (F A) a
  _∈_ x = any (x ≡_)

  empty : ∀ {a} {A : Set a} → Pred (F A) a
  empty l = ∀ {x} → ¬ x ∈ l

  dec-∈ : ∀ {a} {A : Set a} → Decidable {A = A} _≡_ → Decidable _∈_
  dec-∈ dec-≡ = dec-any ∘ dec-≡

open AnyAllAble public

-- Type constructors that preserve decidability of equality

DecEq : TT → Setω
DecEq F = ∀ {a} {A : Set a} → Decidable {A = A} _≡_ → Decidable {A = F A} _≡_

record EqAble (F : TT) : Setω where
  constructor E⟨_⟩
  field
    dec-eq : DecEq F

open EqAble public

-- All spread-able properties in a single record

record SpreadAble (F : TT) : Setω where
  constructor ⟨_,_,_,_⟩
  field
    fold-able    : FoldAble   F
    map-able     : MapAble    F
    any-all-able : AnyAllAble F
    eq-able      : EqAble     F
    
open SpreadAble public


