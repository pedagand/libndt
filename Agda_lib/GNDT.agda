module GNDT where

open import Dependencies.Imports
open import SpreadAble


-- Pattern functors

data Sig a : Set (lsuc a) where
  `⊤ : Sig a
  `K : Set a → Sig a
  `X : Sig a
  `A : Sig a
  _`×_ : Sig a → Sig a → Sig a
  _`⊎_ : Sig a → Sig a → Sig a

⟦_⟧ : ∀ {a} → Sig a → Set a → Set a → Set a
⟦ `⊤ ⟧ A X = Lift _ ⊤
⟦ `K S ⟧ A X = S
⟦ `X ⟧ A X = X
⟦ `A ⟧ A X = A
⟦ Σ₁ `× Σ₂ ⟧ A X = ⟦ Σ₁ ⟧ A X × ⟦ Σ₂ ⟧ A X
⟦ Σ₁ `⊎ Σ₂ ⟧ A X = ⟦ Σ₁ ⟧ A X ⊎ ⟦ Σ₂ ⟧ A X

⟦_⟧-map : ∀ {a}{A B X Y : Set a} → (Σ : Sig a) → (A → B) → (X → Y) → ⟦ Σ ⟧ A X → ⟦ Σ ⟧ B Y
⟦ `⊤ ⟧-map f g t = t
⟦ `K x ⟧-map f g k = k
⟦ `X ⟧-map f g x = g x
⟦ `A ⟧-map f g a = f a
⟦ Σ₁ `× Σ₂ ⟧-map f g (xs₁ , xs₂) = ⟦ Σ₁ ⟧-map f g xs₁ , ⟦ Σ₂ ⟧-map f g xs₂
⟦ Σ₁ `⊎ Σ₂ ⟧-map f g (inj₁ xs₁) = inj₁ (⟦ Σ₁ ⟧-map f g xs₁)
⟦ Σ₁ `⊎ Σ₂ ⟧-map f g (inj₂ xs₂) = inj₂ (⟦ Σ₂ ⟧-map f g xs₂)

□ : ∀ {a b}{A X : Set a} → (Σ : Sig a) → (X → Set b) → ⟦ Σ ⟧ A X → Set b
□ `⊤ P t = Lift _ ⊤
□ (`K x) P k = Lift _ ⊤
□ `X P x = P x
□ `A P a = Lift _ ⊤
□ (Σ₁ `× Σ₂) P (xs₁ , xs₂) = □ Σ₁ P xs₁ × □ Σ₂ P xs₂
□ (Σ₁ `⊎ Σ₂) P (inj₁ xs₁) = □ Σ₁ P xs₁
□ (Σ₁ `⊎ Σ₂) P (inj₂ xs₂) = □ Σ₂ P xs₂

-- The specification for generalized ndt data types

SIG : Setω
SIG = ∀ {a} → Sig a

_∘D_ : ∀ {a} → Sig a → Sig a → Sig a
`⊤ ∘D Σ' = `⊤
`K S ∘D Σ' = `K S
`X ∘D Σ' = Σ'
`A ∘D Σ' = `A
(Σ₁ `× Σ₂) ∘D Σ' = (Σ₁ ∘D Σ') `× (Σ₂ ∘D Σ')
(Σ₁ `⊎ Σ₂) ∘D Σ' = (Σ₁ ∘D Σ') `⊎ (Σ₂ ∘D Σ')

module G  {a} (Σ : SIG)(F : SIG) where

  data GNDT(P : SIG)(A : Set a) : Set a where
    ctor : ⟦ Σ ⟧ A (GNDT (P ∘D F) (⟦ P ∘D F ⟧ A (GNDT P A))) → GNDT P A

open G public

ΣBush : SIG
ΣBush = `⊤ `⊎ (`A `× `X)

FBush : SIG
FBush = ΣBush

Bush : ∀ {a} → Set a → Set a
Bush A = GNDT ΣBush FBush `X A

bnil : ∀ {a}{A : Set a} → Bush A
bnil = ctor (inj₁ (lift tt))

bcons : ∀ {a}{A : Set a} → A → Bush (Bush A) → Bush A
bcons {A = A} a (ctor bs) = ctor (inj₂ (a , ctor {!WRONG DEFINITION!!}))


{-
p-map : ∀ {a}{Σ : SIG}{F : SIG}{A B : Set a} → (A → B) → GNDT Σ F A → GNDT Σ F B
p-map {Σ = Σ}{F = F} f (ctor x) = {!!} -- ctor (⟦ Σ ⟧-map f (p-map (⟦ F ⟧-map f (p-map f))) x)

bout : ∀{a}{A : Set a} → Bush A → ⟦ ΣBush ⟧ A (⟦ FBush ⟧ A (GNDT ΣBush FBush A))
bout (ctor x) = ⟦ ΣBush ⟧-map (λ a → a) {!bout!} x
-}


-- Induction principle over generalized ndt data types

{-
module Induction {Σ : SIG}{F : TT}
                 {b}(P : ∀ {a}{A : Set a} → GNDT Σ F A → Set b)
                 (ih : ∀ {a}{A : Set a} → (xs : ⟦ Σ ⟧ A (GNDT Σ F (F A))) → □ Σ P xs → P (ctor xs)) where

       gndt-ind : ∀ {a}{A : Set a} (x : GNDT Σ F A) → P x

       □-map : ∀ {a}(Σ' : Sig a){A : Set a}
               (x : ⟦ Σ' ⟧ A (GNDT Σ F (F A))) → □ Σ' P x

       gndt-ind (ctor x) = ih x (□-map Σ x)

       □-map `⊤ t = lift tt
       □-map (`K S) k = lift tt
       □-map `X x = gndt-ind x
       □-map `A a = lift tt
       □-map (Σ₁ `× Σ₂) (xs₁ , xs₂) = □-map Σ₁ xs₁ , □-map Σ₂ xs₂
       □-map (Σ₁ `⊎ Σ₂) (inj₁ xs₁) = □-map Σ₁ xs₁
       □-map (Σ₁ `⊎ Σ₂) (inj₂ xs₂) = □-map Σ₂ xs₂

open Induction public
-}
