module GNDT where

open import Dependencies.Imports
open import SpreadAble


-- Pattern functors

data Sig : Set₁ where
  `⊤ : Sig
  `K : Set → Sig
  `X : Sig
  `A : Sig
  _`×_ : Sig → Sig → Sig
  _`⊎_ : Sig → Sig → Sig

⟦_⟧ : Sig → Set → Set → Set
⟦ `⊤ ⟧ A X = ⊤
⟦ `K S ⟧ A X = S
⟦ `X ⟧ A X = X
⟦ `A ⟧ A X = A
⟦ Σ₁ `× Σ₂ ⟧ A X = ⟦ Σ₁ ⟧ A X × ⟦ Σ₂ ⟧ A X
⟦ Σ₁ `⊎ Σ₂ ⟧ A X = ⟦ Σ₁ ⟧ A X ⊎ ⟦ Σ₂ ⟧ A X

⟦_⟧-map : ∀ {A B X Y : Set} → (Σ : Sig) → (A → B) → (X → Y) → ⟦ Σ ⟧ A X → ⟦ Σ ⟧ B Y
⟦ `⊤ ⟧-map f g t = t
⟦ `K x ⟧-map f g k = k
⟦ `X ⟧-map f g x = g x
⟦ `A ⟧-map f g a = f a
⟦ Σ₁ `× Σ₂ ⟧-map f g (xs₁ , xs₂) = ⟦ Σ₁ ⟧-map f g xs₁ , ⟦ Σ₂ ⟧-map f g xs₂
⟦ Σ₁ `⊎ Σ₂ ⟧-map f g (inj₁ xs₁) = inj₁ (⟦ Σ₁ ⟧-map f g xs₁)
⟦ Σ₁ `⊎ Σ₂ ⟧-map f g (inj₂ xs₂) = inj₂ (⟦ Σ₂ ⟧-map f g xs₂)

□ : ∀ {a}{A X : Set} → (Σ : Sig) → (X → Set a) → ⟦ Σ ⟧ A X → Set a
□ `⊤ P t = Lift _ ⊤
□ (`K x) P k = Lift _ ⊤
□ `X P x = P x
□ `A P a = Lift _ ⊤
□ (Σ₁ `× Σ₂) P (xs₁ , xs₂) = □ Σ₁ P xs₁ × □ Σ₂ P xs₂
□ (Σ₁ `⊎ Σ₂) P (inj₁ xs₁) = □ Σ₁ P xs₁
□ (Σ₁ `⊎ Σ₂) P (inj₂ xs₂) = □ Σ₂ P xs₂

-- The specification for generalized ndt data types

data GNDT (Σ : Sig)(F : TT)(A : Set) : Set where
  ctor : ⟦ Σ ⟧ A (GNDT Σ F (F A)) → GNDT Σ F A

-- Induction principle over generalized ndt data types

module Induction {Σ : Sig}{F : TT}
                 {b}(P : ∀ {A : Set} → GNDT Σ F A → Set b)
                 (ih : ∀ {A : Set} → (xs : ⟦ Σ ⟧ A (GNDT Σ F (F A))) → □ Σ P xs → P (ctor xs)) where

       gndt-ind : ∀ {A : Set} (x : GNDT Σ F A) → P x

       □-map : ∀ (Σ' : Sig){A : Set}
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
