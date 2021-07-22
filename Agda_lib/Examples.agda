module Examples where

open import Dependencies.Imports
open import Dependencies.Exports
open import LNDT

-- Examples on Maybe

maybe-example-nothing : Maybe ℕ
maybe-example-nothing = nothing

maybe-example-just : Maybe ℕ
maybe-example-just = just 3

maybe-example-map-nothing : maybe-map (_+ 3) maybe-example-nothing ≡ nothing
maybe-example-map-nothing = refl

maybe-example-map-just : maybe-map (_+ 3) maybe-example-just ≡ just 6
maybe-example-map-just = refl

maybe-example-any-nothing : ¬ maybe-any (_< 2) maybe-example-nothing
maybe-example-any-nothing = λ ()

maybe-example-any-just : maybe-any (_> 2) maybe-example-just
maybe-example-any-just = here (s≤s (s≤s (s≤s z≤n)))

maybe-example-all-nothing : maybe-all (_< 2) maybe-example-nothing
maybe-example-all-nothing = all[]

maybe-example-all-just : ¬ maybe-all (_< 2) maybe-example-just
maybe-example-all-just (all∷ (s≤s (s≤s ())) all[])

maybe-example-size-nothing : maybe-size maybe-example-nothing ≡ 0
maybe-example-size-nothing = refl

maybe-example-size-just : maybe-size maybe-example-just ≡ 1
maybe-example-size-just = refl

maybe-example-fold-nothing : maybe-foldr (_+_) 4 maybe-example-nothing ≡ 4
maybe-example-fold-nothing = refl

maybe-example-fold-just : maybe-foldl (_+_) 4 maybe-example-just ≡ 7
maybe-example-fold-just = refl

maybe-example-show-nothing : maybe-show showₙ maybe-example-nothing ≡ "[ ]"
maybe-example-show-nothing = refl

maybe-example-show-just : maybe-show showₙ maybe-example-just ≡ "[ 3 ]"
maybe-example-show-just = refl

-- Examples on Lists

list-example : List Char
list-example = 'f' ∷ 'l' ∷ 'o' ∷ 'w' ∷ []

list-example-map : list-map ((_∸ 96) ∘ toℕ) list-example ≡ (6 ∷ 12 ∷ 15 ∷ 23 ∷ [])
list-example-map = refl

list-example-foldr : list-foldr (∣ _++_ ⟩- fromChar) "" list-example ≡ "wolf"
list-example-foldr = refl

list-example-foldl : list-foldl (∣ _++_ ⟩- fromChar) "" list-example ≡ "flow"
list-example-foldl = refl

list-example-size : list-size list-example ≡ 4
list-example-size = refl

list-example-any : list-any ((_≥ 10) ∘ (_∸ 96) ∘ toℕ) list-example
list-example-any = there (here (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))

list-example-all : list-all ((_≤ 23) ∘ (_∸ 96) ∘ toℕ) list-example
list-example-all =
  all∷ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (
  all∷ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))) (
  all∷ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))) (
  all∷ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))))))
  all[])))

list-example-show : list-show fromChar list-example ≡ "[ f l o w ]"
list-example-show = refl

-- Examples on Nests

nest-example : Nest ℕ
nest-example = 7 ∷ (1 , 2) ∷ ((6 , 7) , 7 , 4) ∷ ((2 , 5) , 7 , 1) , (3 , 8) , (9 , 3) ∷ []

nest-example-map : nest-map (_∸ 1) nest-example ≡ (6 ∷ (0 , 1) ∷ ((5 , 6) , 6 , 3) ∷ ((1 , 4) , 6 , 0) , (2 , 7) , (8 , 2) ∷ [])
nest-example-map = refl

nest-example-size : nest-size nest-example ≡ 15
nest-example-size = refl

nest-example-foldr : nest-foldr (∣ _++_ ⟩- showₙ) "" nest-example ≡ "398317524776217"
nest-example-foldr = refl

nest-example-foldl : nest-foldl _+_ 0 nest-example ≡ 72
nest-example-foldl = refl

nest-example-any : nest-any (_> 8) nest-example
nest-example-any = there (there (there (here (inj₂ (inj₂ (inj₁
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))

nest-example-all : nest-all (_≥ 1) nest-example
nest-example-all =
  all∷ (s≤s z≤n) (
  all∷ (s≤s z≤n , s≤s z≤n) (
  all∷ ((s≤s z≤n , s≤s z≤n) , s≤s z≤n , s≤s z≤n) (
  all∷ (((s≤s z≤n , s≤s z≤n) , s≤s z≤n , s≤s z≤n) , (s≤s z≤n , s≤s z≤n) , s≤s z≤n , s≤s z≤n)
  all[])))

nest-example-flatten : nest-flatten nest-example ≡ (7 ∷ₗ 1 ∷ₗ 2 ∷ₗ 6 ∷ₗ 7 ∷ₗ 7 ∷ₗ 4 ∷ₗ 2 ∷ₗ 5 ∷ₗ 7 ∷ₗ 1 ∷ₗ 3 ∷ₗ 8 ∷ₗ 9 ∷ₗ 3 ∷ₗ []ₗ)
nest-example-flatten = refl

nest-example-show : nest-show showₙ nest-example ≡ "[ 7 1 2 6 7 7 4 2 5 7 1 3 8 9 3 ]"
nest-example-show = refl

-- Examples on Bushes

bush-example : Bush ℕ
bush-example = 3 ∷ [] ∷ ((4 ∷ (7 ∷ []) ∷ []) ∷ ((10 ∷ []) ∷ []) ∷ []) ∷ []

bush-example-map : bush-map (_* 2) bush-example ≡ (6 ∷ [] ∷ ((8 ∷ (14 ∷ []) ∷ []) ∷ ((20 ∷ []) ∷ []) ∷ []) ∷ [])
bush-example-map = refl

bush-example-size : bush-size bush-example ≡ 4
bush-example-size = refl

bush-example-foldr : bush-foldr (∣ _++_ ⟩- showₙ) "" bush-example ≡ "10743"
bush-example-foldr = refl

bush-example-foldl : bush-foldl (_*_) 1 bush-example ≡ 840
bush-example-foldl = refl

bush-example-any : bush-any (_≡ 10) bush-example
bush-example-any = there (there (here (there (here (here (here refl))))))

bush-example-all : bush-all (_≥ 3) bush-example
bush-example-all = all∷ (s≤s (s≤s (s≤s z≤n))) (all∷ all[] (all∷ (all∷ (all∷
  (s≤s (s≤s (s≤s z≤n))) (all∷ (all∷ (s≤s (s≤s (s≤s z≤n))) all[])
  all[])) (all∷ (all∷ (all∷ (s≤s (s≤s (s≤s z≤n))) all[]) all[]) all[])) all[]))

bush-example-show : bush-show showₙ bush-example ≡ "[ 3 4 7 10 ]"
bush-example-show = refl
