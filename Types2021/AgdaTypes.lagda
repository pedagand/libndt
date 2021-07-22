\newcommand{\imports}{
\begin{code}
module AgdaTypes where

open import Agda.Primitive
open import Data.Product using (_×_ ; _,_ ; ∃)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.String
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
\end{code}
}

\newcommand{\exampleList}{
\begin{code}
data List₀ {a} (A : Set a) : Set a where
  [] : List₀ A
  _∷_ : A → List₀ A → List₀ A
\end{code}
}

\newcommand{\exampleNest}{
\begin{code}
data Nest₀ {a} (A : Set a) : Set a where
  [] : Nest₀ A
  _∷_ : A → Nest₀ (A × A) → Nest₀ A
\end{code}
}

\newcommand{\exampleBush}{
\begin{code}
data Bush₀ {a} (A : Set a) : Set a where
  [] : Bush₀ A
  _∷_ : A → Bush₀ (Bush₀ A) → Bush₀ A
\end{code}
}

\begin{code}[hide]
TT : Setω
TT = ∀ {b} → Set b → Set b
\end{code}

\newcommand{\lndt}{
\begin{code}
data LNDT (F : TT) {a} (A : Set a) : Set a where
  [] : LNDT F A
  _∷_ : A → LNDT F (F A) → LNDT F A
\end{code}
}

\newcommand{\tuples}{
\begin{code}
Tuple : ℕ → TT
Tuple zero = id -- id is the identity function
Tuple (suc n) A = A × (Tuple n A)
\end{code}
}

\newcommand{\nary}{
\begin{multicols}{2}
\begin{code}
N-PT : ℕ → TT
\end{code}
\columnbreak
\begin{code}
N-PT n = LNDT (Tuple n)
\end{code}
\end{multicols}
}
\newcommand{\lndtdefs}{
\begin{multicols}{3}
\begin{code}
List : TT
List = N-PT 0
\end{code}
\columnbreak
\begin{code}
Nest : TT
Nest = N-PT 1
\end{code}
\columnbreak
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\begin{code}
Bush : TT
Bush = LNDT Bush
\end{code}
\end{multicols}
}

\newcommand{\lndtnull}{
\begin{multicols}{2}
\begin{code}
data ⊥ {a} : Set a where
  -- Empty type
\end{code}
\columnbreak
\begin{code}
Null : TT
Null _ = ⊥
\end{code}
\end{multicols}
}

\newcommand{\maybe}{
\begin{multicols}{2}
\begin{code}
Maybe : TT
Maybe = LNDT Null
\end{code}
\columnbreak
\begin{code}
pattern nothing = []
pattern just x  = x ∷ []
\end{code}
\end{multicols}
}

\newcommand{\listmap}{
\begin{code}
list-map₀ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
list-map₀ f [] = []
list-map₀ f (x ∷ l) = f x ∷ list-map₀ f l
\end{code}
}

\newcommand{\nestmap}{
\begin{code}
nest-map₀ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Nest A → Nest B
nest-map₀ f [] = []
nest-map₀ f (x ∷ n) = f x ∷ nest-map₀ (λ {(a , b) → f a , f b}) n
\end{code}
}

\newcommand{\lndtmapz}{
\begin{code}
lndt-map₀ : ∀ {a b} {A : Set a} {B : Set b} {F : TT} → (A → B) →
  (T : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (F A → F B))
  → LNDT F A → LNDT F B
lndt-map₀ _ _ [] = []
lndt-map₀ f T (x ∷ e) = f x ∷ lndt-map₀ (T f) T e
\end{code}
}

\newcommand{\mappable}{
\begin{code}
Map : TT → Setω
Map F = ∀ {a b} {A : Set a} {B : Set b} → (A → B) → F A → F B
\end{code}
}

\newcommand{\lndtmap}{
\begin{code}
lndt-map : ∀ {F : TT} → Map F → Map (LNDT F)
lndt-map F f [] = []
lndt-map F f (x ∷ e) = f x ∷ lndt-map F (F f) e
\end{code}
}

\begin{code}[hide]
list-map : Map List
nest-map : Map Nest
bush-map : Map Bush
maybe-map : Map Maybe
\end{code}

\newcommand{\tuplesmap}{
\begin{code}
tuple-map : ∀ n → Map (Tuple n)
tuple-map zero = id
tuple-map (suc n) f (a , ta) = f a , tuple-map n f ta
\end{code}
}

\newcommand{\lndtmaps}{
\begin{multicols}{2}
\begin{code}
list-map = lndt-map (tuple-map 0)
nest-map = lndt-map (tuple-map 1)
\end{code}
\columnbreak
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\begin{code}
bush-map = lndt-map bush-map
maybe-map = lndt-map λ _ ()
\end{code}
\end{multicols}
}

\begin{code}[hide]
infixr 10 _∷_
\end{code}

\newcommand{\firstexample}{
\begin{multicols}{2}
\begin{code}
map₀ : list-map suc (3 ∷ 4 ∷ 2 ∷ 6 ∷ [])
  ≡ 4 ∷ 5 ∷ 3 ∷ 7 ∷ []
map₀ = refl
\end{code}
\columnbreak
\begin{code}
map₁ : bush-map (_* 2) (3 ∷ (4 ∷ []) ∷ [])
  ≡ (6 ∷ (8 ∷ []) ∷ [])
map₁ = refl
\end{code}
\end{multicols}
}

\newcommand{\fold}{
\begin{code}
Fold : TT → Setω
Fold F = ∀ {a b} {A : Set a} {B : Set b} → (B → A → B) → B → F A → B
\end{code}
}

\newcommand{\folds}{
\begin{code}
lndt-foldl : ∀ {F : TT} → Fold F → Fold (LNDT F)
lndt-foldl _ _ b [] = b
lndt-foldl foldl f b (x ∷ e) = lndt-foldl foldl (foldl f) (f b x) e
\end{code}
}

\newcommand{\foldtuples}{
\begin{code}
tuple-foldl : ∀ n → Fold (Tuple n)
tuple-foldl zero = id
tuple-foldl (suc n) f b₀ (a , ta) = tuple-foldl n f (f b₀ a) ta
\end{code}
}

\newcommand{\foldsinstances}{
\begin{multicols}{2}
\begin{code}
nest-foldl : Fold Nest
nest-foldl = lndt-foldl (tuple-foldl 1)
\end{code}
\columnbreak
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\begin{code}
bush-foldl : Fold Bush
bush-foldl = lndt-foldl bush-foldl
\end{code}
\end{multicols}
}
  
\newcommand{\foldsexamples}{
\begin{code}
foldl₀ : nest-foldl _++_ "" ("a" ∷ ("u" , "r") ∷ (("e" , "l") , "i" , "a") ∷ [])
  ≡ "aurelia" ; foldl₀ = refl
--
foldl₁ : bush-foldl _++_ "l" ("o" ∷ ("l" ∷ []) ∷ (("a" ∷ []) ∷ []) ∷ [])
  ≡ "lola" ; foldl₁ = refl
\end{code}
}

\newcommand{\lndtlist}{
\begin{multicols}{2}
\begin{code}
SquaredList : TT
\end{code}
\columnbreak
\begin{code}
SquaredList = LNDT List
\end{code}
\end{multicols}
}

\newcommand{\lndtlistexample}{
\begin{code}
squared-list-example : SquaredList ℕ
squared-list-example = 8 ∷ (4 ∷ 5 ∷ []) ∷ ((3 ∷ 6 ∷ []) ∷ (7 ∷ 1 ∷ 8 ∷ []) ∷ []) ∷ []
\end{code}
}

\newcommand{\lndtlistmap}{
\begin{multicols}{2}
\begin{code}
squared-list-map : Map SquaredList
\end{code}
\columnbreak
\begin{code}
squared-list-map = lndt-map list-map
\end{code}
\end{multicols}
}

\newcommand{\lndtlistmapexample}{
\begin{code}
squared-list-map-example : squared-list-map (_* 2) squared-list-example
  ≡ 16 ∷ (8 ∷ 10 ∷ []) ∷ ((6 ∷ 12 ∷ []) ∷ (14 ∷ 2 ∷ 16 ∷ []) ∷ []) ∷ []
squared-list-map-example = refl
\end{code}
}
