{-# OPTIONS --type-in-type #-}

module Categories where

open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


record Category (obj : Set) : Set where
  field
    hom : obj -> obj -> Set
    identity : {a : obj} -> hom a a
    composition : {a b c : obj} -> hom a b -> hom b c -> hom a c
open Category {{...}} public 

instance
  sets-category : Category Set
  sets-category = record
    { hom = λ a b -> (a -> b)
    ; identity = id
    ; composition = λ f g -> g ∘ f
    }
  
  product-category : {A B : Set}
    -> {{_ : Category A}}
    -> {{_ : Category B}}
    -> Category (A × B)
  product-category = record
    { hom = λ { (a₁ , b₁) (a₂ , b₂) -> hom a₁ a₂ × hom b₁ b₂ }
    ; identity = identity , identity
    ; composition = λ { (f₁ , g₁) (f₂ , g₂) -> composition f₁ f₂ , composition g₁ g₂ }
    }

record Functor {C D : Set} (F : C -> D) : Set where
  field
    {{is-category-C}} : Category C
    {{is-category-D}} : Category D
    fmap : {x y : C} -> hom x y -> hom (F x) (F y)
open Functor {{...}} public


