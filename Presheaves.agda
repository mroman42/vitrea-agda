{-# OPTIONS --type-in-type #-}

module Presheaves where

open import Categories
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality

record Presheaf {C : Set} {{_ : Category C}}  (F : C -> Set) : Set where
  field
    pmap : {x y : C} -> hom x y -> F y -> F x
open Presheaf {{...}} public

record Copresheaf {C : Set} {{_ : Category C}} (F : C -> Set) : Set where
  field
    cmap : {x y : C} -> hom x y -> F x -> F y
open Copresheaf {{...}} public

instance
  identity-copresheaf : Copresheaf (λ z -> z)
  identity-copresheaf = record { cmap = λ {x} {y} z -> z }

  exp-presheaf : {t : Set} {C : Set} {{_ : Category C}}
    {F : C -> Set} {{_ : Copresheaf F}} -> Presheaf (λ c -> (F c -> t))
  exp-presheaf {a} {C} {F} = record { pmap = λ {x} {y} z z₁ z₂ -> z₁ (cmap z z₂) }

  exp-copresheaf : {t : Set} {C : Set} {{_ : Category C}}
    {F : C -> Set} {{_ : Copresheaf F}} -> Copresheaf (λ c -> (t -> F c))
  exp-copresheaf {t} {C} {F} = record { cmap = λ { x f z -> cmap x (f z) }}

module mult-copresheaf {a : Set} {C : Set} {{_ : Category C}} {F : C -> Set} {{_ : Copresheaf F}} where
  instance 
    left-mult-copresheaf : Copresheaf (λ b -> F b × a)
    left-mult-copresheaf = record { cmap = λ { f (x , y) -> cmap f x , y } }
      
    right-mult-copresheaf : Copresheaf (λ b -> a × F b)
    right-mult-copresheaf = record { cmap = λ { f (x , y) -> x , cmap f y } }
open mult-copresheaf public

module mult-presheaf {a : Set} {C : Set} {{_ : Category C}} {F : C -> Set} {{_ : Presheaf F}} where
  instance 
    left-mult-presheaf : Presheaf (λ b -> F b × a)
    left-mult-presheaf = record { pmap = λ { f (x , y) -> pmap f x , y } }

    right-mult-presheaf : Presheaf (λ b -> a × F b)
    right-mult-presheaf = record { pmap = λ { f (x , y) -> x , pmap f y } }
open mult-presheaf public

module sum-presheaf {a : Set} {C : Set} {{_ : Category C}} {F : C -> Set} {{_ : Presheaf F}} where
  instance
    right-sum-presheaf : Presheaf (λ c -> F c + a)
    right-sum-presheaf = record { pmap = λ { f (left x) -> left (pmap f x) ; f (right x) -> right x } }
open sum-presheaf public

module sum-copresheaf {a : Set} {C : Set} {{_ : Category C}} {F : C -> Set} {{_ : Copresheaf F}} where
  instance
    right-sum-copresheaf : Copresheaf (λ c -> F c + a)
    right-sum-copresheaf = record { cmap = λ { f (left x) -> left (cmap f x) ; f (right x) -> right x } }
open sum-copresheaf public
