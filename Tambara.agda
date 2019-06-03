{-# OPTIONS --type-in-type #-}

module Tambara where

open import Categories
open import Presheaves
open import Isos
open import Ends
open import Yoneda
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


instance
  prof-category : Category (Set -> Set -> Set)
  prof-category = record
    { hom = λ p q -> ∫forall x ∈ Set , (p x x -> q x x)
    ; identity = λ a x -> x
    ; composition = λ x x₁ a x₂ -> x₁ a (x a x₂)
    }


record Action {C : Set} (_⊘_ : C -> Set -> Set) : Set where
  field
    i : C
    _⊗_ : C -> C -> C
    tmap : {a b : Set}{c : C} -> (a -> b) -> (c ⊘ a) -> (c ⊘ b)
    {{unitality}} : {a : Set} -> i ⊘ a ≅ a
    {{multiplicativity}} : {c d : C}{a : Set} -> (c ⊗ d) ⊘ a ≅ c ⊘ (d ⊘ a)
open Action {{...}} public

module TambaraModules {C : Set} {{_ : Category C}} where  
  record Tambara (_⊘_ : C -> Set -> Set) (p : Set -> Set -> Set) : Set where
    field
      dimap : {s t a b : Set} -> (s -> a) -> (b -> t) -> p a b -> p s t
      preserv : {a b : Set}{c : C} -> p a b -> p (c ⊘ a) (c ⊘ b)
  open Tambara {{...}} public  

  opticFormula : {s t a b : Set} {_⊘_ : C -> Set -> Set} {{_ : Action _⊘_}} ->
    (∫forall p ∈ (Set -> Set -> Set) , ({{_ : Tambara _⊘_ p}} -> p a b -> p s t))  ≅  (∫exists c ∈ C , ((s -> c ⊘ a) × (c ⊘ b -> t)))
  opticFormula {s} {t} {a} {b} {_⊘_} = record
    { iso = λ ρ -> ρ (λ s t -> (∫exists c ∈ C , ((s -> c ⊘ a) × (c ⊘ b -> t))))  idoptic
    ; inviso = λ { (c , u , v) p pab -> dimap u v (preserv pab) }
    }
    where
      -- Identity optic
      idoptic : (∫exists c ∈ C , ((a -> c ⊘ a) × (c ⊘ b -> b)))
      idoptic = i , inviso , iso

      -- We need to check that the right hand side is a Tambara module.
      instance 
        right-hand-side : Tambara _⊘_ (λ s t -> (∫exists c ∈ C , ((s -> c ⊘ a) × (c ⊘ b -> t)))) 
        right-hand-side = record
          { dimap = λ { f g (c , u , v) -> c , u ∘ f , g ∘ v }
          ; preserv = λ { {s} {t} {d} (c , u , v) -> d ⊗ c , inviso ∘ tmap u , tmap v ∘ iso }
          }

    -- This is double Yoneda!
    --   [[Optic , Set] , Set](-(s,t), -(a,b)) ≅ Optic((s,t),(a,b))
    -- where I would expect [Optic , Set] ≅ Tamb because of Pastro-Street 5.1.
open TambaraModules public
