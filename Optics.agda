{-# OPTIONS --type-in-type #-}

module Optics where

open import Categories
open import Presheaves
open import Isos
open import Ends
open import Yoneda
open import Tambara
open import Prelude.Function
open import Prelude.Vec
open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


------------
-- OPTICS --
------------

-- Lenses
instance 
  cartesian-action : Action _×_
  cartesian-action = record { i = ⊤ ; _⊗_ = _×_  ; tmap = λ { f (a , b) -> a , f b } }

Cartesian : (Set -> Set -> Set) -> Set
Cartesian = Tambara _×_

lensProfunctorToExistential : {s t a b : Set} ->
  (∫forall p ∈ (Set -> Set -> Set) , ({{_ : Cartesian p}} -> p a b -> p s t)) ≅
  (∫exists c ∈ Set , ((s -> c × a) × (c × b -> t)))
lensProfunctorToExistential = opticFormula

lensDerivation : {s t a b : Set} ->
  (∫exists c ∈ Set , ((s -> c × a) × (c × b -> t))) ≅
  ((s -> a) × (s × b -> t))
lensDerivation {s} {t} {a} {b} =
  begin
   ((∫exists c ∈ Set , ((s -> c × a) × (c × b -> t))))           ≅⟨ ≅-coend (λ c -> trivial) ⟩
   ((∫exists c ∈ Set , (((s -> c) × (s -> a)) × (c × b -> t))))  ≅⟨ ≅-coend (λ c -> trivial) ⟩
   ((∫exists c ∈ Set , ((s -> c) × (s -> a) × (c × b -> t))))    ≅⟨ yoneda ⟩
   ((s -> a) × (s × b -> t))
  qed

lensProfunctorToConcrete : {s t a b : Set} ->
  (∫forall p ∈ (Set -> Set -> Set) , ({{_ : Cartesian p}} -> p a b -> p s t)) ≅
  ((s -> a) × (s × b -> t))
lensProfunctorToConcrete = ≅-trans lensProfunctorToExistential lensDerivation

record ConcreteLens (s t a b : Set) : Set where
  field
    view : s -> a
    update : s × b -> t
open ConcreteLens public    

Lens : Set -> Set -> Set -> Set -> Set
Lens s t a b = ∫forall p ∈ (Set -> Set -> Set) , ({{_ : Cartesian p}} -> p a b -> p s t)

mkLens : {s t a b : Set} -> ConcreteLens s t a b -> Lens s t a b
mkLens record { view = view ; update = update } = inviso {{ lensProfunctorToConcrete }} (view , update)


-- Prisms
instance 
  cocartesian-action : Action _+_
  cocartesian-action = record { i = ⊥ ; _⊗_ = _+_ ; tmap = λ { f (left x) -> left x ; f (right x) -> right (f x) } }

Cocartesian : (Set -> Set -> Set) -> Set
Cocartesian = Tambara _+_

prismProfunctorToExistential : {s t a b : Set} ->
  (∫forall p ∈ (Set -> Set -> Set) , ({{_ : Cocartesian p}} -> p a b -> p s t)) ≅
  (∫exists c ∈ Set , ((s -> c + a) × (c + b -> t)))
prismProfunctorToExistential = opticFormula

prismDerivation : {s t a b : Set} ->
  (∫exists c ∈ Set , ((s -> c + a) × (c + b -> t))) ≅
  (s -> t + a) × (b -> t)
prismDerivation {s} {t} {a} {b} =
  begin
   (∫exists c ∈ Set , ((s -> c + a) × (c + b -> t)))          ≅⟨ ≅-coend (λ c -> trivial) ⟩
   (∫exists c ∈ Set , ((s -> c + a) × ((c -> t) × (b -> t)))) ≅⟨ ≅-coend (λ c -> symmetric trivial) ⟩
   (∫exists c ∈ Set , (((s -> c + a) × (c -> t)) × (b -> t))) ≅⟨ ≅-coend (λ c -> trivial) ⟩
   (∫exists c ∈ Set , (((c -> t) × (s -> c + a)) × (b -> t))) ≅⟨ ≅-coend (λ c -> trivial) ⟩
   (∫exists c ∈ Set , ((c -> t) × ((s -> c + a) × (b -> t)))) ≅⟨ coyoneda ⟩
   ((s -> t + a) × (b -> t))
  qed


-- -- Traversals, over analytic functions
-- series : (Nat -> Set) -> Set -> Set
-- series c a = Σ Nat (λ n -> c n × Vec a n)


-- -- The problem I have with that description is that it is a bit
-- -- difficult to work with these things.  Working with combinatorial
-- -- species is easier than working with these things.
-- analytic-identity : Nat -> Set
-- analytic-identity 0 = ⊥
-- analytic-identity 1 = ⊤
-- analytic-identity (suc (suc n)) = ⊥

-- analytic-composition : (Nat -> Set) -> (Nat -> Set) -> (Nat -> Set)
-- analytic-composition c d zero = {!!}
-- analytic-composition c d (suc n) = {!!}

-- instance
--   analytic-identity-is-unit : {a : Set} -> series analytic-identity a ≅ a
--   analytic-identity-is-unit = record
--     { iso = left-right
--     ; inviso = right-left
--     }
--     where
--       left-right : {a : Set} -> series analytic-identity a -> a
--       left-right (0 , () , _)
--       left-right (1 , tt , x ∷ []) = x
--       left-right (suc _ , () , x ∷ y ∷ l)

--       right-left : {a : Set} -> a -> series analytic-identity a
--       right-left x = 1 , unit , x ∷ []

--   analytic-action : Action series
--   analytic-action = {!!}


-- Traversals, over traversables
