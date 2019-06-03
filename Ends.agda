{-# OPTIONS --type-in-type #-}

module Ends where

open import Categories
open import Isos
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality



-- Ends and coends, enriched over set.  I am taking two decisions that
-- can be difficult to justify. First, I do not take ends or coends
-- over a profunctor, just over the assignment. Because of this I
-- cannot check the axioms.  This is more a forall/exists than an
-- end/coend.
end : {A : Set}{{_ : Category A}} -> (A -> Set) -> Set
end {A} p = (a : A) -> p a

coend : {A : Set}{{_ : Category A}} -> (A -> Set) -> Set
coend {A} p = Σ A (λ x -> p x)

syntax end {C} (λ x -> f) = ∫forall x ∈ C , f
syntax coend {C} (λ x -> f) = ∫exists x ∈ C , f

≅-end : {C : Set} {{_ : Category C}} {p q : C -> Set} ->
  ((c : C) -> p c ≅ q c) ->
  (∫forall x ∈ C , p x) ≅ (∫forall x ∈ C , q x)
≅-end f = record { iso = λ z a -> _≅_.iso (f a) (z a) ; inviso = λ z a -> _≅_.inviso (f a) (z a) }
    
≅-coend : {C : Set} {{_ : Category C}} {p q : C -> Set} ->
  ((c : C) -> p c ≅ q c) ->
  (∫exists x ∈ C , p x) ≅ (∫exists x ∈ C , q x)
≅-coend f = record
  { iso = λ { (c , g) -> c , _≅_.iso (f c) g }
  ; inviso = λ { (c , g) -> c , _≅_.inviso (f c) g }
  }


-- Example with coends
exampleDerivation3 : {s c a b t : Set} ->
  ∫exists c ∈ Set , ((s -> c × a) × (c × b -> t)) ≅
  ∫exists c ∈ Set , ((s -> c) × (s -> a) × (c × b -> t))
exampleDerivation3 {s} {c} {a} {b} {t} =
  begin
    (∫exists c ∈ Set , ((s -> c × a) × (c × b -> t)))          ≅⟨ ≅-coend (λ c -> trivial) ⟩
    (∫exists c ∈ Set , (((s -> c) × (s -> a)) × (c × b -> t))) ≅⟨ ≅-coend (λ c -> trivial) ⟩
    (∫exists c ∈ Set , ((s -> c) × (s -> a) × (c × b -> t)))
  qed
