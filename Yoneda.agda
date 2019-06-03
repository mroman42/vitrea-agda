{-# OPTIONS --type-in-type #-}

module Yoneda where


open import Categories
open import Presheaves
open import Isos
open import Ends
open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


-- Yoneda lemma
module YonedaLemma {C : Set} {{_ : Category C}} where
  yoneda : {K : C -> Set} {{_ : Presheaf K}} {d : C} ->
    (∫exists c ∈ C , (hom d c × K c)) ≅ K d

  yoneda {K} {{_}} {d} = record
    { iso = λ { (c , f , k) -> pmap f k }
    ; inviso = λ x -> d , identity , x
    }
  
  coyoneda : {H : C -> Set} {{_ : Copresheaf H}} {d : C} ->
    (∫exists c ∈ C , (hom c d × H c)) ≅ H d

  coyoneda {H} {{_}} {d} = record
    { iso = λ { (c , f , x) -> cmap f x }
    ; inviso = λ x -> d , identity , x
    }
open YonedaLemma public

exampleDerivation4 : {s a : Set} -> 
  (∫exists c ∈ Set , ((c -> s) × (c × a))) ≅ (s × a)
exampleDerivation4 {s} {a} =
  begin
    (∫exists c ∈ Set , ((c -> s) × (c × a))) ≅⟨ coyoneda ⟩
    (s × a)
  qed
