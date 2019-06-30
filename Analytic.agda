{-# OPTIONS --type-in-type #-}

module Analytic where

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

series : (Nat -> Set) -> Set -> Set
series c a = Σ Nat (λ n -> c n × Vec a n)

-- Finite set of given size.
Fin : Nat -> Set
Fin zero    = ⊥
Fin (suc n) = ⊤ + (Fin n)

-- Partition.
Partition : Set -> Nat -> Set
Partition a n = Vec (Σ Nat (Vec a)) n

-- Partitions.
record partition (n : Nat) : Set where
  field
    size : Nat
    ψ : Fin n -> Fin size
open partition public


sum : {s : Nat} -> Vec Nat s -> Nat
sum [] = 0
sum (x ∷ v) = x +N sum v

Shape : Nat -> Nat -> Set
Shape s n = Σ (Vec Nat s) λ v -> sum v ≡ n



-- Composition of analytic functors.
analytic-composition : (Nat -> Set) -> (Nat -> Set) -> (Nat -> Set)
analytic-composition f g n = {!!}
  
analytic-identity : Nat -> Set
analytic-identity 0 = ⊥
analytic-identity 1 = ⊤
analytic-identity (suc (suc n)) = ⊥


instance
  analytic-identity-is-unit : {a : Set} -> series analytic-identity a ≅ a
  analytic-identity-is-unit = record
    { iso = left-right
    ; inviso = λ z → 1 , unit , z ∷ []
    }
    where
      left-right : {a : Set} -> series analytic-identity a -> a
      left-right (.(suc _) , u , x ∷ v) = x 

  analytic-identity-composition : {a : Set} {f g : Nat -> Set} ->
    series f (series g a) ≅ series (analytic-composition f g) a
  analytic-identity-composition {a} {f} {g} = record
    { iso = {!!}
    ; inviso = {!!}
    }
    where
      left-right : series f (series g a) -> series (analytic-composition g f) a
      left-right (.0 , u , []) = 0 , (record { size = zero ; ψ = λ z → z } , u , λ {()}) , []
      left-right (.(suc _) , u , (nx , gx , vx) ∷ v) = {!!} , {!!} , {!!}

      right-left : series (analytic-composition g f) a -> series f (series g a)
      right-left (n , (record { size = size ; ψ = ψ } , l , f) , v) = size , l , {!!}
        where

