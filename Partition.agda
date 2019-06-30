{-# OPTIONS --type-in-type #-}

module Partition where

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

sum : {m : Nat} -> Vec Nat m -> Nat
sum {zero} v = zero
sum {suc m} (x ∷ v) = x +N (sum v)

-- Partitions
Part : Nat -> Set
Part n = Σ Nat λ m -> Σ (Vec Nat m) λ v -> sum v ≡ n

size : {n : Nat} -> Part n -> Nat
size (s , p) = s

split : {a : Set}{n : Nat} -> (p : Part n) -> Vec a n -> Vec (Σ Nat λ m -> Vec a m) (size p)
split (fst₁ , w , ) v = {!!}
