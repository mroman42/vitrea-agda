{-# OPTIONS --type-in-type #-}

module TraversableCostream where


open import Prelude.Function
open import Prelude.Vec
open import Prelude.List
open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


record Stream (a : Set) : Set where
  coinductive
  field
    hd : a
    tl : Stream a
open Stream public



traversableFromStream : Stream Set -> (Set -> Set)
traversableFromStream stream a = hd stream + (a × traversableFromStream (tl stream) a)
