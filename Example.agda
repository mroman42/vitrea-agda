module Example where

open import Optics

open import Prelude.Int
open import Prelude.Fractional
open import Prelude.List
open import Prelude.Product

record Point : Set where
  field
    x : Int
    y : Int
open Point public    
       
record Unit : Set where
  field
    health : Int
    position : Point
open Unit public    

record Game : Set where
  field
    score' : Int
    units' : List Unit
open Game public  


score : Lens Game Game (List Unit) (List Unit)
score = mkLens (record
  { view = units'
  ; update = λ { (g , u) -> record { score' = score' g ; units' = u } }
  })

