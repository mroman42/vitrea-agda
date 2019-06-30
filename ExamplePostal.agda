module ExamplePostal where

open import Optics

open import Prelude.Nat
open import Prelude.String
open import Prelude.List
open import Prelude.Product

Address : Set
Address = String

record PostalAddress : Set where
  field
    number : Nat 
    street : String
    city   : String
    zipcode : String
open PostalAddress public


street' : Lens PostalAddress PostalAddress String String
street' = mkLens (record { view = street ; update = λ z ->
                                                        record
                                                        { number = number (fst z)
                                                        ; street = snd z
                                                        ; city = city (fst z)
                                                        ; zipcode = zipcode (fst z)
                                                        } })
