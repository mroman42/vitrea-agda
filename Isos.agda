module Isos where

open import Prelude.Function
open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


record _≅_ (A B : Set) : Set where
  field
    iso : A -> B
    inviso : B -> A
open _≅_ {{...}} public

infixr 2 _≅_

instance
  ≅-refl : {A : Set} -> A ≅ A
  ≅-refl = record { iso = id ; inviso = id }

  ≅-closed : {A B C : Set} -> (A × B -> C) ≅ (A -> (B -> C))
  ≅-closed = record { iso = λ z z₁ z₂ -> z (z₁ , z₂) ; inviso = λ z z₁ -> z (fst z₁) (snd z₁) }

  ≅-product : {A B C : Set} -> (A -> B × C) ≅ ((A -> B) × (A -> C))
  ≅-product = record
    { iso = λ x -> (λ z -> fst (x z)) , (λ z -> snd (x z))
    ; inviso = λ x x₁ -> (fst x x₁) , (snd x x₁)
    }

  ≅-coproduct : {A B C : Set} -> (A + B -> C) ≅ ((A -> C) × (B -> C))
  ≅-coproduct = record
    { iso = λ z -> (λ x -> z (left x)) , (λ x -> z (right x))
    ; inviso = λ { (f , g) (left x) -> f x ; (f , g) (right x) -> g x }
    }

  ≅-left-prod-side : {A B C : Set} -> {{_ : A ≅ B}} -> A × C ≅ B × C
  ≅-left-prod-side {{f}} = record
    { iso = λ x -> (_≅_.iso f (fst x)) , (snd x)
    ; inviso = λ x -> (_≅_.inviso f (fst x)) , (snd x) }

  ≅-right-prod-side : {A B C : Set} -> {{_ : A ≅ B}} -> C × A ≅ C × B
  ≅-right-prod-side {{f}} = record
    { iso = λ x -> (fst x) , (_≅_.iso f (snd x))
    ; inviso = λ x -> (fst x) , (_≅_.inviso f (snd x))
    }

  ≅-assoc : {A B C : Set} -> ((A × B) × C) ≅ (A × (B × C))
  ≅-assoc = record
    { inviso = λ x -> ((fst x) , (fst (snd x))) , (snd (snd x))
    ; iso = λ x -> (fst (fst x)) , ((snd (fst x)) , (snd x))
    }

  ≅-comm : {A B : Set} -> (A × B) ≅ (B × A)
  ≅-comm = record
    { iso = λ x -> (snd x) , (fst x)
    ; inviso = λ x -> (snd x) , (fst x)
    }

  cartesian-unit : {a : Set} -> Unit × a ≅ a
  cartesian-unit = record { iso = snd ; inviso = _,_ unit }

  cocartesian-unit : {a : Set} -> ⊥ + a ≅ a
  cocartesian-unit = record { iso = λ { (left ()) ; (right x) -> x } ; inviso = λ x -> right x }
  
  cocartesian-dist : {a b c : Set} -> (a + b) + c ≅ a + (b + c)
  cocartesian-dist = record
    { iso = λ { (left (left x)) -> left x ; (left (right x)) -> right (left x) ; (right x) -> right (right x) }
    ; inviso = λ { (left x) -> left (left x) ; (right (left x)) -> left (right x) ; (right (right x)) -> right x }
    }


≅-trans : {A B C : Set} -> A ≅ B -> B ≅ C -> A ≅ C
≅-trans u v = record
  { iso = λ z -> _≅_.iso v (_≅_.iso u z)
  ; inviso = λ z -> _≅_.inviso u (_≅_.inviso v z)
  }

symmetric : {A B : Set}
  -> A ≅ B
  -> B ≅ A
symmetric f = record { iso = _≅_.inviso f ; inviso = _≅_.iso f }



-- Common combinators for equational reasoning. They allow us to
-- write proofs in an equational style. These versions have been
-- adapted from the old version of the HoTT-agda library.
infixr -2 _≅⟨_⟩_
_≅⟨_⟩_ :  (a : Set) {b c : Set} -> a ≅ b -> b ≅ c -> a ≅ c
_ ≅⟨ p1 ⟩ p2 = ≅-trans p1 p2

infix -1 _qed
_qed : (x : Set) -> x ≅ x
_qed x = ≅-refl

infix  -3 begin_
begin_ : {a b : Set} -> a ≅ b -> a ≅ b
begin_ p = p

trivial : {A B : Set}{{_ : A ≅ B}} -> A ≅ B
trivial {{f}} = f


-- Automating the computation of isoisoisms.
exampleDerivation1 : {s c a b t : Set} -> (s -> c × a) ≅ (s -> c) × (s -> a)
exampleDerivation1 {s} {c} {a} {b} {t} =
  begin
    (s -> c × a)          ≅⟨ trivial ⟩
    (s -> c) × (s -> a)
  qed

exampleDerivation2 : {s c a b t : Set} -> (s -> c) × (s -> a) ≅ (s -> c × a)
exampleDerivation2 {s} {c} {a} {b} {t} =
  begin
    (s -> c) × (s -> a)   ≅⟨ symmetric trivial ⟩
    (s -> c × a)        
  qed

exampleDerivation : {s c a b t : Set} -> (s -> c × a) × (c × b -> t) ≅ (s -> c) × (s -> a) × (c × b -> t)
exampleDerivation {s} {c} {a} {b} {t} =
  begin
    (s -> c × a) × (c × b -> t)          ≅⟨ trivial ⟩
    ((s -> c) × (s -> a)) × (c × b -> t) ≅⟨ trivial ⟩
    (s -> c) × (s -> a) × (c × b -> t)
  qed
