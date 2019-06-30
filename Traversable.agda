{-# OPTIONS --type-in-type #-}

module Traversable where

open import Prelude.Function
open import Prelude.Vec
open import Prelude.List
open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Empty
open import Prelude.Product
open import Prelude.Sum renaming (Either to _+_)
open import Prelude.Equality


record Functor (f : Set -> Set) : Set where
  field
    fmap : {a b : Set} -> (a -> b) -> (f a -> f b)
open Functor {{...}} public

record Applicative (f : Set -> Set) : Set where
  field
    {{isFunctor}} : Functor f
    pure : {a : Set} -> a -> f a
    _⋆_ : {a b : Set} -> f (a -> b) -> f a -> f b
  infixl 30 _⋆_
open Applicative {{...}} public

lax : {f : Set -> Set} {{_ : Applicative f}} {a b : Set} -> f a -> f b -> f (a × b) 
lax x y = pure (_,_) ⋆ x ⋆ y

traverseList : {a : Set}{f : Set -> Set} {{_ : Applicative f}} -> List (f a) -> f (List a)
traverseList [] = pure []
traverseList (x ∷ l) = fmap (λ { (a , l) -> a ∷ l }) (lax x (traverseList l))

record Traversable (t : Set -> Set) : Set where
  field
    {{isFunctor}} : Functor t
    traverse : {a b : Set} {f : Set -> Set} {{_ : Applicative f}} ->
      (a -> f b) -> t a -> f (t b)
open Traversable {{...}} public


composition-functors : {g : Set -> Set} -> {f : Set -> Set} -> {{_ : Functor g}} -> {{_ : Functor f}} ->
  Functor (f ∘ g)
composition-functors = record { fmap = fmap ∘ fmap }

composition-traversables : {t : Set -> Set} -> {r : Set -> Set}
  -> {{_ : Traversable t}} -> {{_ : Traversable r}} ->
  Traversable (t ∘ r)
composition-traversables {t} {r} {{_}} {{_}} = record { traverse = traversing }
  where
    instance
      composition-functor : Functor (t ∘ r)
      composition-functor = composition-functors {r} {t}

    traversing : {a b : Set} {f : Set -> Set} {{_ : Applicative f}} -> (a -> f b) -> t (r a) -> f (t (r b))
    traversing g x = traverse (traverse g) x

crush : {a : Set} {t : Set -> Set} {{_ : Traversable t}} -> t a -> List a
crush {a} {t} = traverse {t} {a} {a} {f = λ s → List a} (λ x -> [ x ])
  where
    instance
      constFunctor : {a : Set} -> Functor (λ s -> List a)
      constFunctor = record { fmap = λ {a} {b} _ z → z }
      constApplicative : {a : Set} -> Applicative (λ s -> List a)
      constApplicative {a} = record { pure = λ {b} x -> [] ; _⋆_ = λ {b} {c} x y -> x ++ y }

len : {a : Set} {t : Set -> Set} {{_ : Traversable t}} -> t a -> Nat
len = length ∘ crush

powerSeries :  (t : Set -> Set) -> {{_ : Traversable t}} -> (Nat -> Set)
powerSeries t n = Σ (t Unit) λ p -> len p ≡ n

powerTraversal : (Nat -> Set) -> (Set -> Set)
powerTraversal c a = Σ Nat λ n -> c n × Σ (List a) λ l -> length l ≡ n

instance
  powerTraversalIsFunctor : {c : Nat -> Set} -> Functor (powerTraversal c)
  powerTraversalIsFunctor {c} = record
    { fmap = λ { f (n , v , l , α) -> n , v , map f l , yep l α }
    }
    where
      postulate
        yep : {a b : Set}(l : List a){f : a -> b}{n : Nat}
          -> length l ≡ n -> length (map f l) ≡ n

  powerTraversalIsTraversal : {c : Nat -> Set} -> Traversable (powerTraversal c)
  powerTraversalIsTraversal {c} = record { traverse = traversing }
    where
      traversing : {a b : Set} {f : Set -> Set} ⦃ _ : Applicative f ⦄ ->
        (a -> f b) -> powerTraversal c a -> f (powerTraversal c b)
      traversing {a} {b} {f} {{_}} g (n , s , l , α) = tra (poly α s)
        where
          flistb : f (List b)
          flistb = traverseList (map g l)

          poly : (length l ≡ n) -> c n -> powerTraversal c (f b)
          poly refl s = length l , s , map g l , yep
            where postulate yep : length (map g l) ≡ length l

          tra : powerTraversal c (f b) -> f (powerTraversal c b)
          tra (m , s , l , β) = fmap translate (lax flistb (lax (pure β) (pure s)))
            where
              translate : List b × length l ≡ m × c m -> powerTraversal c b
              translate (l , γ , s) = m , s , l , yep
                where postulate yep : length l ≡ m  
