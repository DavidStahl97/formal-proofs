module Algebra.Structures.Monoid where
    open import Algebra.Structures.Semigroup public

    record Identity {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            left : left-identity _·_ e
            right : right-identity _·_ e

    open Identity public

    record Monoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            semigroup : Semigroup _·_
            identity : Identity _·_ e

    open Monoid public
    
    record CommutativeMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            monoid : Monoid _·_ e
            comm : commutative _·_

    open CommutativeMonoid public