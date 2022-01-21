module Algebra.Structures.Monoid where
    open import Algebra.Structures.Semigroup public

    record Identity {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            left : left-identity _·_ e
            right : right-identity _·_ e

    open Identity public

    record IsMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            semigroup : IsSemigroup _·_
            identity : Identity _·_ e

    open IsMonoid public
    
    record Monoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isMonoid : IsMonoid _·_ e             

    open Monoid public

    record IsCommutativeMonoid {A : Set} (_·_ : op₂ A) (e : A) : Set where
        field
            monoid : IsMonoid _·_ e
            comm : commutative _·_        

    open IsCommutativeMonoid public

    record CommutativeMonoid : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            e : Carrier
            isCommutativeMonoid : IsCommutativeMonoid _·_ e
    
    open CommutativeMonoid public