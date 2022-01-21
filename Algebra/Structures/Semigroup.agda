module Algebra.Structures.Semigroup where
    open import Algebra.Structures.Definitions public

    record IsSemigroup {A : Set} (_·_ : op₂ A) : Set where
        field
            assoc : associative _·_

    open IsSemigroup public

    record Semigroup : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            isSemigroup : IsSemigroup _·_

    open Semigroup public