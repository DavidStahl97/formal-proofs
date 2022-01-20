module Algebra.Structures.Semigroup where
    open import Algebra.Structures.Definitions public

    record Semigroup {A : Set} (_·_ : op₂ A) : Set where
        field
            assoc : associative _·_

    open Semigroup public