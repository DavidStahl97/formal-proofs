module Dave.Structures.Semigroup where
    open import Dave.Structures.Definitions

    record IsSemigroup {A : Set} (_·_ : op₂ A) : Set where
        field
            assoc : associative _·_

    record Semigroup : Set₁ where
        field
            Carrier : Set
            _·_ : op₂ Carrier
            isSemigroup : IsSemigroup _·_