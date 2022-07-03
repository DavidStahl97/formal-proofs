module Dave.ComputerScience.Algorithms.Decidable where
    open import Dave.Equality
    open import Dave.Isomorphism
    open import Dave.Logic.Basics
    open import Dave.ComputerScience.Algorithms.Boolean
    open import Dave.Functions

    record _▸₂_ {A B : Set} (f : A → B → Bool) (P : A → B → Set) : Set where
        field
            true▸ : ∀ {a : A} {b : B} → f a b ≡ true → P a b
            false▸ : ∀ {a : A} {b : B} → f a b ≡ false → ¬ P a b
            true◂ : ∀ {a : A} {b : B} → P a b → f a b ≡ true            