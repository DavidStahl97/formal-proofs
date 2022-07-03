module Dave.ComputerScience.Algorithms.Decidable where
    open import Dave.Equality
    open import Dave.Isomorphism
    open import Dave.Logic.Basics
    open import Dave.Functions

    data Bool : Set where
        false : Bool
        true : Bool    

    {-# BUILTIN BOOL  Bool  #-}
    {-# BUILTIN TRUE  true  #-}
    {-# BUILTIN FALSE false #-}  

    record _▸₁_ {A : Set} (f : A → Bool) (P : A → Set) : Set where
        field
            true▸ : ∀ {a} → f a ≡ true → P a
            false▸ : ∀ {a} → f a ≡ false → ¬ P a
            true◂ : ∀ {a} → P a → f a ≡ true

    record _▸₂_ {A B : Set} (f : A → B → Bool) (P : A → B → Set) : Set where
        field
            true▸ : ∀ {a b} → f a b ≡ true → P a b
            false▸ : ∀ {a b} → f a b ≡ false → ¬ P a b
            true◂ : ∀ {a b} → P a b → f a b ≡ true            