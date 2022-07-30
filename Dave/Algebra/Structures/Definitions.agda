module Dave.Structures.Definitions where
    open import Dave.Equality public
 
    op₁ : Set → Set
    op₁ A = A → A

    op₂ : Set → Set
    op₂ A = A → A → A 

    associative : {A : Set} → op₂ A → Set
    associative _·_ = ∀ m n p → (m · n) · p ≡ m · (n · p)

    commutative : {A : Set} → op₂ A → Set
    commutative _·_ = ∀ m n → m · n ≡ n · m

    left-identity : {A : Set} → op₂ A → (e : A) → Set
    left-identity _·_ e = ∀ m → e · m ≡ m

    right-identity : {A : Set} → op₂ A → (e : A) → Set
    right-identity _·_ e = ∀ m → m · e ≡ m    