module Dave.ComputerScience.Algorithms.Vector where
    open import Dave.Algebra.Naturals.Definition
    open import Dave.Algebra.Naturals.Addition
    open import Dave.ComputerScience.Algorithms.Boolean

    data Vector {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
        [] : Vector A zero
        _∷_ : ∀ {n : ℕ} → A → Vector A n → Vector A (suc n)

    _++_ : ∀ {ℓ} {A : Set ℓ}{n m : ℕ}
        →  Vector A m → Vector A n
        → Vector A (m + n)
    [] ++ y = y
    (x ∷ xs) ++ y = x ∷ (xs ++ y)

    head : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A (suc n) → A
    head (x ∷ xs) = x

    tail : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A (suc n) → Vector A n
    tail (x ∷ xs) = xs

    map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ}
        → (A → B) → Vector A n → Vector B n
    map A→B [] = []
    map A→B (x ∷ v) = (A→B x) ∷ (map A→B v)