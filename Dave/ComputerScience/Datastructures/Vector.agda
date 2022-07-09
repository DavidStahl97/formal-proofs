module Dave.ComputerScience.Datastructures.Vector where
    open import Dave.Algebra.Naturals.Definition
    open import Dave.Algebra.Naturals.Addition
    open import Dave.ComputerScience.Datastructures.Boolean

    data Vector {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
        [] : Vector A zero
        _∷_ : ∀ {n : ℕ} → A → Vector A n → Vector A (suc n)

    _V++_ : ∀ {ℓ} {A : Set ℓ}{n m : ℕ}
        →  Vector A m → Vector A n
        → Vector A (m + n)
    [] V++ y = y
    (x ∷ xs) V++ y = x ∷ (xs V++ y)

    V-head : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A (suc n) → A
    V-head (x ∷ xs) = x

    V-tail : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vector A (suc n) → Vector A n
    V-tail (x ∷ xs) = xs

    V-map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ}
        → (A → B) → Vector A n → Vector B n
    V-map A→B [] = []
    V-map A→B (x ∷ v) = (A→B x) ∷ (V-map A→B v)