module Algebra.Naturals.Ordering where
    open import Algebra.Naturals.Definition public

    data _≤_ : ℕ → ℕ → Set where
        z≤n : ∀ {n : ℕ} → zero ≤ n
        s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
    
