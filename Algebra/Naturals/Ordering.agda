module Algebra.Naturals.Ordering where
    open import Algebra.Naturals.Definition public
    open import Algebra.Naturals.Addition public
    open import Algebra.Naturals.Multiplication public

    -- TO-DO: define relation
    data _≤_ : ℕ → ℕ → Set where
        z≤n : ∀ {n : ℕ} → zero ≤ n
        s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n        
    
    infix 4 _≤_

    inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
    inv-s≤s (s≤s m≤n) = m≤n

    inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
    inv-z≤n z≤n = refl

    -- TO-DO: define relation properties in general
    ≤-refl : ∀ {n : ℕ} → n ≤ n
    ≤-refl {zero} = z≤n
    ≤-refl {suc n} = s≤s ≤-refl

    ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
    ≤-trans z≤n n≤p = z≤n
    ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

    ≤-trans´ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
    ≤-trans´ zero n p z≤n n≤p = z≤n
    ≤-trans´ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans´ m n p m≤n n≤p)

    ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
    ≤-antisym z≤n z≤n = refl
    ≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

    data Total (m n : ℕ) : Set where
        forward : m ≤ n → Total m n
        flipped : n ≤ m → Total m n

    data Total´ : ℕ → ℕ → Set where
        forward´ : ∀ {m n : ℕ} → m ≤ n → Total´ m n
        flipped´ : ∀ {m n : ℕ} → n ≤ m → Total´ m n

    ≤-total : ∀ (m n : ℕ) → Total m n
    ≤-total zero n = forward z≤n
    ≤-total (suc m) zero = flipped z≤n
    ≤-total (suc m) (suc n) with ≤-total m n
    ...                         | forward m≤n = forward (s≤s m≤n)    
    ...                         | flipped n≤m = flipped (s≤s n≤m)

    ≤-total´ : ∀ (m n : ℕ) → Total m n
    ≤-total´ zero n = forward z≤n
    ≤-total´ (suc m) zero = flipped z≤n
    ≤-total´ (suc m) (suc n) = helper (≤-total´ m n)
        where
        helper : Total m n → Total (suc m) (suc n)
        helper (forward m≤n) = forward (s≤s m≤n)
        helper (flipped n≤m) = flipped (s≤s n≤m)

    +-monoᵣ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
    +-monoᵣ-≤ zero p q p≤q = p≤q
    +-monoᵣ-≤ (suc n) p q p≤q = s≤s (+-monoᵣ-≤ n p q p≤q)

    +-monoₗ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
    +-monoₗ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p = +-monoᵣ-≤ p m n m≤n

    +-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
    +-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoₗ-≤ m n p m≤n) (+-monoᵣ-≤ n p q p≤q)

    *-monoᵣ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
    *-monoᵣ-≤ zero p q p≤q = z≤n
    *-monoᵣ-≤ (suc n) p q p≤q = +-mono-≤ (n * p) (n * q) p q (*-monoᵣ-≤ n p q p≤q) p≤q

    *-monoₗ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
    *-monoₗ-≤ m n p m≤n  rewrite ℕ-*-comm m p | ℕ-*-comm n p = *-monoᵣ-≤ p m n m≤n

    *-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
    *-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoₗ-≤ m n p m≤n) (*-monoᵣ-≤ n p q p≤q)

    {- Strict inequality -}
    infix 4 _<_
    
    data _<_ : ℕ → ℕ → Set where
        z<s : ∀ {n : ℕ} → zero < suc n
        s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

    <-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
    <-trans z<s (s<s n<p) = z<s
    <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)
    