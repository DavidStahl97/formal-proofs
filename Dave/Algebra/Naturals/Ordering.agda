module Dave.Algebra.Naturals.Ordering where
    open import Dave.Algebra.Naturals.Definition public
    open import Dave.Algebra.Naturals.Addition public
    open import Dave.Algebra.Naturals.Multiplication public
    open import Dave.Logic.Basics

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
    infix 4 _<_ _>_
    
    data _<_ : ℕ → ℕ → Set where
        z<s : ∀ {n : ℕ} → zero < suc n
        s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

    suc<→< : ∀ {m n : ℕ} → suc m < suc n → m < n
    suc<→< (s<s m<n) = m<n

    <-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
    <-trans z<s (s<s n<p) = z<s
    <-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)    

    +-monoᵣ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
    +-monoᵣ-< zero p q p<q = p<q
    +-monoᵣ-< (suc n) p q p<q = s<s (+-monoᵣ-< n p q p<q)

    +-monoₗ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
    +-monoₗ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoᵣ-< p m n m<n

    +-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
    +-mono-< m n p q m<n p<q = <-trans (+-monoₗ-< m n p m<n) (+-monoᵣ-< n p q p<q)

    suc-≤→< : ∀ (m n : ℕ) → suc m ≤ n → m < n
    suc-≤→< zero (suc n) leq = z<s
    suc-≤→< (suc m) (suc n) (s≤s leq) = s<s (suc-≤→< m n leq)

    <→suc-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
    <→suc-≤ zero (suc n) le = s≤s z≤n
    <→suc-≤ (suc m) (suc n) (s<s le) = s≤s (<→suc-≤ m n le)

    <-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
    <-irreflexive {zero} ()
    <-irreflexive {suc n} (s<s n<n) = <-irreflexive n<n

    suc-¬< : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
    suc-¬< ¬m<n sucm<sucn = ¬m<n (suc<→< sucm<sucn)

    pred-¬< : ∀ {m n : ℕ} → ¬ suc m < suc n → ¬ m < n
    pred-¬< {m} {n} ¬m<n m<n = ¬m<n (s<s m<n)    

    data _>_ : ℕ → ℕ → Set where
        co-m>n : ∀ {m n : ℕ} → n < m → m > n

    >→< : ∀ {m n : ℕ} → m > n → n < m
    >→< (co-m>n n<m) = n<m    

    ℕ-suc-> : ∀ {m n : ℕ} → m > n → suc m > suc n
    ℕ-suc-> (co-m>n x) = co-m>n (s<s x)

    suc>→> : ∀ {m n : ℕ} → suc m > suc n → m > n
    suc>→> (co-m>n sucn<sucm) = co-m>n (suc<→< sucn<sucm)

    suc-¬> : ∀ {m n : ℕ} → ¬ (m > n) → ¬ (suc m > suc n)
    suc-¬> ¬m>n sucm>sucn = ¬m>n (suc>→> sucm>sucn)

    >-irreflexive : ∀ {n : ℕ} → ¬ (n > n)
    >-irreflexive n>n = <-irreflexive (>→< n>n)

    {- Trichotomy -}
    data Trichotomy (m n : ℕ) : Set where
        t-m>n : m > n → ¬ (m < n) → ¬ (m ≡ n) → Trichotomy m n
        t-m≡n : m ≡ n → ¬ (m < n) → ¬ (m > n) → Trichotomy m n
        t-m<n : m < n → ¬ (m > n) → ¬ (m ≡ n) → Trichotomy m n
    
    ℕ-suc-Trichotomy : ∀ {m n : ℕ} → Trichotomy m n → Trichotomy (suc m) (suc n)
    ℕ-suc-Trichotomy (t-m>n m>n ¬m<n ¬m≡n) = t-m>n (ℕ-suc-> m>n) (suc-¬< ¬m<n) (ℕ-suc-≠ ¬m≡n)
    ℕ-suc-Trichotomy (t-m≡n m≡n ¬m<n ¬m>n) = t-m≡n (ℕ-suc-≡ m≡n) (suc-¬< ¬m<n) (suc-¬> ¬m>n)
    ℕ-suc-Trichotomy (t-m<n m<n ¬m>n ¬m≡n) = t-m<n (s<s m<n) (suc-¬> ¬m>n) (ℕ-suc-≠ ¬m≡n)

    ¬n<0 : ∀ {n : ℕ} → ¬ (n < 0)
    ¬n<0 ()

    ¬0>n : ∀ {n : ℕ} → ¬ (0 > n)
    ¬0>n (co-m>n n<m) = ¬n<0 n<m                

    <-swap : ∀ {m n : ℕ} → m < n → ¬ (n < m)
    <-swap z<s ()
    <-swap (s<s m<n) = suc-¬< (<-swap m<n)

    >-swap : ∀ {m n : ℕ} → m > n → ¬ (n > m)
    >-swap (co-m>n n<m) (co-m>n m<n) = <-swap m<n n<m

    ℕ-is-Trichotomy : ∀ (m n : ℕ) → Trichotomy m n
    ℕ-is-Trichotomy zero zero = t-m≡n refl <-irreflexive >-irreflexive
    ℕ-is-Trichotomy zero (suc n) = t-m<n z<s ¬0>n 0≠suc
    ℕ-is-Trichotomy (suc m) zero = t-m>n (co-m>n z<s) ¬n<0 suc≠0
    ℕ-is-Trichotomy (suc m) (suc n) = ℕ-suc-Trichotomy (ℕ-is-Trichotomy m n)