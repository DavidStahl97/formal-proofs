module Dave.ComputerScience.Algorithms.NaturalNumbers.Ordering where
    open import Dave.ComputerScience.Datastructures.Module
    open import Dave.ComputerScience.Algorithms.NaturalNumbers.Equality
    open import Dave.Logic.Module
    open import Dave.Algebra.Naturals.Module

    is_<_ : ℕ → ℕ → Bool
    is zero < zero = false
    is zero < suc n = true
    is suc m < zero = false
    is suc m < suc n = is m < n

    is▸< : is_<_ ▸₂ _<_
    is▸< = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = true◂
        }
        where
        true▸ : ∀ {m n : ℕ} → (is m < n) ≡ true → m < n        
        true▸ {zero} {suc n} is-true = z<s
        true▸ {suc m} {suc n} is-true = s<s (true▸ is-true)

        false▸ : ∀ {m n : ℕ} → (is m < n) ≡ false → ¬ m < n        
        false▸ {zero} {zero} ≡-refl ()
        false▸ {suc m} {zero} is-false ()
        false▸ {suc m} {suc n} is-false (s<s x) = false▸ is-false x

        true◂ : ∀ {m n : ℕ} → m < n → (is m < n) ≡ true
        true◂ {zero} {suc n} m<n = ≡-refl
        true◂ {suc m} {suc n} (s<s m<n) = true◂ m<n

    is_≤_ : ℕ → ℕ → Bool
    is m ≤ n = (is m < n) || (is m ≡ n)

    is▸≤ : is_≤_ ▸₂ _≤_
    is▸≤ = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = true◂
        }
        where
        true▸ : ∀ {m n : ℕ} → (is m ≤ n) ≡ true → m ≤ n
        true▸ {zero} {n} m≤n = z≤n
        true▸ {suc m} {suc n} m≤n = s≤s (true▸ m≤n)

        pred-is≤≡false : ∀ {m n : ℕ}
            → (is suc m ≤ suc n) ≡ false    
            → (is m ≤ n) ≡ false
        pred-is≤≡false {zero} {zero} ()
        pred-is≤≡false {zero} {suc n} ()
        pred-is≤≡false {suc m} {zero} ≡-refl = ≡-refl
        pred-is≤≡false {suc m} {suc n} is-sucm≤sucn = pred-is≤≡false {m} {n} is-sucm≤sucn    

        false▸ : ∀ {m n : ℕ} → (is m ≤ n) ≡ false → ¬ m ≤ n
        false▸ {.0} {zero} () z≤n
        false▸ {.0} {suc n} () z≤n
        false▸ {suc m} {suc n} is-m≤n (s≤s x) = false▸ (pred-is≤≡false {m} {n} is-m≤n) x

        suc-is≤≡true : ∀ {m n : ℕ} → (is m ≤ n) ≡ true → (is suc m ≤ suc n) ≡ true
        suc-is≤≡true {zero} {zero} is-m≤n = ≡-refl
        suc-is≤≡true {zero} {suc n} is-m≤n = ≡-refl
        suc-is≤≡true {suc m} {suc n} is-m≤n = suc-is≤≡true {m} {n} is-m≤n

        true◂ : ∀ {m n : ℕ} → m ≤ n → (is m ≤ n) ≡ true
        true◂ {zero} {zero} m≤n = ≡-refl
        true◂ {zero} {suc n} z≤n = ≡-refl
        true◂ {suc m} {suc n} (s≤s m≤n) = suc-is≤≡true {m} {n} (true◂ m≤n)