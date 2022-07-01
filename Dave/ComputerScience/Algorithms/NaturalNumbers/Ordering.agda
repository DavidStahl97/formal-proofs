module Dave.ComputerScience.Algorithms.NaturalNumbers.Ordering where
    open import Dave.ComputerScience.Algorithms.Decidable
    open import Dave.ComputerScience.DataStructures.Boolean
    open import Dave.Logic.Basics
    open import Dave.Algebra.Naturals.Definition
    open import Dave.Algebra.Naturals.Ordering

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
        true▸ : ∀ {m n : ℕ} → is m < n ≡ true → m < n        
        true▸ {zero} {suc n} is-true = z<s
        true▸ {suc m} {suc n} is-true = s<s (true▸ is-true)

        false▸ : ∀ {m n : ℕ} → is m < n ≡ false → ¬ m < n        
        false▸ {zero} {zero} refl ()
        false▸ {suc m} {zero} is-false ()
        false▸ {suc m} {suc n} is-false (s<s x) = false▸ is-false x

        true◂ : ∀ {m n : ℕ} → m < n → is m < n ≡ true
        true◂ {zero} {suc n} m<n = refl
        true◂ {suc m} {suc n} (s<s m<n) = true◂ m<n 