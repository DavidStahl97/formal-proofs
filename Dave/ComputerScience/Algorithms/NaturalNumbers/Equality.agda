module Dave.ComputerScience.Algorithms.NaturalNumbers.Equality where
    open import Dave.ComputerScience.Datastructures.Module
    open import Dave.Logic.Module
    open import Dave.Algebra.Naturals.Module

    is_≡_ : ℕ → ℕ → Bool
    is zero ≡ zero = true
    is zero ≡ suc n = false
    is suc m ≡ zero = false
    is suc m ≡ suc n = is m ≡ n

    is▸≡ : is_≡_ ▸₂ _≡_
    is▸≡ = record 
        {
            true▸ = true▸;
            false▸ = false▸;
            true◂ = true◂
        }
        where
        true▸ : ∀ {m n : ℕ} → (is m ≡ n) ≡ true → m ≡ n        
        true▸ {zero} {zero} is-m≡n = ≡-refl
        true▸ {suc m} {suc n} is-m≡n = ≡-cong suc (true▸ is-m≡n)

        false▸ : ∀ {m n : ℕ} → (is m ≡ n) ≡ false → ¬ m ≡ n
        false▸ {suc m} {zero} is-m≡n ()
        false▸ {zero} {suc n} is-m≡n ()
        false▸ {suc m} {suc .m} is-m≡n ≡-refl = false▸ {m} {m} is-m≡n ≡-refl

        true◂ : ∀ {m n : ℕ} → m ≡ n → (is m ≡ n) ≡ true
        true◂ {zero} {zero} ≡-refl = ≡-refl
        true◂ {suc m} {suc n} m≡n = true◂ {m} {n} (suc≡→≡ m≡n)

