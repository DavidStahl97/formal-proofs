module Dave.Algebra.Naturals.Monus where
    open import Dave.Algebra.Naturals.Definition
    open import Dave.Algebra.Naturals.Addition

    _∸_ : ℕ → ℕ → ℕ
    m ∸ zero = m
    zero ∸ suc n = zero
    suc m ∸ suc n = m ∸ n

    infixl 6 _∸_

    ∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
    ∸-zero zero = ≡-refl
    ∸-zero (suc n) = ≡-refl

    ∸-assoc-+ : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
    ∸-assoc-+ m zero p = ≡-refl
    ∸-assoc-+ zero (suc n) p = ∸-zero p
    ∸-assoc-+ (suc m) (suc n) p = begin
        suc m ∸ suc n ∸ p ≡⟨⟩
        m ∸ n ∸ p ≡⟨ ∸-assoc-+ m n p ⟩
        m ∸ (n + p) ≡⟨⟩
        suc m ∸ suc (n + p) ≡⟨⟩
        suc m ∸ (suc n + p) ∎