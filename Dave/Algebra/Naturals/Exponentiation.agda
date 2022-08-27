module Dave.Algebra.Naturals.Exponentiation where
  open import Dave.Algebra.Naturals.Definition
  open import Dave.Algebra.Naturals.Multiplication
  open import Dave.Algebra.Naturals.Addition

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = (a ^ b) * a

  infixl 8 _^_ 

  ^-distribₗ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^-distribₗ m zero p = ≡-refl
  ^-distribₗ m (suc n) p = begin
    m ^ (suc n + p) ≡⟨⟩
    m ^ suc (n + p) ≡⟨⟩
    (m ^ (n + p)) * m ≡⟨ ≡-cong (λ a → a * m) (^-distribₗ m n p) ⟩
    (m ^ n) * (m ^ p) * m ≡⟨ IsCommutativeMonoid.swap021 ℕ-*-IsCommutativeMonoid (m ^ n) (m ^ p) m ⟩
    (m ^ n) * m * (m ^ p) ≡⟨⟩
    (m ^ n) * (m ^ 1) * (m ^ p) ≡⟨ ≡-cong (λ a → a * (m ^ p)) (≡-sym (^-distribₗ m n 1)) ⟩
    (m ^ (n + 1)) * (m ^ p) ≡⟨ ≡-cong (λ a → (m ^ a) * (m ^ p)) (+-add1ᵣ n) ⟩
    (m ^ suc n) * (m ^ p) ∎
  
  ^-distribᵣ : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  ^-distribᵣ m n zero = ≡-refl
  ^-distribᵣ m n (suc p) = begin
     (m * n) ^ suc p ≡⟨⟩ 
     ((m * n) ^ p) * (m * n) ≡⟨ ≡-cong (λ a → a * (m * n)) (^-distribᵣ m n p) ⟩
     (m ^ p) * (n ^ p) * (m * n) ≡⟨ ≡-sym (IsSemigroup.assoc ℕ-*-IsSemigroup ((m ^ p) * (n ^ p)) m n) ⟩
     (m ^ p) * (n ^ p) * m * n ≡⟨ ≡-cong (λ a → a * n) (IsCommutativeMonoid.swap021 ℕ-*-IsCommutativeMonoid (m ^ p) (n ^ p) m) ⟩
     (m ^ p) * m * (n ^ p) * n ≡⟨ IsSemigroup.assoc ℕ-*-IsSemigroup ((m ^ p) * m) (n ^ p) n ⟩
     (m ^ p) * m * ((n ^ p) * n) ≡⟨⟩
     (m ^ p) * (m ^ 1) * ((n ^ p) * (n ^ 1)) ≡⟨ ≡-cong (λ a → a * ((n ^ p) * (n ^ 1))) (≡-sym (^-distribₗ m p 1)) ⟩
     (m ^ (p + 1)) * ((n ^ p) * (n ^ 1)) ≡⟨ ≡-cong (λ a → (m ^ a) * ((n ^ p) * (n ^ 1))) (+-add1ᵣ p) ⟩
     (m ^ suc p) * ((n ^ p) * (n ^ 1)) ≡⟨ ≡-cong (λ a → (m ^ suc p) * a) (≡-sym (^-distribₗ n p 1)) ⟩
     (m ^ suc p) * (n ^ (p + 1)) ≡⟨ ≡-cong (λ a → (m ^ suc p) * (n ^ a)) (+-add1ᵣ p) ⟩
     (m ^ suc p) * (n ^ suc p) ∎

  ^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
  ^-*-assoc m n zero = ≡-sym (begin 
    m ^ (n * zero) ≡⟨ ≡-cong (λ a → m ^ a) (*-zero n) ⟩
    1 ∎)
  ^-*-assoc m n (suc p) = begin
    (m ^ n) ^ suc p ≡⟨⟩
    (m ^ n) ^ p * (m ^ n) ≡⟨ ≡-cong (λ a → a * (m ^ n)) (^-*-assoc m n p) ⟩
    m ^ (n * p) * (m ^ n) ≡⟨ ≡-sym (^-distribₗ m (n * p) n) ⟩ 
    m ^ (n * p + n) ≡⟨ ≡-cong (λ a → m ^ a ) (≡-sym (*-distrib1ᵣ-+ₗ n p)) ⟩ 
    m ^ (n * (p + 1)) ≡⟨ ≡-cong (λ a → m ^ (n * a)) (+-add1ᵣ p) ⟩ 
    m ^ (n * suc p) ∎