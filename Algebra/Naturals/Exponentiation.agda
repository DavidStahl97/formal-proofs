module Algebra.Naturals.Exponentiation where
  open import Algebra.Naturals.Definition
  open import Algebra.Naturals.Multiplication
  open import Algebra.Naturals.Addition

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = (a ^ b) * a

  infixl 8 _^_ 


  ^-distribₗ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
  ^-distribₗ m zero p = refl
  ^-distribₗ m (suc n) p = begin
    m ^ (suc n + p) ≡⟨⟩
    m ^ suc (n + p) ≡⟨⟩
    (m ^ (n + p)) * m ≡⟨ cong (λ a → a * m) (^-distribₗ m n p) ⟩
    (m ^ n) * (m ^ p) * m ≡⟨ IsCommutativeMonoid.swap021 ℕ-*-IsCommutativeMonoid (m ^ n) (m ^ p) m ⟩
    (m ^ n) * m * (m ^ p) ≡⟨⟩
    (m ^ n) * (m ^ 1) * (m ^ p) ≡⟨ cong (λ a → a * (m ^ p)) (sym (^-distribₗ m n 1)) ⟩
    (m ^ (n + 1)) * (m ^ p) ≡⟨ cong (λ a → (m ^ a) * (m ^ p)) (+-add1ᵣ n) ⟩
    (m ^ suc n) * (m ^ p) ∎

    {-
  
  ^-distribᵣ : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
  ^-distribᵣ m n zero = refl
  ^-distribᵣ m n (suc p) = begin
     (m * n) ^ suc p ≡⟨⟩ 
     m * n * ((m * n) ^ p) ≡⟨ cong (λ a → m * n * a) (^-distribᵣ m n p) ⟩
     m * n * ((m ^ p) * (n ^ p)) ≡⟨ IsCommutativeMonoid.swap021 ℕ-*-IsCommutativeMonoid m n ((m ^ p) * (n ^ p)) ⟩
     m * ((m ^ p) * (n ^ p)) * n ≡⟨ cong (λ a → a * n) (sym (IsSemigroup.assoc ℕ-*-IsSemigroup m (m ^ p) (n ^ p))) ⟩
     m * (m ^ p) * (n ^ p) * n ≡⟨ IsSemigroup.assoc ℕ-*-IsSemigroup (m * (m ^ p)) (n ^ p) n ⟩
     m * (m ^ p) * ((n ^ p) * n) ≡⟨ cong (λ a → a * (m ^ p) * ((n ^ p) * n)) (sym (^-right-identity m)) ⟩
     (m ^ 1) * (m ^ p) * ((n ^ p) * n) ≡⟨ cong (λ a → a * ((n ^ p) * n)) (sym (^-distribₗ m 1 p)) ⟩
     (m ^ suc p) * ((n ^ p) * n) ≡⟨ cong (λ a → (m ^ suc p) * ((n ^ p) * a)) (sym (^-right-identity n)) ⟩
     (m ^ suc p) * ((n ^ p) * (n ^ 1)) ≡⟨ cong (λ a → (m ^ suc p) * a) (sym (^-distribₗ n p 1)) ⟩
     (m ^ suc p) * (n ^ (p + 1)) ≡⟨ cong (λ a → (m ^ suc p) * (n ^ a)) (+-add1ᵣ p) ⟩
     (m ^ suc p) * (n ^ suc p) ∎
  
  ^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
  ^-*-assoc m n zero = begin
    (m ^ n) ^ 0 ≡⟨ {!   !} ⟩
     m ^ (n * 0) ∎
  ^-*-assoc m n (suc p) = begin
    (m ^ n) ^ suc p ≡⟨ {!   !} ⟩
    m ^ (n * suc p) ∎ -}