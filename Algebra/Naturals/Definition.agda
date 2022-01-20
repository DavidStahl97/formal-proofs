module Algebra.Naturals.Definition where
  open import Algebra.Equality public
  open import Algebra.Structures.Monoid public
  
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  one = suc zero
  two = suc one
  three = suc two
  four = suc three
  five = suc four
  six = suc five
  seven = suc six
  eight = suc seven
  nine = suc eight

  {-# BUILTIN NATURAL  ℕ #-}

  {-  
      ----------
      Addition 
      ----------
  -}

  
  



  {-  
      ----------
      Multiplication 
      ----------
  -}
  {-
  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = (a * b) + b

  infixl 7 _*_

  *-zero : ∀ (m : ℕ) → m * zero ≡ zero
  *-zero zero = refl
  *-zero (suc m) = begin
    suc m * zero ≡⟨⟩
    m * zero + zero ≡⟨ +-right-identity (m * zero) ⟩
    m * zero ≡⟨ *-zero m ⟩
    zero ∎

  *-identity : ∀ (m : ℕ) → m * 1 ≡ m
  *-identity zero = refl
  *-identity (suc m) = begin
    suc m * 1 ≡⟨⟩
    m * 1 + 1 ≡⟨ cong (λ a → a + 1) (*-identity m) ⟩
    m + 1 ≡⟨ +-add1ᵣ m ⟩
    suc m ∎ -}

  {-
  *-distrib-+ᵣ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ᵣ zero n p = refl
  *-distrib-+ᵣ (suc m) n p = begin
    (suc m + n) * p ≡⟨⟩
    suc (m + n) * p ≡⟨⟩
    (m + n) * p + p ≡⟨ cong (λ a → a + p) (*-distrib-+ᵣ m n p) ⟩
    m * p + n * p + p ≡⟨ {!   !} ⟩

    suc m * p + n * p ∎

  *-distrib-+ₗ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
  *-distrib-+ₗ zero n p = refl
  *-distrib-+ₗ (suc m) n p = begin
    suc m * (n + p) ≡⟨⟩
    m * (n + p) + (n + p) ≡⟨ cong (λ a → a + (n + p)) (*-distrib-+ₗ m n p) ⟩
    m * n + m * p + (n + p) ≡⟨ {!   !} ⟩
    suc m * n + suc m * p ∎

-}
{-
  *-distrib-+ᵣ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ᵣ zero n p = refl
  *-distrib-+ᵣ (suc m) n p = begin
    (suc m + n) * p           ≡⟨⟩
    suc (m + n) * p           ≡⟨⟩
    (m + n) * p + p          ≡⟨ cong (λ a → a + p) (*-distrib-+ᵣ m n p) ⟩
    (m * p + n * p) + p      ≡⟨ +-comm (m * p + n * p) p ⟩
    p + (m * p + n * p)   ≡⟨ sym (+-assoc (1 * p) (m * p) (n * p)) ⟩
    (1 * p + m * p) + n * p   ≡⟨ cong (λ a → a + n * p) (+-comm (1 * p) (m * p)) ⟩
    (m * p + 1 * p) + n * p   ≡⟨ sym (cong (λ a → a + n * p) (*-distrib-+ᵣ m 1 p)) ⟩
    (m + 1) * p + n * p       ≡⟨ cong (λ a → a * p + n * p) (+-add1ᵣ m) ⟩ 
    (suc m) * p + n * p ∎
-}
  {-
  *-distrib-+ᵣ-suc : ∀ (m p : ℕ) → suc m * p ≡ p + m * p
  *-distrib-+ᵣ-suc m p = begin
    suc m * p ≡⟨⟩
    (1 + m) * p ≡⟨ *-distrib-+ᵣ 1 m p ⟩
    1 * p + m * p ≡⟨ {!   !} ⟩
    p + m * p ∎   

  *-distrib-+ₗ : ∀ (m n p : ℕ) → p * (m + n) ≡ p * m + p * n
  *-distrib-+ₗ m n zero = refl
  *-distrib-+ₗ m n (suc p) = begin
    suc p * (m + n) ≡⟨⟩
    (m + n) + p * (m + n) ≡⟨ cong (λ a → m + n + a) (*-distrib-+ₗ m n p) ⟩
    (m + n) + (p * m + p * n) ≡⟨ +-assoc m n (p * m + p * n) ⟩
    m + (n + (p * m + p * n)) ≡⟨ cong (λ a → m + a) (+-comm n (p * m + p * n)) ⟩
    m + (p * m + p * n + n) ≡⟨ cong (λ a → m + a) (+-assoc (p * m) (p * n) n) ⟩
    m + (p * m + (p * n + n)) ≡⟨ sym (+-assoc m (p * m) (p * n + n)) ⟩
    (m + p * m) + (p * n + n) ≡⟨ cong (λ a → (m + p * m) + a) (+-comm (p * n) n) ⟩
    (m + p * m) + (n + p * n) ≡⟨ {!   !} ⟩    
    suc p * m + suc p * n ∎

  *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
  *-assoc zero n p = refl
  *-assoc (suc m) n p = begin
    (suc m * n) * p           ≡⟨⟩
    (n + m * n) * p           ≡⟨ *-distrib-+ᵣ n (m * n) p ⟩
    n * p + m * n * p         ≡⟨ sym (cong (λ a → a + m * n * p) (*-identityₗ (n * p))) ⟩
    1 * (n * p) + m * n * p   ≡⟨ cong (λ a → 1 * (n * p) + a) (*-assoc m n p) ⟩
    1 * (n * p) + m * (n * p) ≡⟨ sym (*-distrib-+ᵣ 1 m (n * p)) ⟩
    (1 + m) * (n * p)         ≡⟨ cong (λ a → a * (n * p)) (+-add1ₗ m) ⟩
    suc m * (n * p) ∎

  *-comm : ∀ (m n) → m * n ≡ n * m
  *-comm zero n = begin
    zero * n ≡⟨⟩
    zero ≡⟨ sym (*-zero n) ⟩
    n * zero ∎
  *-comm (suc m) n = begin
    suc m * n ≡⟨⟩
    n + m * n ≡⟨ {!   !} ⟩    
    n * suc m ∎

  {-  
      ----------
      Exponentiation 
      ----------
  -}
  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = a * (a ^ b)

  infixl 8 _^_ -}

  
 