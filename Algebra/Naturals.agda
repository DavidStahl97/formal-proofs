module Algebra.Naturals where
  open import Algebra.Equality
  open import Algebra.Structures
  
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
  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  _∸_ : ℕ → ℕ → ℕ
  a ∸ zero = a
  zero ∸ suc b = zero
  suc a ∸ suc b = a ∸ b

  infixl 6 _+_ _∸_

  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc zero n p = refl
  +-assoc (suc m) n p = cong suc (+-assoc m n p)

  ℕ-Semigroup : Semigroup _+_
  Semigroup.assoc ℕ-Semigroup = +-assoc

  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-identity zero = refl
  +-identity (suc n) = cong suc (+-identity n)

  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)

  +-add1ᵣ : ∀ (m : ℕ) → m + 1 ≡ suc m
  +-add1ᵣ zero = refl
  +-add1ᵣ (suc m) = cong suc (+-add1ᵣ m)

  +-add1ₗ : ∀ (m : ℕ) → 1 + m ≡ suc m
  +-add1ₗ m = refl

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero = +-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎

 

  +-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc' zero n p = begin
    (zero + n) + p ≡⟨⟩
    n + p ≡⟨⟩
    zero + (n + p) ∎
  +-assoc' (suc m) n p = begin
    (suc m + n) + p ≡⟨⟩
    suc (m + n) + p ≡⟨⟩
    suc ((m + n) + p) ≡⟨ cong suc (+-assoc' m n p) ⟩
    suc (m + (n + p)) ∎

  +-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
  +-rearrange m n p q = begin
    (m + n) + (p + q) ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q)) ≡⟨ cong (λ a → m + a) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q) ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q ∎

  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap m n p = begin
    m + (n + p) ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m ≡⟨ +-assoc n p m ⟩
    n + (p + m) ≡⟨ cong (λ a → n + a) (+-comm p m) ⟩
    n + (m + p) ∎

  {-  
      ----------
      Multiplication 
      ----------
  -}
  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = (a * b) + b

  infixl 7 _*_

  *-zero : ∀ (m : ℕ) → m * zero ≡ zero
  *-zero zero = refl
  *-zero (suc m) = begin
    suc m * zero ≡⟨⟩
    m * zero + zero ≡⟨ +-identity (m * zero) ⟩
    m * zero ≡⟨ *-zero m ⟩
    zero ∎

  *-identity : ∀ (m : ℕ) → m * 1 ≡ m
  *-identity zero = refl
  *-identity (suc m) = begin
    suc m * 1 ≡⟨⟩
    m * 1 + 1 ≡⟨ cong (λ a → a + 1) (*-identity m) ⟩
    m + 1 ≡⟨ +-add1ᵣ m ⟩
    suc m ∎ 

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

  
 