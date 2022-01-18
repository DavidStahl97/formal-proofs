module Algebra.Naturals where
  open import Algebra.Equality
  
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

  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
  +-assoc zero n p = refl
  +-assoc (suc m) n p = cong suc (+-assoc m n p)

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
  suc a * b = b + (a * b)

  infixl 7 _*_

  *-zero : ∀ (m : ℕ) → m * zero ≡ zero
  *-zero zero = refl
  *-zero (suc m) = begin
    suc m * zero ≡⟨⟩
    zero + (m * zero) ≡⟨⟩
    m * zero ≡⟨ *-zero m ⟩
    zero ∎

  *-identityᵣ : ∀ (m : ℕ) → m * 1 ≡ m
  *-identityᵣ zero = refl
  *-identityᵣ (suc m) = cong suc (*-identityᵣ m)

  *-identityₗ : ∀ (m : ℕ) → 1 * m ≡ m
  *-identityₗ zero = refl
  *-identityₗ (suc m) = cong suc (*-identityₗ m)

  *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ zero n p = refl
  *-distrib-+ (suc m) n p = begin
    (suc m + n) * p           ≡⟨⟩
    suc (m + n) * p           ≡⟨⟩
    p + (m + n) * p           ≡⟨ cong (λ a → p + a) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)       ≡⟨ sym (cong (λ a → a + (m * p + n * p)) (*-identityₗ p)) ⟩
    1 * p + (m * p + n * p)   ≡⟨ sym (+-assoc (1 * p) (m * p) (n * p)) ⟩
    (1 * p + m * p) + n * p   ≡⟨ cong (λ a → a + n * p) (+-comm (1 * p) (m * p)) ⟩
    (m * p + 1 * p) + n * p   ≡⟨ sym (cong (λ a → a + n * p) (*-distrib-+ m 1 p)) ⟩
    (m + 1) * p + n * p       ≡⟨ cong (λ a → a * p + n * p) (+-add1ᵣ m) ⟩ 
    (suc m) * p + n * p ∎

  *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
  *-assoc zero n p = refl
  *-assoc (suc m) n p = begin
    (suc m * n) * p           ≡⟨⟩
    (n + m * n) * p           ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + m * n * p         ≡⟨ sym (cong (λ a → a + m * n * p) (*-identityₗ (n * p))) ⟩
    1 * (n * p) + m * n * p   ≡⟨ cong (λ a → 1 * (n * p) + a) (*-assoc m n p) ⟩
    1 * (n * p) + m * (n * p) ≡⟨ sym (*-distrib-+ 1 m (n * p)) ⟩
    (1 + m) * (n * p)         ≡⟨ cong (λ a → a * (n * p)) (+-add1ₗ m) ⟩
    suc m * (n * p) ∎

  {-  
      ----------
      Exponentiation 
      ----------
  -}
  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = a * (a ^ b)

  infixl 8 _^_

  
 