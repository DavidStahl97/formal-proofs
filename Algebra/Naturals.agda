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

  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm m zero = +-identity m
  +-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

  +-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +-identity m
  +-comm' m (suc n) = begin
      (m + suc n) ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
      suc (n + m) ∎

  {-  
      ----------
      Multiplication 
      ----------
  -}
  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = b + (a * b)

  infixl 7 _*_

  {-  
      ----------
      Exponentiation 
      ----------
  -}
  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = a * (a ^ b)

  infixl 8 _^_

  
