module Dave.Core.Naturals where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  {-# BUILTIN NATURAL  ℕ #-} 

  infixl 6 _+_
  infixl 7 _*_
  infixl 6 _∸_
  
  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = (a * b) + b

  _∸_ : ℕ → ℕ → ℕ
  m ∸ zero = m
  zero ∸ suc n = zero
  suc m ∸ suc n = m ∸ n