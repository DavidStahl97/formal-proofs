module Algebra.Naturals.Addition where
  open import Algebra.Naturals.Data
  
  _+_ : ℕ → ℕ → ℕ
  zero + b = b
  suc a + b = suc (a + b)

  _∸_ : ℕ → ℕ → ℕ
  a ∸ zero = a
  zero ∸ suc b = zero
  suc a ∸ suc b = a ∸ b

  infixl 6 _+_ _∸_
