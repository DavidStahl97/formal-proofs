module Algebra.Naturals.Multiplication where
  open import Algebra.Naturals.Data
  open import Algebra.Naturals.Addition
  
  _*_ : ℕ → ℕ → ℕ
  zero * b = zero
  suc a * b = b + (a * b)
