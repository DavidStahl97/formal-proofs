module Algebra.Naturals.Exponentiation where
  open import Algebra.Naturals.Data
  open import Algebra.Naturals.Multiplication

  _^_ : ℕ → ℕ → ℕ
  a ^ zero = 1
  a ^ suc b = a * (a ^ b)
